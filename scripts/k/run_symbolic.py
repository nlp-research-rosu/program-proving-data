#!/usr/bin/env python3
"""run_symbolic — generate the B-family (symbolic-trace) samples.

Pipeline per program:
  py2mpy_traced (--linemarks)                 -> .mpy with magic-literal args
  krun --depth 0 --output kore (llvm traced)  -> ground initial configuration
  textual substitution                        -> magic Int literals become sorted
                                                 KORE variables (inj{SortInt,SortExpr}(VarA))
  kore-rpc (pyk kore_server on MPY-TRACED-SYM, no MPY-CONCRETE)
     client.execute until BranchingResult     -> fork per branch, building the tree
  per leaf:
     kore-print --output json                 -> KAST; trace cell = line-tagged
                                                 SYMBOLIC locals; scopes = result term
     client.get_model                         -> z3 witness for the path condition
     witness replay (CPython + traced llvm)   -> line path must match the leaf's

Watchdogs: every subprocess call is wrapped in a timeout; the RPC client uses
per-request timeouts. Anything slower than minutes on these programs is stuck
(see PLAN.md runtime discipline)."""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts"))

import kastjson  # noqa: E402
import tracelib  # noqa: E402
from py2mpy_traced import to_mpy  # noqa: E402

from pyk.kore.parser import KoreParser  # noqa: E402
from pyk.kore.rpc import BranchingResult, KoreClient, SatResult, kore_server  # noqa: E402

SYM_DEF = ROOT / "build/k/traced-sym"
TRACED_DEF = ROOT / "build/k/traced"
MODULE = "MPY-TRACED-SYM"

SAMPLES = [
    {
        "id": "b1_abs_val",
        "program": "programs/abs_val.py",
        "entry": "abs_val",
        "magics": {31337: ("VarX", "x")},
    },
    {
        "id": "b2_classify_triangle",
        "program": "programs/classify_triangle.py",
        "entry": "classify_triangle",
        "magics": {31337: ("VarA", "a"), 31338: ("VarB", "b"), 31339: ("VarC", "c")},
    },
]

MAX_NODES = 64  # loop-free programs: anything larger means runaway exploration


# --------------------------------------------------------------------------
# initial symbolic configuration
# --------------------------------------------------------------------------
def initial_kore(py_path: Path, magics: dict[int, tuple[str, str]]) -> str:
    mpy = ROOT / "build/k/mpy" / (py_path.stem + ".mpy")
    mpy.write_text(to_mpy(str(py_path)))
    p = subprocess.run(
        ["timeout", "120", "krun", "--definition", str(TRACED_DEF), str(mpy),
         "--depth", "0", "--output", "kore"],
        capture_output=True, text=True, check=True)
    kore = p.stdout
    for magic, (var, _) in magics.items():
        pat = re.compile(r"Lbl[A-Za-z0-9'\-]*\{\}\(\\dv\{SortInt\{\}\}\(\"" + str(magic) + r"\"\)\)")
        n = len(pat.findall(kore))
        assert n == 1, f"magic {magic} occurs {n} times in initial config"
        kore = pat.sub(f"inj{{SortInt{{}}, SortExpr{{}}}}({var}:SortInt{{}})", kore)
    return kore


# --------------------------------------------------------------------------
# KAST rendering of symbolic terms / path conditions
# --------------------------------------------------------------------------
ARITH = {"_+Int_": "+", "_-Int_": "-", "_*Int_": "*", "_/Int_": "/", "_modInt_": "%"}
CMP = {"_<Int_": "<", "_<=Int_": "<=", "_>Int_": ">", "_>=Int_": ">=",
       "_==Int_": "==", "_=/=Int_": "!=", "_==K_": "==", "_=/=K_": "!="}


class SymRenderer(kastjson.Renderer):
    """kastjson.Renderer + KVariable and arithmetic applications."""

    def __init__(self, heap_node, varmap: dict[str, str]):
        super().__init__(heap_node)
        self.varmap = varmap

    def val(self, n: dict, name_hint: str | None = None):
        if n["node"] == "KVariable":
            return self.varmap.get(n["name"], n["name"])
        if n["node"] == "KApply":
            b = n["label"]["name"]
            if b in ARITH or b in CMP:
                op = ARITH.get(b) or CMP[b]
                l, r = (self.val(a) for a in n["args"])
                return f"{self._paren(l)} {op} {self._paren(r)}"
        return super().val(n, name_hint)

    @staticmethod
    def _paren(v) -> str:
        s = v if isinstance(v, str) else repr(v)
        return f"({s})" if isinstance(v, str) and " " in s and not s.startswith("(") else s


def pc_conjuncts(kast: dict, r: SymRenderer) -> list[str]:
    """Collect the path condition from a KAST pattern's ML constraints."""
    out: list[str] = []

    def pred(n: dict, neg: bool) -> None:
        b = n["label"]["name"] if n["node"] == "KApply" else ""
        if b == "#And":
            for a in n["args"]:
                pred(a, neg)
        elif b == "#Not":
            pred(n["args"][0], not neg)
        elif b == "#Equals":
            lhs, rhs = n["args"]
            if lhs.get("node") == "KToken" and lhs.get("token") in ("true", "false"):
                s = r.val(rhs)
                if lhs["token"] == "false":
                    neg = not neg
            elif rhs.get("node") == "KToken" and rhs.get("token") in ("true", "false"):
                s = r.val(lhs)
                if rhs["token"] == "false":
                    neg = not neg
            else:
                s = f"{r.val(lhs)} == {r.val(rhs)}"
            out.append(f"not ({s})" if neg else str(s))
        elif b == "#Top":
            pass
        elif b.startswith("#"):
            out.append(("not " if neg else "") + json.dumps(b))

    def walk(n: dict) -> None:
        if n["node"] != "KApply":
            return
        b = n["label"]["name"]
        if b == "#And":
            for a in n["args"]:
                walk(a)
        elif b in ("#Equals", "#Not", "#Top", "#Ceil"):
            pred(n, False) if b != "#Ceil" else None
        # the configuration application itself is skipped

    walk(kast)
    return out


def kore_to_kast(kore_text: str) -> dict:
    p = subprocess.run(
        ["timeout", "120", "kore-print", "/dev/stdin", "--definition", str(SYM_DEF),
         "--output", "json"],
        input=kore_text, capture_output=True, text=True, check=True)
    return json.loads(p.stdout)["term"]


# --------------------------------------------------------------------------
# tree exploration
# --------------------------------------------------------------------------
def explore(client: KoreClient, init: "Pattern") -> tuple[list[dict], list[dict], list[dict]]:
    """BFS from init; returns (nodes, edges, leaf_records) with raw kore refs."""
    nodes: list[dict] = []
    edges: list[dict] = []
    leaves: list[dict] = []
    work = [(0, init, None)]  # (node_id, pattern, parent)
    nodes.append({"node": 0, "kore": init})
    next_id = 1

    while work:
        nid, pat, _parent = work.pop(0)
        assert next_id < MAX_NODES, "exploration exceeded MAX_NODES — runaway?"
        res = client.execute(pat)
        if isinstance(res, BranchingResult):
            for st in res.next_states:
                cid = next_id
                next_id += 1
                nodes.append({"node": cid, "kore": st.kore})
                cond = st.rule_predicate
                edges.append({"from": nid, "to": cid,
                              "cond_kore": cond.text if cond is not None else None})
                work.append((cid, st.kore, nid))
        else:
            leaves.append({"node": nid, "kore": res.state.kore,
                           "reason": type(res).__name__})
    return nodes, edges, leaves


# --------------------------------------------------------------------------
# witness handling
# --------------------------------------------------------------------------
def get_witness(client: KoreClient, pat, magics) -> dict[str, int] | None:
    res = client.get_model(pat)
    if not isinstance(res, SatResult):
        return None
    witness = {py: 0 for _, py in magics.values()}  # unconstrained vars: any value
    if res.model is None:
        return witness
    text = res.model.text
    for m in re.finditer(r"(Var\w+)\s*:\s*SortInt\{\}\s*,\s*\\dv\{SortInt\{\}\}\(\"(-?\d+)\"\)", text):
        var, val = m.group(1), int(m.group(2))
        for _, (kvar, py) in magics.items():
            if kvar == var:
                witness[py] = val
    # kore \equals form fallback
    for _, (kvar, py) in magics.items():
        m = re.search(re.escape(kvar) + r":SortInt\{\}.*?\\dv\{SortInt\{\}\}\(\"(-?\d+)\"\)", text, re.S)
        if m:
            witness[py] = int(m.group(1))
    return witness


def replay(py_path: Path, magics, witness: dict[str, int], leaf_lines: list[int],
           leaf_value) -> dict:
    """Run the witness concretely through CPython AND the traced llvm build;
    check the line path and return value against the leaf's symbolic ones."""
    src = py_path.read_text()
    for magic, (_, py) in magics.items():
        src = src.replace(str(magic), str(witness[py]))
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td) / py_path.name
        tmp.write_text(src)
        # CPython
        g: dict = {}
        exec(compile(src, str(tmp), "exec"), g)
        py_result = g["result"]
        py_lines = [e["line"] for e in tracelib.cpython_events(str(tmp)) if e["event"] == "line"]
        # K traced llvm
        mpy = Path(td) / (py_path.stem + ".mpy")
        mpy.write_text(to_mpy(str(tmp)))
        p = subprocess.run(["timeout", "120", "krun", "--definition", str(TRACED_DEF),
                            str(mpy), "--output", "json"], capture_output=True, text=True)
        term = json.loads(p.stdout)["term"]
        k_lines = [e[1] for e in kastjson.raw_events(term) if e[0] == "line"]
        k_result = kastjson.module_result(term)

    expected = leaf_value
    if isinstance(leaf_value, str) and not leaf_value.startswith(("'", '"')):
        try:  # symbolic term like "-x" or "x": evaluate under the witness
            expected = eval(leaf_value, {}, dict(witness))
        except Exception:
            pass
    ok = (k_lines == leaf_lines == py_lines) and (py_result == k_result == expected)
    return {"ok": ok, "cpython_result": py_result, "k_result": k_result,
            "expected_from_symbolic": expected,
            "lines_match": k_lines == leaf_lines == py_lines}


# --------------------------------------------------------------------------
# B2-specific: syntactically possible but SMT-infeasible paths, proved by z3
# --------------------------------------------------------------------------
def z3_unsat(constraints: list[str], names: list[str]) -> bool:
    smt = "".join(f"(declare-const {n} Int)" for n in names)
    smt += "".join(f"(assert {c})" for c in constraints) + "(check-sat)"
    p = subprocess.run(["timeout", "60", "z3", "-in"], input=smt,
                       capture_output=True, text=True)
    return p.stdout.strip() == "unsat"


def b2_pruned() -> list[dict]:
    combos = [
        (["(= a b)", "(= b c)", "(not (= a c))"], "a == b and b == c and not (a == c)"),
        (["(= a b)", "(not (= b c))", "(= a c)"], "a == b and not (b == c) and a == c"),
        (["(not (= a b))", "(= b c)", "(= a c)"], "not (a == b) and b == c and a == c"),
    ]
    out = []
    for smt_c, pretty in combos:
        assert z3_unsat(smt_c, ["a", "b", "c"]), f"expected unsat: {pretty}"
        out.append({"path_condition": pretty, "verdict": "infeasible",
                    "proof": "z3 unsat on the path constraints (equality is transitive)"})
    return out


# --------------------------------------------------------------------------
# per-sample driver
# --------------------------------------------------------------------------
def leaf_record(leaf, client, magics, varmap, ft, py_path):
    kast = kore_to_kast(leaf["kore"].text)
    cs = kastjson.cells(kast)
    r = SymRenderer(cs.get("<heap>"), varmap)
    # line-tagged symbolic locals from the trace cell
    trace_nodes = kastjson.klist_items(cs["<trace>"])
    line_events = []
    for item in trace_nodes:
        if kastjson.lbl(item) == "lineEvt":
            line_n, scope_n, heap_n = item["args"]
            rr = SymRenderer(heap_n, varmap)
            line_events.append({"line": kastjson.token(line_n),
                                "locals": rr.scope_locals(scope_n)})
    pc = pc_conjuncts(kast, r)
    # result value from the module scope
    result = None
    for k, v in kastjson.kmap_entries(cs["<scopes>"]):
        if kastjson.token(k) == 0:
            m = r.scope_locals(v["args"][0])
            result = m.get("result")
    witness = get_witness(client, leaf["kore"], magics)
    rep = None
    if witness is not None:
        rep = replay(py_path, magics, witness, [e["line"] for e in line_events], result)
    return {
        "node": leaf["node"],
        "event": "return",
        "value": result,
        "path_condition": pc,
        "trace": line_events,
        "witness": witness,
        "witness_validated": bool(rep and rep["ok"]),
        "witness_replay": rep,
        "terminal_reason": leaf["reason"],
    }


def build_sample(spec, client) -> dict:
    py_path = ROOT / spec["program"]
    ft = tracelib.FuncTable(str(py_path))
    magics = spec["magics"]
    # kore-print's KAST strips the `Var` prefix: cover both spellings
    varmap = {}
    for _, (kvar, py) in magics.items():
        varmap[kvar] = py
        varmap[kvar.removeprefix("Var")] = py

    init_text = initial_kore(py_path, magics)
    init = KoreParser(init_text).pattern()
    nodes, edges, leaves = explore(client, init)

    leaf_records = [leaf_record(lf, client, magics, varmap, ft, py_path) for lf in leaves]

    # render edge conditions
    for e in edges:
        if e["cond_kore"]:
            kast = kore_to_kast(e["cond_kore"])
            e["condition"] = "; ".join(pc_conjuncts(kast, SymRenderer(None, varmap))) or e["cond_kore"]
        else:
            e["condition"] = None
        del e["cond_kore"]

    rec = {
        "id": f"symbolic/{py_path.stem}/" + ",".join(f"{py}=?{py}:int" for _, (_, py) in magics.items()),
        "kind": "symbolic_trace",
        "source": {"file": spec["program"],
                   "code": ft.source.replace("31337", "a").replace("31338", "b").replace("31339", "c")
                   if len(magics) > 1 else ft.source.replace("31337", "x"),
                   "entry": spec["entry"],
                   "args": {py: f"?{py}:int" for _, (_, py) in magics.items()}},
        "tree": {"n_nodes": len(nodes), "edges": edges},
        "leaves": leaf_records,
        "pruned_infeasible": b2_pruned() if spec["id"] == "b2_classify_triangle" else [],
        "provenance": {
            "generator": "pyk kore-rpc (kore-exec) on MPY-TRACED-SYM (haskell backend)",
            "smt": "z3 (server-side get-model; pruned paths re-proved with standalone z3)",
            "witness_validation": "each leaf's z3 witness replayed through CPython and the "
                                  "traced LLVM build; line paths and results must all agree",
        },
    }
    return rec


def to_markdown(rec: dict) -> str:
    lines = [f"# {rec['id']}", "", "```python", rec["source"]["code"].rstrip(), "```", "",
             f"Symbolic args: `{rec['source']['args']}` — {len(rec['leaves'])} feasible paths, "
             f"{len(rec['pruned_infeasible'])} infeasible (SMT-pruned)", ""]
    for lf in rec["leaves"]:
        w = lf["witness"]
        lines += [f"## Path -> return `{lf['value']}`  (node {lf['node']})", "",
                  f"- path condition: `{' and '.join(lf['path_condition']) or 'True'}`",
                  f"- witness: `{w}` — replay validated: **{lf['witness_validated']}**",
                  "", "| line | source | symbolic locals |", "|---|---|---|"]
        ft_lines = rec["source"]["code"].splitlines()
        for e in lf["trace"]:
            src = ft_lines[e["line"] - 1].strip() if e["line"] <= len(ft_lines) else ""
            lines.append(f"| {e['line']} | `{src}` | {json.dumps(e['locals'])} |")
        lines.append("")
    if rec["pruned_infeasible"]:
        lines += ["## Infeasible paths (pruned by SMT)", ""]
        for p in rec["pruned_infeasible"]:
            lines.append(f"- `{p['path_condition']}` — {p['proof']}")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    outdir = ROOT / "data/k/symbolic"
    outdir.mkdir(parents=True, exist_ok=True)
    print("starting kore-rpc server on MPY-TRACED-SYM ...")
    with kore_server(SYM_DEF, MODULE, smt_timeout=10000, smt_retry_limit=2) as server:
        with KoreClient("localhost", server.port, timeout=120000) as client:
            for spec in SAMPLES:
                rec = build_sample(spec, client)
                (outdir / f"{spec['id']}.jsonl").write_text(json.dumps(rec, sort_keys=True) + "\n")
                (outdir / f"{spec['id']}.md").write_text(to_markdown(rec))
                nv = sum(1 for lf in rec["leaves"] if lf["witness_validated"])
                print(f"[ok] {spec['id']}: {len(rec['leaves'])} paths "
                      f"({nv} witness-validated), {len(rec['pruned_infeasible'])} pruned")
    return 0


if __name__ == "__main__":
    sys.exit(main())
