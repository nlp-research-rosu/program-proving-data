#!/usr/bin/env python3
"""build_tasks — generate the Harbor task tree (tasks/) and registry.json from
the corpus.

Every task is derived from one canonical artifact of corpus/ (the K claim
module of a verification record, or the Lean derivation of its mirror) plus the
shared templates in scripts/harbor/templates/. The output is committed; CI
regenerates it into a scratch directory and fails on any difference, so tasks/
can never drift from the corpus.

Four task families (see README.md):

  k-spec-<program>     write + prove the full final-state claim in K (33 tasks)
  k-inv-<program>      write the circularity claim(s) for a frozen entry claim (21)
  lean-spec-<program>  derive the frozen functional spec in RL over proved paths (12)
  lean-inv-<program>   invent the invariant + Circularity derivation over proved legs (21)

Usage: python scripts/harbor/build_tasks.py [--out DIR]   (default: <repo>/tasks)
"""
from __future__ import annotations

import argparse
import ast
import json
import re
import shutil
import subprocess
import sys
import tempfile
import uuid
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CORPUS = ROOT / "corpus"
TEMPL = HERE / "templates"
sys.path.insert(0, str(HERE))
import kclaims as K  # noqa: E402

ORG = "nlp-research-rosu"
REPO_URL = "https://github.com/nlp-research-rosu/sample-data-public"
K_VERSION = "7.1.337"
K_IMAGE = f"runtimeverificationinc/kframework-k:ubuntu-jammy-{K_VERSION}"
VMOD = "MPY-VERIFICATION"
CANARY_NS = uuid.UUID("5b1d7a2e-9c6f-4d1b-8a3e-2f0c7e9d4b61")
LEAN_BASE = ["Prelude", "Sorts", "Inj", "Func", "Rewrite", "Relations", "RL"]
LEAN_TOOLCHAIN = (CORPUS / "lean" / "lean-toolchain").read_text().strip()
N_SAMPLES = 24
SEED = 20261030
KPROVE_TIMEOUT = 600
DATASET_VERSION = "1.0.0"

# programs outside the KleverBench port: structural tier by analogy with PROVENANCE.md
EXTRA_TIERS = {"range_loop": 2, "abs_val": 2, "sum_to_n": 2}


# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def render(template: str, mapping: dict[str, str]) -> str:
    out = template
    for k, v in mapping.items():
        out = out.replace("{{" + k + "}}", str(v))
    left = re.findall(r"\{\{[a-z_]+\}\}", out)
    if left:
        raise SystemExit(f"unrendered placeholders {left}")
    return out


def tmpl(*parts: str) -> str:
    return (TEMPL.joinpath(*parts)).read_text(encoding="utf-8")


def canary(task_name: str) -> str:
    return str(uuid.uuid5(CANARY_NS, task_name))


def toml_str(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def toml_list(xs: list[str]) -> str:
    return "[" + ", ".join(toml_str(x) for x in xs) + "]"


class Out:
    """Collects files to write (LF, utf-8) and writes them atomically into a
    fresh directory."""

    def __init__(self) -> None:
        self.files: dict[str, bytes] = {}
        self.exec: set[str] = set()

    def put(self, rel: str, text: str | bytes, *, executable: bool = False) -> None:
        if rel in self.files:
            raise SystemExit(f"duplicate output {rel}")
        data = text if isinstance(text, bytes) else text.replace("\r\n", "\n").encode("utf-8")
        self.files[rel] = data
        if executable:
            self.exec.add(rel)

    def copy(self, rel: str, src: Path) -> None:
        self.put(rel, src.read_bytes().replace(b"\r\n", b"\n"))

    def write_all(self, root: Path) -> None:
        for rel, data in self.files.items():
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
            if rel in self.exec:
                try:
                    p.chmod(0o755)
                except OSError:
                    pass


def loop_info(code: str) -> tuple[int, int, str]:
    """(number of loops, max nesting depth, human phrase)."""
    tree = ast.parse(code)
    count = 0
    depth = 0
    kinds: list[str] = []

    def walk(node, d):
        nonlocal count, depth
        for ch in ast.iter_child_nodes(node):
            if isinstance(ch, (ast.While, ast.For)):
                count += 1
                depth = max(depth, d + 1)
                kinds.append("for" if isinstance(ch, ast.For) else "while")
                walk(ch, d + 1)
            else:
                walk(ch, d)
    walk(tree, 0)
    if count == 0:
        phrase = "no loops"
    elif count == 1:
        phrase = f"a `{kinds[0]}` loop" + (" over `range`" if kinds[0] == "for" else "")
    elif depth >= 2 and count == 2:
        phrase = "two nested `while` loops"
    else:
        phrase = f"{count} loops (nesting depth {depth})"
    return count, depth, phrase


def tiers() -> dict[str, int]:
    out = dict(EXTRA_TIERS)
    for line in (ROOT / "programs" / "PROVENANCE.md").read_text(encoding="utf-8").splitlines():
        m = re.match(r"\|\s*(kb_\w+)\.py\s*\|\s*problems/imp/[\w-]+\s*\|\s*(\d)\s*\|", line)
        if m:
            out[m.group(1)] = int(m.group(2))
    return out


def difficulty(family: str, toolchain: str, tier: int) -> str:
    if toolchain == "lean" and family == "loop-invariant":
        return "hard"
    if tier >= 4:
        return "hard"
    if tier == 1:
        return "easy"
    return "medium"


def camel(stem: str) -> str:
    return "".join(p.capitalize() for p in stem.split("_"))


# ---------------------------------------------------------------------------
# the corpus: one Program per verification record
# ---------------------------------------------------------------------------

@dataclass
class Program:
    record_stem: str            # c14_kb_sum
    num: int                    # 14
    key: str                    # kb_sum
    slug: str                   # kb-sum
    record: dict
    spec_dir: Path
    spec_text: str
    tier: int
    program_file: Path | None   # programs/kb_sum.py (None for the vendored range_loop)
    loops: int = 0
    depth: int = 0
    loop_phrase: str = ""
    # filled from the parsed reference spec
    spec_module: str = ""
    entry: K.Claim | None = None
    others: list = field(default_factory=list)
    inputs: K.Inputs | None = None

    @property
    def code(self) -> str:
        return self.record["source"]["code"]

    @property
    def fn_names(self) -> list[str]:
        e = self.record["source"].get("entry")
        return [e] if e else []

    @property
    def requires_english(self) -> str:
        return self.record["spec"]["requires"]

    @property
    def upstream(self) -> str:
        up = self.record.get("provenance", {}).get("upstream")
        if up:
            return f"KleverBench {up['problem']} @ {up['sha'][:7]}"
        if self.key == "range_loop":
            return "klever reference proof tests/verification/range-loop"
        return "this repository"


def load_programs() -> dict[str, Program]:
    tier = tiers()
    progs: dict[str, Program] = {}
    for p in sorted((CORPUS / "k" / "verification").glob("*.jsonl")):
        rec = json.loads(p.read_text(encoding="utf-8"))
        if rec["result"] != "proved":
            continue
        m = re.match(r"c(\d+)_(.*)", p.stem)
        num, key = int(m.group(1)), m.group(2)
        slug = key.replace("_", "-")
        spec_dir = (ROOT / "vendor/klever/tests/verification/range-loop" if key == "range_loop"
                    else CORPUS / "specs" / slug)
        spec_text = (spec_dir / "spec.k").read_text(encoding="utf-8")
        pf = ROOT / "programs" / f"{key}.py"
        prog = Program(record_stem=p.stem, num=num, key=key, slug=slug, record=rec,
                       spec_dir=spec_dir, spec_text=spec_text, tier=tier[key],
                       program_file=pf if pf.exists() else None)
        prog.loops, prog.depth, prog.loop_phrase = loop_info(prog.code)
        vmod = re.search(r"imports\s+([A-Z][A-Z0-9-]*)", spec_text).group(1)
        mod = K.parse_module(spec_text, verification_module=vmod)
        prog.spec_module = mod.name
        prog.entry, prog.others = K.entry_claim(mod)
        args = list(rec["source"]["args"].keys()) if rec["source"].get("entry") else []
        prog.inputs = K.discover_inputs(prog.entry.cells["k"].split("=>")[0], args)
        probs = K.check_closed_forms(prog.entry, code=prog.code, inputs=prog.inputs,
                                     requires=prog.entry.requires, fn_names=prog.fn_names,
                                     n_samples=N_SAMPLES, seed=SEED)
        if probs:
            raise SystemExit(f"reference claim of {p.stem} fails the semantic check: {probs}")
        progs[key] = prog
    return progs


# ---------------------------------------------------------------------------
# K tasks
# ---------------------------------------------------------------------------

def program_display(prog: Program) -> str:
    """program.py as handed to the agent."""
    if prog.program_file is not None:
        body = prog.program_file.read_text(encoding="utf-8")
        head = ("# The module-level assignments below are the inputs: their literal values stand\n"
                "# for arbitrary integers (symbolic in the claim).\n")
    else:
        body = prog.code
        args = ", ".join(prog.record["source"]["args"])
        head = (f"# `{args}` is the program's input: a free name here, a symbolic integer in the\n"
                "# claim. The program is not runnable as a script.\n")
    return head + body


def inputs_sentence_k(prog: Program) -> str:
    inp = prog.inputs
    pre = prog.entry.requires
    pre_txt = (f"The precondition is `requires {pre}` ({prog.requires_english})."
               if pre else f"There is no precondition ({prog.requires_english}).")
    if inp.module:
        lits = {}
        if prog.program_file is not None:
            for ln in prog.program_file.read_text(encoding="utf-8").splitlines():
                m = re.match(r"(\w+)\s*=\s*(-?\d+)\s*$", ln)
                if m:
                    lits.setdefault(m.group(1), m.group(2))
        names = ", ".join(f"`{py}`" for py, _ in inp.module)
        litxt = ", ".join(f"`{lits.get(py, '?')}`" for py, _ in inp.module)
        kv = ", ".join(f"`{k}:Int`" for _, k in inp.module)
        return (f"The inputs are the module variables {names}, written as the literals {litxt} in "
                f"`program.py`; the claim replaces them by the symbolic integers {kv}. {pre_txt}")
    names = ", ".join(f"`{py}`" for py, _ in inp.call)
    kv = ", ".join(f"`{k}:Int`" for _, k in inp.call)
    fn = prog.fn_names[0]
    return (f"The input is the argument {names} of `{fn}`, the symbolic integer {kv} in the "
            f"claim's call. {pre_txt}")


def claim_block(text: str) -> str:
    """Re-indent a parsed (comment-stripped) claim body under `  claim`."""
    return "  claim\n    " + text.strip() + "\n"


def skeleton_spec(prog: Program) -> str:
    text = prog.entry.text.strip()
    m = re.search(r"(<scopes>)(.*?)(</scopes>)", text, re.S)
    lhs, _rhs = K.split_scopes(m.group(2))
    new_scopes = (m.group(1) + lhs.rstrip() + "\n    =>\n      -1 |-> builtinsScope\n"
                  "      0 |-> scope(/* FINAL-SCOPE: .Map [ \"x\" <- TERM ] [ \"y\" <- TERM ] ... */, parent(-1))\n"
                  "    " + m.group(3))
    text = text[:m.start()] + new_scopes + text[m.end():]
    attr = re.search(r"\[\s*all-path\s*\]\s*$", text)
    em = re.search(r"(?<![\w-])ensures(?![\w-])", text)
    placeholder = "/* ENSURES: `ensures COND` pinning every ?-variable, or delete this comment */\n    "
    if em:
        text = text[:em.start()] + placeholder + text[attr.start():]
    else:
        text = text[:attr.start()] + placeholder + text[attr.start():]
    return text


def k_header(prog: Program, task_name: str) -> str:
    return (f"// Harbor task {task_name} — see instruction.md.\n"
            f"// Claim module for program.py over the klever MPY semantics ({VMOD}).\n"
            'requires "verification.k"\n\n'
            f"module {prog.spec_module}\n  imports {VMOD}\n\n")


def build_k_task(out: Out, prog: Program, family: str, registry: list[dict]) -> None:
    fam = "spec" if family == "proved-spec" else "inv"
    name = f"k-{fam}-{prog.slug}"
    base = f"tasks/{name}"
    can = canary(name)
    ctx = {
        "canary": can, "task_name": name, "family": family, "program": prog.key,
        "k_version": K_VERSION, "k_image": K_IMAGE, "verification_module": VMOD,
        "spec_module": prog.spec_module, "spec_dir": prog.spec_dir.name,
        "prover_seconds": str(prog.record["prover"]["wall_seconds"]),
        "program_code": program_display(prog).rstrip("\n"),
        "inputs_sentence": inputs_sentence_k(prog), "loop_phrase": prog.loop_phrase,
    }
    # environment
    out.put(f"{base}/environment/Dockerfile", render(tmpl("k", "Dockerfile"), ctx))
    src = ROOT / "vendor/klever/src"
    out.copy(f"{base}/environment/klever/src/semantics.k", src / "semantics.k")
    for f in sorted((src / "semantics").glob("*.k")):
        out.copy(f"{base}/environment/klever/src/semantics/{f.name}", f)
    verification_k = tmpl("k", "verification.k")
    out.put(f"{base}/environment/klever/verification.k", verification_k)
    out.put(f"{base}/environment/app/verification.k", verification_k)
    out.put(f"{base}/environment/app/program.py", program_display(prog))
    if fam == "spec":
        body = ("  // ---- Loop-invariant (circularity) claims go here, one per loop level, if the\n"
                "  //      program has loops ----\n\n"
                "  // ---- Entry claim: frozen except the FINAL-SCOPE and ENSURES placeholders ----\n"
                + claim_block(skeleton_spec(prog)))
    else:
        body = ("  // ---- Loop-invariant (circularity) claims go here, one per loop level ----\n\n"
                "  // ---- Entry claim (frozen) ----\n" + claim_block(prog.entry.text))
    out.put(f"{base}/environment/app/spec.k", k_header(prog, name) + body + "endmodule\n")
    # tests
    out.put(f"{base}/tests/test.sh", render(tmpl("k", "test.sh"), ctx), executable=True)
    out.put(f"{base}/tests/grade.py", render(tmpl("k", "grade.py"), ctx))
    out.copy(f"{base}/tests/kclaims.py", HERE / "kclaims.py")
    out.put(f"{base}/tests/verification.k", verification_k)
    ref = {
        "task": name, "family": family, "program": prog.key, "record": prog.record_stem,
        "verification_module": VMOD, "spec_module": prog.spec_module,
        "code": prog.code, "inputs": prog.inputs.to_json(), "fn_names": prog.fn_names,
        "requires": prog.entry.requires, "n_samples": N_SAMPLES, "seed": SEED,
        "kprove_timeout": KPROVE_TIMEOUT,
    }
    if fam == "spec":
        ref["frozen_parts"] = K.frozen_entry_parts(prog.entry)
    else:
        ref["entry_normalized"] = K.normalize(prog.entry.text)
    out.put(f"{base}/tests/reference.json", json.dumps(ref, indent=2, ensure_ascii=False) + "\n")
    # solution
    sol = re.sub(r"imports\s+[A-Z][A-Z0-9-]*-VERIFICATION", f"imports {VMOD}", prog.spec_text, count=1)
    out.put(f"{base}/solution/solve.sh", render(tmpl("k", "solve.sh"), ctx), executable=True)
    out.put(f"{base}/solution/spec.k", sol)
    # instruction + config
    out.put(f"{base}/instruction.md", render(tmpl("k", f"instruction_{fam}.md"), ctx))
    desc = (f"Write and prove, in K over the klever MPY semantics, the full final-state "
            f"specification of {prog.key} ({prog.loop_phrase})."
            if fam == "spec" else
            f"Find the loop invariant(s) — K circularity claims — that let kprove prove the "
            f"frozen final-state claim of {prog.key} ({prog.loop_phrase}).")
    out.put(f"{base}/task.toml", task_toml(
        name=name, canary=can, description=desc, family=family, toolchain="k", prog=prog,
        keywords=["k-framework", "reachability-logic", "formal-verification", family, "python-semantics"],
        verifier_timeout=1200, agent_timeout=3600, memory_mb=8192, build_timeout=2400,
        artifacts='["/app/spec.k"]',
        extra_meta={"reference_prover_seconds": str(prog.record["prover"]["wall_seconds"]),
                    "spec_module": toml_str(prog.spec_module),
                    "reference_claims": str(len(prog.others) + 1)}))
    registry.append({"name": name, "family": family, "toolchain": "k", "program": prog.key,
                     "tier": prog.tier, "loops": prog.loops, "depth": prog.depth})


def task_toml(*, name: str, canary: str, description: str, family: str, toolchain: str,
              prog: Program, keywords: list[str], verifier_timeout: int, agent_timeout: int,
              memory_mb: int, build_timeout: int, artifacts: str, extra_meta: dict[str, str]) -> str:
    meta = {
        "family": toml_str(family),
        "toolchain": toml_str(toolchain),
        "program": toml_str(prog.key),
        "k_record": toml_str(prog.record_stem),
        "tier": str(prog.tier),
        "loops": str(prog.loops),
        "loop_depth": str(prog.depth),
        "upstream": toml_str(prog.upstream),
        "difficulty": toml_str(difficulty(family, toolchain, prog.tier)),
        "category": toml_str("formal_verification"),
        "tags": toml_list(keywords),
    }
    meta.update(extra_meta)
    meta_lines = "\n".join(f"{k} = {v}" for k, v in meta.items())
    return f"""# harbor-canary GUID {canary}
schema_version = "1.4"
artifacts = {artifacts}

[task]
name = {toml_str(f"{ORG}/{name}")}
version = {toml_str(DATASET_VERSION)}
description = {toml_str(description)}
keywords = {toml_list(keywords)}
[[task.authors]]
name = {toml_str(ORG)}

[metadata]
{meta_lines}

[verifier]
timeout_sec = {verifier_timeout}.0
environment_mode = "separate"

[agent]
timeout_sec = {agent_timeout}.0

[environment]
network_mode = "no-network"
build_timeout_sec = {build_timeout}.0
memory_mb = {memory_mb}
os = "linux"
workdir = "/app"
"""


# ---------------------------------------------------------------------------
# Lean tasks
# ---------------------------------------------------------------------------

LEAN_VERIF = CORPUS / "lean" / "KMiniPy" / "Verification"
ID_RE = re.compile(r"[A-Za-z_][\w.']*")
ALLOWED_BODY_IDS = {"def", "pre", "post", "Pat", "fun", "pat", "init", "final", "iV", "Int",
                    "min", "max", "B1AbsVal.init", "B1AbsVal.final"}


def def_block(text: str, name: str) -> str | None:
    """`def <name> ...` through the next blank line, docstring excluded."""
    m = re.search(rf"(?m)^def {name}\b.*$", text)
    if not m:
        return None
    end = text.find("\n\n", m.start())
    return text[m.start(): end if end >= 0 else len(text)].rstrip() + "\n"


def doc_before(text: str, pos: int) -> int:
    """Start of the docstring immediately preceding position `pos`, else `pos`."""
    head = text[:pos].rstrip()
    if head.endswith("-/"):
        start = head.rfind("/--")
        if start >= 0:
            return start
    return pos


def last_rlone_theorem(text: str) -> tuple[str, str, int, int]:
    """(name, signature text up to ':=', start, end-of-signature) of the last theorem
    whose statement mentions RLOne."""
    found = None
    for m in re.finditer(r"(?m)^theorem (\w+)\b(.*?):=", text, re.S):
        if "RLOne" in m.group(2):
            found = m
    if not found:
        raise SystemExit("no RLOne theorem")
    sig = text[found.start(): found.end() - 2].rstrip()
    return found.group(1), sig, found.start(), found.end()


def body_ids_ok(block: str, binders: list[str]) -> None:
    bound = set(binders)
    for m in re.finditer(r"∃\s*\(?([\w\s]+?)\)?\s*:", block):
        bound |= set(m.group(1).split())
    for ident in ID_RE.findall(block):
        if ident in ALLOWED_BODY_IDS or ident in bound or ident == "γ":
            continue
        raise SystemExit(f"unexpected identifier {ident!r} in a pre/post body:\n{block}")


def qualify(text: str, owner_ns: str) -> str:
    return re.sub(r"(?<![\w.])(init|final)(?!\w)", lambda m: f"{owner_ns}.{m.group(1)}", text)


@dataclass
class LeanTask:
    name: str                 # C14KbSum
    file: Path
    text: str
    ns: str
    owner_module: str         # KMiniPy.Verification.C14KbSumLegs / KMiniPy.Symbolic.B1AbsVal / <Name>Paths
    owner_rel: str            # KMiniPy/Verification/C14KbSumLegs.lean
    owner_ns: str             # namespace holding init/final
    family: str               # loop-invariant | proved-spec
    prog: Program
    pre: str | None
    post: str | None
    thm_name: str
    thm_sig: str
    binders: list[str]
    stub: str = ""
    solution: str = ""
    paths_text: str | None = None


def lean_tasks(progs: dict[str, Program]) -> list[LeanTask]:
    by_num = {p.num: p for p in progs.values()}
    tasks: list[LeanTask] = []
    for f in sorted(LEAN_VERIF.glob("C*.lean")):
        if f.stem.endswith("Legs") or re.match(r"C3[A-Z]", f.stem):
            continue
        text = f.read_text(encoding="utf-8")
        num = int(re.match(r"C(\d+)", f.stem).group(1))
        prog = by_num[num]
        if f.stem == "C1SumToN":  # the Lean C1 mirror is sum_to_n, not the vendored range_loop
            prog = sum_to_n_program(progs["range_loop"])
        ns = re.search(r"(?m)^namespace (\w+)", text).group(1)
        imports = re.findall(r"(?m)^import (KMiniPy\.[\w.]+)", text)
        others = [i for i in imports if i not in ("KMiniPy.RL", "KMiniPy.Relations")]
        thm_name, sig, _s, _e = last_rlone_theorem(text)
        binders = []
        for m in re.finditer(r"\(([\w\s]+):\s*SortInt\)", sig):
            binders += m.group(1).split()
        pre, post = def_block(text, "pre"), def_block(text, "post")
        if others:
            owner_module = others[0]
            owner_rel = owner_module.replace(".", "/") + ".lean"
            owner_ns = owner_module.split(".")[-1]
            family = "loop-invariant" if owner_ns.endswith("Legs") else "proved-spec"
            paths_text = None
        else:
            owner_module = f"KMiniPy.Verification.{f.stem}Paths"
            owner_rel = f"KMiniPy/Verification/{f.stem}Paths.lean"
            owner_ns = ns
            family = "proved-spec"
            paths_text = ""  # filled below
        t = LeanTask(name=f.stem, file=f, text=text, ns=ns, owner_module=owner_module,
                     owner_rel=owner_rel, owner_ns=owner_ns, family=family, prog=prog,
                     pre=pre, post=post, thm_name=thm_name, thm_sig=sig, binders=binders,
                     paths_text=paths_text)
        for blk in (pre, post):
            if blk:
                body_ids_ok(blk, binders)
        build_lean_texts(t)
        tasks.append(t)
    return tasks


def sum_to_n_program(range_loop: Program) -> Program:
    """A Program view of programs/sum_to_n.py for the Lean C1 mirror (no K record of
    its own: the K-side c1 is the vendored range_loop)."""
    pf = ROOT / "programs" / "sum_to_n.py"
    code = pf.read_text(encoding="utf-8")
    rec = {"source": {"code": code, "entry": "sum_to_n", "args": {"n": "symbolic int"}, "file": "programs/sum_to_n.py"},
           "spec": {"requires": "n >= 0"}, "prover": {"wall_seconds": None}, "provenance": {}}
    p = Program(record_stem="c1_range_loop", num=1, key="sum_to_n", slug="sum-to-n", record=rec,
                spec_dir=range_loop.spec_dir, spec_text="", tier=EXTRA_TIERS["sum_to_n"], program_file=pf)
    p.loops, p.depth, p.loop_phrase = loop_info(code)
    return p


def build_lean_texts(t: LeanTask) -> None:
    text = t.text
    # ---- stub ----
    if t.family == "loop-invariant":
        head = (f"import {t.owner_module}\nimport KMiniPy.RL\n\n"
                "set_option linter.unusedVariables false\n\n"
                f"/-! # {t.name}: `{t.prog.key}` — the loop claim, to be derived\n\n"
                f"`{t.thm_name}` states the one-path reachability claim of this program over\n"
                f"the proved execution legs of `{t.owner_ns}`. Replace the `sorry` with a\n"
                "derivation in the `RL` calculus (see instruction.md). The statement, `pre`\n"
                "and `post` are frozen. -/\n\n"
                f"open RLogic\n\nnamespace {t.ns}\n\nopen {t.owner_ns}\n\n")
    elif t.paths_text is not None:
        head = (f"import {t.owner_module}\nimport KMiniPy.RL\n\n"
                f"/-! # {t.name}: `{t.prog.key}` — the functional spec, to be derived\n\n"
                f"`{t.thm_name}` states the one-path reachability claim of this program over\n"
                f"the proved path theorems of `{t.owner_module}`. Replace the `sorry` with a\n"
                "derivation in the `RL` calculus (see instruction.md). The statement (and\n"
                "`post`) are frozen. -/\n\n"
                f"open RLogic\n\nnamespace {t.ns}\n\n")
    else:  # C2 over B1
        head = (f"import {t.owner_module}\nimport KMiniPy.RL\n\n"
                f"/-! # {t.name}: `{t.prog.key}` — the functional spec, to be derived\n\n"
                f"`{t.thm_name}` states the one-path reachability claim of this program over\n"
                f"the proved symbolic paths of `{t.owner_ns}`. Replace the `sorry` with a\n"
                "derivation in the `RL` calculus (see instruction.md). The statement, `pre`\n"
                "and `post` are frozen. -/\n\n"
                f"open RLogic\n\nnamespace {t.ns}\n\n")
    parts = [head]
    if t.pre:
        parts.append(doc_of(text, "pre") + t.pre + "\n")
    if t.post:
        parts.append(doc_of(text, "post") + t.post + "\n")
    parts.append(f"/-- The claim. Replace `sorry` with a complete derivation. -/\n{t.thm_sig} := by\n  sorry\n\nend {t.ns}\n")
    t.stub = "".join(parts)
    # ---- solution / paths ----
    if t.paths_text is None:
        t.solution = text
    else:
        anchor = re.search(r"(?m)^def post\b", text)
        pos = anchor.start() if anchor else last_rlone_theorem(text)[2]
        pos = doc_before(text, pos)
        t.paths_text = text[:pos].rstrip() + f"\n\nend {t.ns}\n"
        t.solution = (f"import {t.owner_module}\nimport KMiniPy.RL\n\n"
                      f"/-! # {t.name}: reachability-logic derivation over `{t.owner_module}`\n"
                      "(the proved path theorems; split out of the corpus file for this task). -/\n\n"
                      f"open RLogic\n\nnamespace {t.ns}\n\n" + text[pos:])
    if "sorry" in t.solution or t.solution == t.stub:
        raise SystemExit(f"bad solution for {t.name}")


def doc_of(text: str, name: str) -> str:
    m = re.search(rf"(?m)^def {name}\b", text)
    start = doc_before(text, m.start())
    return text[start:m.start()] if start < m.start() else ""


def check_lean(t: LeanTask) -> str:
    """The verifier's Check.lean: the frozen statement over verifier-owned
    `init`/`final`, closed by the agent's theorem, then the axiom audit."""
    lines = [f"import KMiniPy.Verification.{t.name}", "", "open RLogic", "", "namespace HarborCheck", ""]
    sig = t.thm_sig
    if t.pre:
        lines += [qualify(t.pre.replace("def pre", "def refPre", 1), t.owner_ns)]
        sig = re.sub(r"(?<![\w.])pre(?!\w)", "refPre", sig)
    if t.post:
        lines += [qualify(t.post.replace("def post", "def refPost", 1), t.owner_ns)]
        sig = re.sub(r"(?<![\w.])post(?!\w)", "refPost", sig)
    sig = qualify(sig, t.owner_ns)
    sig = re.sub(r"^theorem \w+", "theorem check", sig)
    args = " ".join(t.binders)
    lines += [f"{sig} :=", f"  {t.ns}.{t.thm_name} {args}", "", "end HarborCheck", "",
              "#print axioms HarborCheck.check", ""]
    return "\n".join(lines)


def inputs_sentence_lean(t: LeanTask) -> str:
    prog = t.prog
    b = ", ".join(f"`{x}`" for x in t.binders)
    if prog.program_file is not None and prog.inputs is not None and prog.inputs.module:
        lits = {}
        for ln in prog.program_file.read_text(encoding="utf-8").splitlines():
            m = re.match(r"(\w+)\s*=\s*(-?\d+)\s*$", ln)
            if m:
                lits.setdefault(m.group(1), m.group(2))
        litxt = ", ".join(f"`{lits.get(x, '?')}`" for x in t.binders)
        return (f"The inputs are the module variables {b}, written as the literals {litxt} in the "
                f"program; the claim quantifies over them as `SortInt` binders. Precondition: "
                f"{prog.requires_english}.")
    fn = prog.fn_names[0] if prog.fn_names else prog.key
    return (f"The input is the argument {b} of `{fn}` (a literal in the program file, a `SortInt` "
            f"binder in the claim). Precondition: {prog.requires_english}.")


def build_lean_task(out: Out, t: LeanTask, registry: list[dict]) -> None:
    fam = "spec" if t.family == "proved-spec" else "inv"
    name = f"lean-{fam}-{t.prog.slug}"
    base = f"tasks/{name}"
    can = canary(name)
    stub_file = f"{t.name}.lean"
    claim_lean = "\n\n".join(x for x in [t.pre.rstrip() if t.pre else None,
                                          t.post.rstrip() if t.post else None,
                                          t.thm_sig] if x)
    ctx = {
        "canary": can, "task_name": name, "family": t.family, "program": t.prog.key,
        "lean_toolchain": LEAN_TOOLCHAIN, "stub_file": stub_file, "owner_file": Path(t.owner_rel).name,
        "owner_path": t.owner_rel, "namespace": t.ns, "theorem": t.thm_name,
        "program_code": (t.prog.program_file.read_text(encoding="utf-8") if t.prog.program_file
                         else t.prog.code).rstrip("\n"),
        "inputs_sentence": inputs_sentence_lean(t), "loop_phrase": t.prog.loop_phrase,
        "claim_lean": claim_lean,
        "solution_rel": f"Verification/{t.name}.lean",
    }
    lean_root = CORPUS / "lean"
    base_root = "import KMiniPy.Rewrite\nimport KMiniPy.Relations\nimport KMiniPy.RL\n"
    task_root = base_root + f"import {t.owner_module}\nimport KMiniPy.Verification.{t.name}\n"
    # environment/base (shared layer)
    for fn in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
        out.copy(f"{base}/environment/base/{fn}", lean_root / fn)
        out.copy(f"{base}/tests/pristine/{fn}", lean_root / fn)
    out.put(f"{base}/environment/base/KMiniPy.lean", base_root)
    for mod in LEAN_BASE:
        out.copy(f"{base}/environment/base/KMiniPy/{mod}.lean", lean_root / "KMiniPy" / f"{mod}.lean")
        out.copy(f"{base}/tests/pristine/KMiniPy/{mod}.lean", lean_root / "KMiniPy" / f"{mod}.lean")
    # environment/task
    out.put(f"{base}/environment/task/KMiniPy.lean", task_root)
    out.put(f"{base}/tests/pristine/KMiniPy.lean", task_root)
    if t.paths_text is not None:
        out.put(f"{base}/environment/task/{t.owner_rel}", t.paths_text)
        out.put(f"{base}/tests/pristine/{t.owner_rel}", t.paths_text)
    else:
        out.copy(f"{base}/environment/task/{t.owner_rel}", lean_root / t.owner_rel)
        out.copy(f"{base}/tests/pristine/{t.owner_rel}", lean_root / t.owner_rel)
    out.put(f"{base}/environment/task/KMiniPy/Verification/{stub_file}", t.stub)
    out.put(f"{base}/environment/Dockerfile", render(tmpl("lean", "Dockerfile"), ctx))
    # tests
    out.put(f"{base}/tests/test.sh", render(tmpl("lean", "test.sh"), ctx), executable=True)
    out.put(f"{base}/tests/grade.py", render(tmpl("lean", "grade.py"), ctx))
    out.put(f"{base}/tests/Check.lean", check_lean(t))
    # solution
    out.put(f"{base}/solution/solve.sh", render(tmpl("lean", "solve.sh"), ctx), executable=True)
    out.put(f"{base}/solution/{stub_file}", t.solution)
    # instruction + config
    out.put(f"{base}/instruction.md", render(tmpl("lean", f"instruction_{fam}.md"), ctx))
    desc = (f"Derive, in the reachability-logic calculus of KMiniPy (Lean 4), the frozen "
            f"functional specification of {t.prog.key} from its proved execution paths."
            if fam == "spec" else
            f"Invent the loop invariant and derive, by Circularity in the reachability-logic "
            f"calculus of KMiniPy (Lean 4), the frozen claim of {t.prog.key} ({t.prog.loop_phrase}) "
            f"over its proved execution legs.")
    out.put(f"{base}/task.toml", task_toml(
        name=name, canary=can, description=desc, family=t.family, toolchain="lean", prog=t.prog,
        keywords=["lean4", "reachability-logic", "formal-verification", t.family, "k-framework"],
        verifier_timeout=1800, agent_timeout=3600, memory_mb=6144, build_timeout=2400,
        artifacts='[{ source = "/app", destination = "app", exclude = [".lake", ".lake/**"] }]',
        extra_meta={"lean_module": toml_str(f"KMiniPy.Verification.{t.name}"),
                    "theorem": toml_str(f"{t.ns}.{t.thm_name}"),
                    "legs_module": toml_str(t.owner_module)}))
    registry.append({"name": name, "family": t.family, "toolchain": "lean", "program": t.prog.key,
                     "tier": t.prog.tier, "loops": t.prog.loops, "depth": t.prog.depth})


# ---------------------------------------------------------------------------
# registry + driver
# ---------------------------------------------------------------------------

def registry_json(rows: list[dict]) -> str:
    def ds(name: str, desc: str, pred) -> dict:
        return {"name": name, "version": DATASET_VERSION, "description": desc,
                "tasks": [{"name": r["name"], "path": f"tasks/{r['name']}"} for r in rows if pred(r)]}
    datasets = [
        ds("all", "Every task: proved specs and loop invariants, K and Lean 4.", lambda r: True),
        ds("proved-specs", "Write/derive and prove full final-state specifications (K + Lean).",
           lambda r: r["family"] == "proved-spec"),
        ds("loop-invariants", "Find loop invariants that close a frozen claim (K circularities, Lean Circularity).",
           lambda r: r["family"] == "loop-invariant"),
        ds("k-proved-specs", "K: complete the entry claim (final scope + ensures + circularities) and prove it with kprove.",
           lambda r: r["toolchain"] == "k" and r["family"] == "proved-spec"),
        ds("k-loop-invariants", "K: add the circularity claims that let kprove prove the frozen entry claim.",
           lambda r: r["toolchain"] == "k" and r["family"] == "loop-invariant"),
        ds("lean-proved-specs", "Lean 4: derive the frozen functional spec in reachability logic over proved paths.",
           lambda r: r["toolchain"] == "lean" and r["family"] == "proved-spec"),
        ds("lean-loop-invariants", "Lean 4: invent the invariant and derive the frozen loop claim by Circularity over proved legs.",
           lambda r: r["toolchain"] == "lean" and r["family"] == "loop-invariant"),
    ]
    for d in datasets:
        d["metrics"] = [{"type": "mean", "kwargs": {}}]
    return json.dumps(datasets, indent=2) + "\n"


def build(out_root: Path) -> list[dict]:
    progs = load_programs()
    out = Out()
    rows: list[dict] = []
    for key in sorted(progs, key=lambda k: progs[k].num):
        prog = progs[key]
        build_k_task(out, prog, "proved-spec", rows)
        if prog.others:
            build_k_task(out, prog, "loop-invariant", rows)
    for t in lean_tasks(progs):
        build_lean_task(out, t, rows)
    out.put("registry.json", registry_json(rows))
    out.put("tasks/INDEX.json", json.dumps(rows, indent=2) + "\n")
    if out_root.exists():
        for child in (out_root / "tasks").glob("*") if (out_root / "tasks").exists() else []:
            shutil.rmtree(child) if child.is_dir() else child.unlink()
    out.write_all(out_root)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=ROOT, help="repo root to write tasks/ and registry.json into")
    a = ap.parse_args()
    rows = build(a.out)
    fam = {}
    for r in rows:
        fam[(r["toolchain"], r["family"])] = fam.get((r["toolchain"], r["family"]), 0) + 1
    for k, v in sorted(fam.items()):
        print(f"{k[0]:5s} {k[1]:15s} {v}")
    print(f"{len(rows)} tasks -> {a.out / 'tasks'}")
    if a.out == ROOT:
        try:  # record the executable bit for the shell scripts (Windows checkouts cannot)
            files = [str(p.relative_to(ROOT)).replace("\\", "/")
                     for p in (ROOT / "tasks").glob("*/*/*.sh")]
            subprocess.run(["git", "update-index", "--add", "--chmod=+x", *files],
                           cwd=ROOT, check=False, capture_output=True)
        except OSError:
            pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
