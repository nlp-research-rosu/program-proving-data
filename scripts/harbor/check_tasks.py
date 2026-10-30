#!/usr/bin/env python3
"""check_tasks — everything about tasks/ that can be verified without Docker.

  1. drift: regenerating into a scratch directory reproduces tasks/ and
     registry.json byte for byte;
  2. shape: every task has the Harbor files, the shell scripts are executable in
     the git index, task.toml parses, canaries are consistent;
  3. K verifiers offline: the reference solution passes every grader step but
     kprove; the skeleton handed to the agent fails (so the nop agent scores 0);
     the whitelist rejects a handful of known gaming attempts;
  4. no leaks: the files the agent sees contain no circularity anchor, no
     reference ensures, no `.circ`/invariant text; every Lean stub has exactly
     one `sorry`, every Lean solution none; Check.lean names resolve.

Exit status 1 on any failure. Used by CI and `make harbor-check`.
"""
from __future__ import annotations

import json
import re
import shlex
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import build_tasks  # noqa: E402
import kclaims as K  # noqa: E402

FAIL: list[str] = []
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def check(cond: bool, msg: str) -> None:
    print(f"[{'ok' if cond else 'FAIL'}] {msg}")
    if not cond:
        FAIL.append(msg)


def drift() -> None:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        build_tasks.build(tmp)
        fresh = {str(p.relative_to(tmp)).replace("\\", "/"): p.read_bytes() for p in tmp.rglob("*") if p.is_file()}
        have = {str(p.relative_to(ROOT)).replace("\\", "/"): p.read_bytes()
                for p in list((ROOT / "tasks").rglob("*")) + [ROOT / "registry.json"] if p.is_file()}
        missing = sorted(set(fresh) - set(have))
        extra = sorted(set(have) - set(fresh))
        differ = sorted(k for k in fresh if k in have and fresh[k] != have[k])
        check(not missing and not extra and not differ,
              f"tasks/ and registry.json are up to date (missing {len(missing)}, extra {len(extra)}, differ {len(differ)})")
        for k in (missing + extra + differ)[:10]:
            print("    ", k)


def git_modes() -> dict[str, str]:
    try:
        out = subprocess.run(["git", "ls-files", "-s", "tasks"], cwd=ROOT, capture_output=True,
                             text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        return {}
    modes = {}
    for ln in out.splitlines():
        mode, _sha, _stage, path = ln.split(None, 3)
        modes[path] = mode
    return modes


def shape() -> list[Path]:
    tasks = sorted(p for p in (ROOT / "tasks").iterdir() if p.is_dir())
    check(len(tasks) == 87, f"87 task directories (found {len(tasks)})")
    modes = git_modes()
    for t in tasks:
        req = ["instruction.md", "task.toml", "environment/Dockerfile", "tests/test.sh", "solution/solve.sh"]
        missing = [r for r in req if not (t / r).is_file()]
        check(not missing, f"{t.name}: required files present" + (f" (missing {missing})" if missing else ""))
        cfg = tomllib.loads((t / "task.toml").read_text(encoding="utf-8"))
        check(cfg["task"]["name"] == f"{build_tasks.ORG}/{t.name}", f"{t.name}: task.toml name matches directory")
        check(cfg["verifier"]["environment_mode"] == "separate" and cfg["environment"]["network_mode"] == "no-network",
              f"{t.name}: separate verifier, no network")
        can = build_tasks.canary(t.name)
        for f in ("instruction.md", "task.toml", "tests/test.sh", "solution/solve.sh", "environment/Dockerfile"):
            check(can in (t / f).read_text(encoding="utf-8"), f"{t.name}: canary in {f}")
        for sh in ("tests/test.sh", "solution/solve.sh"):
            rel = f"tasks/{t.name}/{sh}"
            if modes:
                check(modes.get(rel) == "100755", f"{t.name}: {sh} is executable in the index ({modes.get(rel)})")
            check(b"\r" not in (t / sh).read_bytes(), f"{t.name}: {sh} has LF line endings")
    return tasks


def k_offline(t: Path) -> None:
    ref = json.loads((t / "tests" / "reference.json").read_text(encoding="utf-8"))
    sol = (t / "solution" / "spec.k").read_text(encoding="utf-8")
    skel = (t / "environment" / "app" / "spec.k").read_text(encoding="utf-8")
    fam = ref["family"]
    instruction = (t / "instruction.md").read_text(encoding="utf-8")
    cmd = re.search(r"(?m)^cd /app && (timeout .+)$", instruction)
    expected = ["timeout", str(ref["kprove_timeout"]), "kprove", "spec.k",
                "--definition", "/opt/klever/kompiled", "--spec-module", ref["spec_module"],
                *ref["kprove_flags"]]
    check(cmd is not None and shlex.split(cmd.group(1)) == expected,
          f"{t.name}: instruction command preserves the grader's argument boundaries")
    preflight = f"kprove {shlex.join(ref['kprove_flags'])} --help-hidden"
    check(preflight in (t / "environment" / "Dockerfile").read_text(encoding="utf-8"),
          f"{t.name}: image checks prover flags before compiling")

    def grade(text: str) -> list[str]:
        """Every grader step except kprove, as a list of problems."""
        try:
            mod = K.parse_module(text, verification_module=ref["verification_module"])
            entry, others = K.entry_claim(mod, k_cell=ref["entry_k"])
        except K.SpecError as e:
            return [f"grammar: {e}"]
        if fam == "loop-invariant":
            probs = [] if K.normalize(entry.text) == ref["entry_normalized"] else ["entry claim changed"]
            if not others:
                probs.append("no additional claims")
            return probs
        probs = K.check_frozen(entry, ref["frozen_parts"])
        probs += K.check_closed_forms(entry, code=ref["code"], inputs=K.Inputs.from_json(ref["inputs"]),
                                      requires=ref["requires"], fn_names=ref["fn_names"],
                                      n_samples=ref["n_samples"], seed=ref["seed"])
        return probs

    check(not grade(sol), f"{t.name}: reference solution passes the offline grader")
    check(bool(grade(skel)), f"{t.name}: untouched skeleton fails the offline grader")
    # the skeleton and instruction must not leak the reference
    seen = K.normalize(skel + (t / "instruction.md").read_text(encoding="utf-8"))
    check("#while(" not in skel and "#loop(" not in skel,
          f"{t.name}: no circularity anchor in the skeleton")
    m = K.parse_module(sol, verification_module=ref["verification_module"])
    ref_entry, ref_others = K.entry_claim(m)
    entry_ens = K.normalize(ref_entry.ensures or "")
    for i, c in enumerate(ref_others):
        ens = K.normalize(c.ensures or "")
        leaked_ens = bool(ens) and ens != entry_ens and ens in seen  # the entry's own ensures is given
        check(K.normalize(c.cells["k"]) not in seen and not leaked_ens,
              f"{t.name}: reference circularity {i} not in the agent-visible files")
    if fam == "proved-spec":
        check(ref_entry.ensures is None or K.normalize(ref_entry.ensures) not in seen,
              f"{t.name}: reference ensures not in the agent-visible files")
        _lhs, ref_rhs = K.split_scopes(ref_entry.cells["scopes"])
        check(K.normalize(ref_rhs) not in seen, f"{t.name}: reference final scope not in the agent-visible files")
    # gaming attempts the whitelist must reject
    attempts = {
        "trusted claim": sol.replace("[all-path]", "[trusted]", 1),
        "simplification rule": sol.replace("endmodule", "  rule X:Int ==Int Y:Int => true [simplification]\nendmodule"),
        "extra requires": sol.replace('requires "verification.k"', 'requires "verification.k"\nrequires "lemmas.k"'),
        "extra import": sol.replace("imports MPY-VERIFICATION", "imports MPY-VERIFICATION\n  imports MPY-LEMMAS"),
        "second module": sol + "\nmodule EXTRA\n  imports MPY-VERIFICATION\n  rule X => Y\nendmodule\n",
    }
    for label, text in attempts.items():
        check(bool(grade(text)), f"{t.name}: whitelist rejects {label}")
    if ref_others:  # an attribute group smuggled onto a circularity
        first = ref_others[0]
        check(bool(grade(sol.replace(first.text, first.text.replace("[all-path]", "[all-path, comm]"), 1))),
              f"{t.name}: comma-separated attribute group is rejected")
        # a <scopeLoc> cell on a circularity is legal K and must stay admissible
        with_loc = sol.replace(first.text, first.text.replace("<exc> NoExc </exc>",
                                                              "<exc> NoExc </exc>\n    <scopeLoc> _ </scopeLoc>"), 1)
        check(not grade(with_loc), f"{t.name}: a circularity carrying <scopeLoc> is still accepted")
    if fam == "proved-spec":
        e = ref_entry
        if e.ensures:
            head, _sep, tail = sol.rpartition(e.ensures)
            weak_forms = {
                "`ensures true`": "true",
                "band-restricted ensures": f"(({e.ensures}) andBool N <=Int 25) orBool N >Int 25".replace("N", ref["inputs"]["module"][0][1] if ref["inputs"]["module"] else ref["inputs"]["call"][0][1]),
                "disjunction of candidates": f"({e.ensures}) orBool ({e.ensures.replace('==Int', '==Int 1 +Int', 1)})",
                "==Bool tautology": f"{e.ensures} andBool 1 ==Int 2 ==Bool false",
                "existential under notBool": f"{e.ensures} andBool notBool false",
            }
            for label, ens in weak_forms.items():
                probs = grade(head + ens + tail)
                check(bool(probs) if label != "existential under notBool" else not probs,
                      f"{t.name}: {label} -> {'rejected' if label != 'existential under notBool' else 'accepted (no existential involved)'}")
    else:
        weakened = re.sub(r"ensures", "ensures true andBool", sol)
        check(bool(grade(weakened)), f"{t.name}: a modified entry claim is rejected")


def lean_offline(t: Path) -> None:
    cfg = tomllib.loads((t / "task.toml").read_text(encoding="utf-8"))
    mod = cfg["metadata"]["lean_module"].split(".")[-1]
    instruction = (t / "instruction.md").read_text(encoding="utf-8")
    scratch_imports = re.findall(r"`import ([\w.]+)`", instruction)
    check(scratch_imports == [cfg["metadata"]["lean_module"]],
          f"{t.name}: scratch-file example imports the proof module")
    stub = (t / "environment" / "task" / "KMiniPy" / "Verification" / f"{mod}.lean").read_text(encoding="utf-8")
    sol = (t / "solution" / f"{mod}.lean").read_text(encoding="utf-8")
    chk = (t / "tests" / "Check.lean").read_text(encoding="utf-8")
    code_only = re.sub(r"/-.*?-/", "", stub, flags=re.S)
    code_only = re.sub(r"--.*", "", code_only)
    check(code_only.count("sorry") == 1, f"{t.name}: stub has exactly one sorry")
    check("sorry" not in sol, f"{t.name}: solution has no sorry")
    check(".circ" not in stub and "inv " not in stub and "Circularity" not in stub.split("open RLogic")[0].replace("Circularity derivation", ""),
          f"{t.name}: stub carries no derivation text")
    thm = cfg["metadata"]["theorem"]
    spec_ns = cfg["metadata"]["spec_module"].split(".")[-1]
    check(f"_root_.{thm} " in chk and f"_root_.{spec_ns}.statement" in chk, f"{t.name}: Check.lean closes {spec_ns}.statement with {thm}")
    check("#print axioms harborCheck" in chk and "open " not in chk and "namespace " not in chk,
          f"{t.name}: Check.lean audits axioms, no open/namespace")
    legs = cfg["metadata"]["legs_module"].replace(".", "/") + ".lean"
    check((t / "tests" / "pristine" / legs).is_file() and (t / "environment" / "task" / legs).is_file(),
          f"{t.name}: legs/paths module present in environment and pristine copy")
    legs_env = (t / "environment" / "task" / legs).read_text(encoding="utf-8")
    doc = re.search(r"/-!(.*?)-/", legs_env, re.S)
    check(doc is not None and not re.search(r"Circularity|fuel induction|derivation \(", doc.group(1)),
          f"{t.name}: legs module docstring carries no derivation plan")
    spec_rel = f"KMiniPy/Verification/{spec_ns}.lean"
    spec_txt = (t / "environment" / "task" / spec_rel).read_text(encoding="utf-8")
    check((t / "tests" / "pristine" / spec_rel).read_text(encoding="utf-8") == spec_txt
          and "abbrev statement : Prop := ∀" in spec_txt, f"{t.name}: Spec module in environment and pristine, with statement")
    check(f"import KMiniPy.Verification.{spec_ns}" in (t / "tests" / "pristine" / "KMiniPy.lean").read_text(encoding="utf-8"),
          f"{t.name}: root module imports the Spec module")
    check("def pre" not in stub and "def post" not in stub and f"open {spec_ns}" in stub,
          f"{t.name}: stub takes pre/post from the Spec module")
    check(not (t / "tests" / "pristine" / "KMiniPy" / "Verification" / f"{mod}.lean").exists(),
          f"{t.name}: the agent's module is not in the pristine set")
    # the solution's and stub's theorem statements agree
    def sig(text: str) -> str:
        m = re.search(r"(?m)^theorem (\w+)\b(.*?):=", text, re.S)
        return re.sub(r"\s+", " ", m.group(0)) if m else ""
    stub_sigs = [re.sub(r"\s+", " ", m.group(0)) for m in re.finditer(r"(?m)^theorem (\w+)\b(.*?):=", stub, re.S)]
    sol_sigs = [re.sub(r"\s+", " ", m.group(0)) for m in re.finditer(r"(?m)^theorem (\w+)\b(.*?):=", sol, re.S)]
    check(len(stub_sigs) == 1 and stub_sigs[0] in sol_sigs, f"{t.name}: stub theorem statement is the solution's")
    # the reference solution (and the stub) must pass the grader's lexical ban
    import importlib.util
    spec = importlib.util.spec_from_file_location(f"grade_{t.name}".replace("-", "_"), t / "tests" / "grade.py")
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    for label, text in (("solution", sol), ("stub", stub)):
        probs = g.lexical_problems(g.strip_lean_comments(text), label)
        check(not probs, f"{t.name}: {label} passes the lexical ban" + (f" ({probs})" if probs else ""))
    for bad in ("set_option debug.skipKernelTC true in\n", "unsafe def x := 1\n", "#eval IO.println 1\n",
                "import Lean\n", "import  Lean\n", "import\tLean\n", "@[init] def payload : IO Unit := pure ()\n",
                'notation "RLOne" a:max b:max => True\n', "instance (priority := high) : LE Int := ⟨fun _ _ => False⟩\n",
                "attribute [simp] Nat.add_comm\n", "#print axioms foo\n", "open Lean Elab Command\n",
                "def _root_.HarborCheck.x := 1\n"):
        probs = g.lexical_problems(g.strip_lean_comments(bad + sol), "probe")
        check(bool(probs), f"{t.name}: lexical ban catches {bad.strip()!r}")


def registry() -> None:
    reg = json.loads((ROOT / "registry.json").read_text(encoding="utf-8"))
    names = {d["name"]: d for d in reg}
    check(len(names["all"]["tasks"]) == 87, "registry: `all` lists 87 tasks")
    for d in reg:
        for task in d["tasks"]:
            check((ROOT / task["path"] / "task.toml").is_file(), f"registry {d['name']}: {task['path']} exists")


def main() -> int:
    drift()
    tasks = shape()
    for t in tasks:
        if t.name.startswith("k-"):
            k_offline(t)
        else:
            lean_offline(t)
    registry()
    print(f"\n{len(FAIL)} failure(s)")
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
