#!/usr/bin/env python3
"""gen_lean_traces — emit Lean theorem files for the concrete-trace samples.

Statement mode (default): per program, print the initial and final
configurations as Lean terms (using pyk.klean's own pattern printer, so the
terms match the generated Sorts/Inj modules exactly) and emit the headline
theorem `Rewrites init final := sorry`, plus the `Reaches` corollary.

--prove mode (stage B): additionally reconstruct the per-step rule sequence
(from a krun --depth sweep, matching each step's redex against the rule set
via the LLVM proof-hints pipeline is not needed here: the sweep itself yields
the applied-rule ordinals via kore-proof-trace on a hints build) and emit the
proof as a right-nested `Rewrites.tran` fold of per-step theorems. Every
intermediate configuration is printed explicitly (`def c<i>`, from the krun
sweep): a chain with implicit configs stalls elaboration wherever unification
must invert a K function. Constructor hypothesis arities (how many
hypothesis tactics to emit) are parsed from Rewrite.lean.

Ground hypothesis goals are closed by ONE uniform tactic (TACTIC below):
`rfl` handles the non-recursive K functions; the WF-recursive mutual ones
(vsnoc/snocW/lookup/update/flookup — @[irreducible], never reduce by rfl)
need `simp` with their equation lemmas; `eqStringHook` (Relations.lean)
interprets the signature-only String-equality hook axiom; the trailing
`<;> rfl` clears `Option`/`failure` residue.

Cool-rule constructors additionally need SortExpr-typed implicits that sit
under `@inj SortExpr SortKItem` in the rule LHS passed EXPLICITLY (named
args): `Inj SortExpr SortKItem` is a normalizing match, so unification of
`inj ?HOLE` against the collapsed `SortKItem.inj_SortVal v` in the source
state is stuck on the metavariable. The values are recovered by structurally
matching the rule's kore LHS against the step's source configuration
(match_lhs below) and printed with the klean printer.

Watchdogs: every subprocess runs under timeout (krun 120 s each)."""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent          # repo root
REPO = ROOT
DEFN = ROOT / "build/lean/minipy-lean"
HINTS_DEFN = ROOT / "build/lean/minipy-lean-hints"
PKG = ROOT / "corpus/lean"

sys.path.insert(0, str(REPO / ".venv/lib/python3.12/site-packages"))

from pyk.kore.parser import KoreParser  # noqa: E402
from pyk.kore.internal import KoreDefn  # noqa: E402
from pyk.kore.syntax import And, App, EVar  # noqa: E402
from pyk.klean.k2lean4 import K2Lean4, _escape_ident, _rule_name, _var_ident  # noqa: E402

SAMPLES = [
    # (subpackage, theorem file, program stem, argument substitution)
    ("Concrete", "A1SumToN", "sum_to_n", None),
    ("Concrete", "A2Gcd", "gcd", None),
    ("Verification", "C3BuggyAbsAt0", "buggy_abs", ("31337", "0")),
    ("Concrete", "A3CollatzSteps", "collatz_steps", None),
    ("Concrete", "A4HalfOfEven", "half_of_even", None),
]

MAX_STEPS = 2000


def load_printer() -> K2Lean4:
    defn = KoreDefn.from_definition(KoreParser((DEFN / "definition.kore").read_text()).definition())
    return K2Lean4(defn.project_to_rewrites())


def krun_kore(mpy: Path, depth: int | None) -> str:
    cmd = ["timeout", "120", "krun", "--definition", str(DEFN), str(mpy), "--output", "kore"]
    if depth is not None:
        cmd += ["--depth", str(depth)]
    p = subprocess.run(cmd, capture_output=True, text=True)
    assert p.returncode == 0, p.stderr[:800]
    return p.stdout.strip()


def sweep(mpy: Path) -> list[str]:
    """Configurations c_0..c_N (kore text) until the fixed point."""
    configs = [krun_kore(mpy, 0)]
    final = krun_kore(mpy, None)
    k = 0
    while configs[-1] != final:
        k += 1
        assert k <= MAX_STEPS, "runaway sweep"
        configs.append(krun_kore(mpy, k))
    return configs


def rule_sequence(stem: str, mpy: Path) -> list[str]:
    """Applied top-level rule labels, in order, via the proof-hints pipeline."""
    hints = ROOT / "build/lean" / f"{stem}.hints"
    txt = ROOT / "build/lean" / f"{stem}.hints.txt"
    header = ROOT / "build/lean/hints-header.bin"
    if not header.exists():
        subprocess.run(["timeout", "120", "kore-rich-header", str(HINTS_DEFN / "definition.kore"),
                        "-o", str(header)], check=True)
    with open(hints, "wb") as fh:
        subprocess.run(["timeout", "120", "krun", "--definition", str(HINTS_DEFN), str(mpy),
                        "--proof-hint"], stdout=fh, check=True)
    with open(txt, "w") as fh:
        subprocess.run(["timeout", "300", "kore-proof-trace", "--verbose", str(header),
                        str(hints), str(HINTS_DEFN / "definition.kore")], stdout=fh,
                       stderr=subprocess.STDOUT, check=True)
    labels, depth = [], 0
    rule_re = re.compile(r"rule: (\d+) ")
    for line in txt.read_text().splitlines():
        if line.startswith("function:"):
            depth += 1
        elif line.startswith("function exit:"):
            depth -= 1
        elif line.startswith("rule:") and depth == 0:
            labels.append(int(rule_re.match(line).group(1)))
    return labels


def ordinal_to_label(defn_dir: Path) -> dict[int, str]:
    """Axiom ordinal -> rule label, from definition.kore axiom order."""
    kore = KoreParser((defn_dir / "definition.kore").read_text()).definition()
    out: dict[int, str] = {}
    ordinal = 0
    for module in kore.modules:
        for sent in module.sentences:
            if type(sent).__name__ == "Axiom":
                label = uid = None
                for attr in sent.attrs:
                    if attr.symbol == "label":
                        label = attr.args[0].value
                    elif attr.symbol == "UNIQUE'Unds'ID":
                        uid = attr.args[0].value
                if label:
                    out[ordinal] = _escape_ident(label.replace("-", "_").replace(".", "_"))
                elif uid:
                    out[ordinal] = f"_{uid[:7]}"
                ordinal += 1
    return out


def ctor_arities(rewrite_lean: Path) -> dict[str, tuple[int, bool]]:
    """label -> (#defn hypotheses, has req) parsed from generated Rewrite.lean."""
    out: dict[str, tuple[int, bool]] = {}
    for line in rewrite_lean.read_text().splitlines():
        m = re.match(r"\s*\|\s*(«[^»]+»|\w+)\s*(.*):\s*Rewrites .*", line)
        if not m:
            continue
        name, sig = m.group(1), m.group(2)
        ndefs = len(re.findall(r"\(defn\w*\s*:", sig))
        has_req = "(req " in sig or "(req: " in sig or "(req :" in sig
        out[name] = (ndefs, has_req)
    return out


# One uniform tactic for every ground hypothesis argument (see module docstring).
TACTIC = (
    "first | rfl | (simp [«vsnoc(_,_)_MINIPY-LEAN_Vals_Vals_Val», _b922119, _f20aa8c, "
    "«snocW(_,_,_)_MINIPY-LEAN_Stmts_Stmts_Expr_Stmts», _0e7f4fe, _50a6500, "
    "«lookup(_,_)_MINIPY-LEAN_OptVal_Env_String», _639b4ef, _95e90d4, _9ce0d02, "
    "«update(_,_,_)_MINIPY-LEAN_Env_Env_String_Val», _bd0f5e0, _c952276, _f3c9862, "
    "«flookup(_,_)_MINIPY-LEAN_OptFun_Funs_String», _ae92d99, _efd7dee, _f5f3f2e, "
    "«_=/=String__STRING-COMMON_Bool_String_String», _f390a9b, "
    "notBool_, _17ebc68, _53fc758, eqStringHook, guard] <;> rfl)"
)

# Supersorts whose Inj instance into SortKItem is a normalizing `match`
# (klean emits one whenever the supersort has its own inj_* constructors):
# bare rule binders of these sorts under `inj` cannot be solved by unification.
NORMALIZING_SUPERSORTS = {"SortExpr", "SortKResult"}


def match_lhs(pattern, subject, binds: dict, needs: set) -> None:
    """Best-effort structural match of a rule's kore LHS against a concrete
    configuration. Records EVar bindings (as kore patterns) in `binds` and, in
    `needs`, binders that sit bare under a normalizing injection (these must be
    emitted as explicit named args). Collapsed injections in the subject
    (`inj{C,B}` vs pattern `inj{A,B}` with C <: A) are re-nested as
    `inj{C,A}(·)` so the binder value is a well-typed A-sorted term."""
    if isinstance(pattern, EVar):
        binds.setdefault(_var_ident(pattern.name), subject)
        return
    if isinstance(pattern, And):
        # alias node (`p #as x` in the K rule, eliminated by klean's
        # elim_aliases at ctor-gen time): match every conjunct against the
        # same subject — heat/cool redex heads are `\and(inj(VarHOLE), _Gen)`.
        for op in pattern.ops:
            match_lhs(op, subject, binds, needs)
        return
    if isinstance(pattern, App) and pattern.symbol == "inj" and len(pattern.args) == 1:
        (psub, psup), parg = pattern.sorts, pattern.args[0]
        if (isinstance(parg, EVar) and psub.name in NORMALIZING_SUPERSORTS
                and psup.name == "SortKItem"):
            needs.add(_var_ident(parg.name))
        if isinstance(subject, App) and subject.symbol == "inj" and len(subject.args) == 1:
            ssub, sarg = subject.sorts[0], subject.args[0]
            if ssub.name == psub.name:
                match_lhs(parg, sarg, binds, needs)
            else:
                match_lhs(parg, App("inj", (ssub, psub), (sarg,)), binds, needs)
        return
    if (isinstance(pattern, App) and isinstance(subject, App)
            and pattern.symbol == subject.symbol
            and len(pattern.args) == len(subject.args)):
        for p, s in zip(pattern.args, subject.args):
            match_lhs(p, s, binds, needs)
    # anything else (DV leaves, exotic nodes): nothing to bind below


def step_proof(label: str, arities: dict[str, tuple[int, bool]], rule,
               subject, printer: K2Lean4) -> str:
    """Constructor application for one step: explicit named implicits for
    binders unification cannot solve, then the uniform tactic per hypothesis."""
    ndefs, has_req = arities[label]
    named = ""
    if rule is not None and subject is not None:
        binds: dict = {}
        needs: set = set()
        match_lhs(rule.lhs, subject, binds, needs)
        for ident in sorted(needs):
            if ident in binds:
                val = printer._transform_pattern(binds[ident], concrete=True)
                named += f" ({ident} := {val})"
    args = [f"(by {TACTIC})"] * (ndefs + (1 if has_req else 0))
    return f"Rewrites.{label}" + named + ("".join(f" {a}" for a in args) if args else "")


def tran_fold(steps: list[str]) -> str:
    """Right-nested tran fold of the step proofs."""
    if len(steps) == 1:
        return steps[0]
    return f"Rewrites.tran ({steps[0]})\n    ({tran_fold(steps[1:])})"


def gen_sample(subdir: str, name: str, stem: str, subst, printer: K2Lean4, prove: bool,
               arities, ord2label, rule_by_label) -> None:
    src = (REPO / "programs" / f"{stem}.py").read_text()
    mpy_text = (ROOT / "build/lean/mpy" / f"{stem}.mpy").read_text()
    if subst:
        old, new = subst
        src = src.replace(old, new)
        mpy_text = mpy_text.replace(old, new)
    mpy = ROOT / "build/lean/mpy" / f"{name}.mpy"
    mpy.write_text(mpy_text)

    init_kore, final_kore = krun_kore(mpy, 0), krun_kore(mpy, None)
    init_t = str(printer._transform_pattern(KoreParser(init_kore).pattern(), concrete=True))
    final_t = str(printer._transform_pattern(KoreParser(final_kore).pattern(), concrete=True))

    proof = "sorry"
    n_steps = None
    step_defs = ""
    if prove:
        ordinals = rule_sequence(name, mpy)
        labels = [ord2label[o] for o in ordinals]
        n_steps = len(labels)
        configs = sweep(mpy)
        assert len(configs) == n_steps + 1, f"{len(configs)} configs vs {n_steps} rules"
        kpats = [KoreParser(c).pattern() for c in configs]
        cterms = [str(printer._transform_pattern(p, concrete=True)) for p in kpats]
        parts = []
        for i, ct in enumerate(cterms):
            nm = "init" if i == 0 else ("final" if i == n_steps else f"c{i}")
            if i not in (0, n_steps):
                parts.append(f"def c{i} : SortGeneratedTopCell :=\n  {ct}\n")
        for i, lbl in enumerate(labels):
            a = "init" if i == 0 else f"c{i}"
            b = "final" if i == n_steps - 1 else f"c{i+1}"
            sp = step_proof(lbl, arities, rule_by_label.get(lbl), kpats[i], printer)
            parts.append(f"theorem step_{i} : Rewrites {a} {b} := {sp}\n")
        step_defs = "\n".join(parts)
        proof = tran_fold([f"step_{i}" for i in range(n_steps)])

    lint_opt = "\nset_option linter.unusedSimpArgs false\n" if prove else ""
    # the tran-fold nests one application per step: past ~250 steps the
    # elaborator's default maxRecDepth (512) overflows on the proof term
    rec_opt = f"set_option maxRecDepth {max(2048, 16 * n_steps)} in\n" if n_steps else ""
    body = f"""import KMiniPy.Relations
{lint_opt}
/-! {name}: concrete execution of `{stem}` as a theorem.
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
{'Proof: ' + str(n_steps) + '-step tran-fold of rule applications.' if n_steps else 'Statement-only stage: proof stubbed.'}
-/

namespace {name}

def init : SortGeneratedTopCell :=
  {init_t}

def final : SortGeneratedTopCell :=
  {final_t}

{step_defs}
{rec_opt}theorem trace : Rewrites init final :=
  {proof}

theorem trace_reaches : Reaches init final := Reaches.of_rewrites trace

end {name}
"""
    out = PKG / "KMiniPy" / subdir / f"{name}.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body)
    print(f"[ok] {name}: {'proved, ' + str(n_steps) + ' steps' if prove else 'statement'} "
          f"({len(init_t)}+{len(final_t)} chars of config)")


def main() -> int:
    prove = "--prove" in sys.argv
    only = ([a for a in sys.argv[sys.argv.index("--only") + 1:] if not a.startswith("-")]
            if "--only" in sys.argv else None)
    printer = load_printer()
    arities = ctor_arities(PKG / "KMiniPy" / "Rewrite.lean") if prove else None
    ord2label = ordinal_to_label(HINTS_DEFN) if prove else None
    rule_by_label = ({_rule_name(r): r for r in printer.defn.rewrites}
                     if prove else {})
    for subdir, name, stem, subst in SAMPLES:
        if only is not None and name not in only:
            continue
        gen_sample(subdir, name, stem, subst, printer, prove, arities, ord2label, rule_by_label)
    return 0


if __name__ == "__main__":
    sys.exit(main())
