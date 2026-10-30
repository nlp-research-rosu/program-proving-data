#!/usr/bin/env python3
"""gen_lean_symbolic — emit the verification files C2 and C3-refutation.
C2AbsVal.lean is fixed text (no sweeps): the PROVED reachability-logic
derivation of the abs_val spec over the B1 path legs. C3Refutation.lean
parameterizes a printed ground configuration — the argument literal becomes
a bound `SortInt` variable — around the proved refutation witness. The
PROVED B1AbsVal and B2ClassifyTriangle path theorems and the C1
init/final/legs (C1Legs.lean) are emitted by gen_lean_paths.py instead;
C1SumToN.lean is maintained by hand."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
REPO = ROOT
DEFN = ROOT / "build/lean/minipy-lean"
PKG = ROOT / "corpus/lean/KMiniPy"

sys.path.insert(0, str(REPO / ".venv/lib/python3.12/site-packages"))
from pyk.kore.parser import KoreParser  # noqa: E402
from pyk.kore.internal import KoreDefn  # noqa: E402
from pyk.klean.k2lean4 import K2Lean4  # noqa: E402

printer = K2Lean4(
    KoreDefn.from_definition(KoreParser((DEFN / "definition.kore").read_text()).definition())
    .project_to_rewrites())


def cfg_term(mpy_text: str, depth: int | None) -> str:
    tmp = ROOT / "build/lean/mpy/_sym_tmp.mpy"
    tmp.write_text(mpy_text)
    cmd = ["timeout", "120", "krun", "--definition", str(DEFN), str(tmp), "--output", "kore"]
    if depth is not None:
        cmd += ["--depth", str(depth)]
    p = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return str(printer._transform_pattern(KoreParser(p.stdout.strip()).pattern(), concrete=True))


INT_LIT = "(SortExpr.«Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» {})"


def emit(name: str, body: str) -> None:
    path = PKG / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body)
    print(f"[ok] {name}")


emit("Verification/C2AbsVal.lean", """import KMiniPy.Symbolic.B1AbsVal
import KMiniPy.RL

/-! # C2: functional spec of `abs_val` — reachability-logic derivation

`spec x : RLOne (pre x) (post x)` derives, in the OOPSLA'16 proof system of
`KMiniPy.RL`, the one-path reachability claim of C2: from `init x` — any
integer input, no precondition — the program reaches a final state whose
result `r` satisfies `0 ≤ r ∧ (r = x ∨ r = -x)`. Per the statement taxonomy
(verification claims are reachability claims), the former
`∃ r, Rewrites …` statement is retired: the K `?`-variable `r` is
existential INSIDE the right pattern (`post`), exactly adaptation 1 of the
`RL` encoding, and `Rewrites` enters only through the B1 legs.

The derivation is the calculus form of "C2 follows from B1's path
analysis", showcasing **Case Analysis**: **Consequence** splits `pre` by
the sign of `x`; each disjunct enters the corresponding machine-checked
symbolic path of `B1AbsVal` (`path_neg`/`path_nonneg`) as an **Axiom** over
`SRew`, and **Consequence** packs the existential witness (`0 - x` resp.
`x`) with its arithmetic side conditions. Each branch lemma is total in
`x`: on its infeasible side the left pattern is empty, and **Reflexivity**
closes it vacuously — legal, since the circularity set is `∅` throughout
(`abs_val` is loop-free; no Circularity anywhere in C2).

Integer binders below are `Int` (definitionally `SortInt`, an `abbrev`) so
the arithmetic side conditions elaborate at `Int` and `omega` can read
them, as in C1; all B1 lemmas accept the arguments unchanged. -/

open RLogic

namespace C2AbsVal

/-- Precondition: at program start. The spec is total — no constraint. -/
def pre (x : Int) : Pat := pat (B1AbsVal.init x)

/-- Postcondition: terminated with an integer result `r` that is
non-negative and equals `x` or `-x` (the K `?`-variable, existential inside
the pattern). -/
def post (x : Int) : Pat := fun γ =>
  ∃ r : Int, γ = B1AbsVal.final (iV r) ∧ 0 ≤ r ∧ (r = x ∨ r = -x)

/-- Negative branch, total in `x`: for `x < 0`, B1's negative path (Axiom
over `SRew`) lands on `r = 0 - x`; otherwise the branch pattern is empty
and Reflexivity closes it vacuously. -/
theorem negBranch (x : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre x γ ∧ x < 0, post x) :=
  if h : x < 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (B1AbsVal.path_neg x h))
      (fun _γ hγ => ⟨0 - x, hγ, by omega, Or.inr (by omega)⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Non-negative branch, total in `x`: for `0 ≤ x`, B1's non-negative path
lands on `r = x`; vacuous otherwise. -/
theorem nonnegBranch (x : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre x γ ∧ 0 ≤ x, post x) :=
  if h : 0 ≤ x then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (B1AbsVal.path_nonneg x h))
      (fun _γ hγ => ⟨x, hγ, h, Or.inl rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- The guard split: every pre-state satisfies one of the two branch
patterns. -/
theorem split (x : Int) : ∀ γ, pre x γ →
    (pre x γ ∧ x < 0) ∨ (pre x γ ∧ 0 ≤ x) :=
  fun _γ hγ => if h : x < 0 then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C2. For every integer input, `abs_val` reaches a final state whose
result is non-negative and equal to `x` or `-x`: Consequence + Case
Analysis over the two machine-checked B1 paths. -/
theorem spec (x : SortInt) : RLOne (pre x) (post x) :=
  .conseq (split x) (.caseA (negBranch x) (nonnegBranch x)) (fun _ h => h)

end C2AbsVal
""")

buggy_mpy = (ROOT / "build/lean/mpy/buggy_abs.mpy").read_text()
buggy_init = cfg_term(buggy_mpy, 0).replace(INT_LIT.format(31337), "(SortExpr.«Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» x)")

emit("Verification/C3Refutation.lean", f"""import KMiniPy.Verification.C3BuggyAbsAt0

/-! C3: the absolute-value spec is REFUTED for `buggy_abs` (missing x == 0
case): there is an input on which the program terminates with result None —
not an integer at all, so `0 ≤ r ∧ (r = x ∨ r = -x)` cannot hold. Witness:
x = 0, whose full execution is the concrete trace theorem
`C3BuggyAbsAt0.trace`. -/

namespace C3Refutation

def init (x : SortInt) : SortGeneratedTopCell :=
  {buggy_init}

/-- Some input reaches a `None` result (spec-violating terminal state).
Witness: x = 0; `init 0` is definitionally `C3BuggyAbsAt0.init`, and the
46-step concrete trace theorem carries it to the `result ↦ None` state. -/
theorem spec_refuted :
    ∃ x : SortInt, Rewrites (init x) C3BuggyAbsAt0.final :=
  ⟨0, C3BuggyAbsAt0.trace⟩

end C3Refutation
""")
