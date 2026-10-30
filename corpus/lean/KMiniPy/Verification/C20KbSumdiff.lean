import KMiniPy.Verification.C20KbSumdiffLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b : Int) claim-family binders

/-! # C20: `kb_sumdiff` — `res` climbs to `2 * |a - b|`, with NO precondition

`spec a b : RLOne (pre a b) (post a b)` derives the one-path reachability
claim of C20: from `init a b` for ARBITRARY integers, the program reaches
the terminal state with `t ↦ 0` and `res ↦ 2 * max (a - b) (b - a)` (the
absolute difference, doubled). Mirrors corpus/k/verification/c20_kb_sumdiff.

The program branches before the loop — `t = b - a` if `a < b` else
`t = a - b` — then counts `t` down to 0 adding 2 to `res` each iteration.
The piecewise `max` closed form forces a THREE-way top-level **Case
Analysis** (`a < b` / `b < a` / `a = b`), nested as
`caseA caseLT (caseA caseGT caseEQ)`:

* `a < b`: `prologue_lt_leg` enters the loop at `t = b - a`;
  **Transitivity** through the ∃-packed invariant `inv a b (b - a)` —
  `res + 2*t = 2*(b - a)`, fully linear, plain `omega` — then
  **Circularity**: guard true takes `body_leg` and re-packs at
  `(t - 1, res + 2)`; guard false forces `t = 0`, and
  `max (a - b) (b - a) = b - a` closes the slot.
* `b < a`: symmetric via `prologue_ge_leg` and `inv a b (a - b)` —
  the invariant machinery is shared, parameterized by the branch-computed
  loop count `d` with the side fact `d = max (a - b) (b - a)` carried at
  the meta level.
* `a = b`: the loop never runs — the whole run is one composed `Rewrites`
  leg (prologue via `prologue_ge_leg`, exit at the ground continuation,
  epilogue) entering as an **Axiom** over `SRew`; both `a - b` and the
  `max` collapse to 0.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12/C13. -/

open RLogic

namespace C20KbSumdiff

open C20KbSumdiffLegs

/-! ## The loop-head continuation shape -/

/-- One block-residue frame (shape from `body_leg`'s RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-- Continuations reachable at the loop head. -/
inductive NilStack : SortK → Prop
  | base : NilStack loopRest
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

/-- Glue an execution leg to a possibly-empty continuation. -/
theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the residue frames after loop exit, one `nil_step` per layer. -/
theorem drain (a b t res : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit a b t res rest) (loopExit a b t res loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b t res _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (a b t res : Int) {rest : SortK} (h : t ≤ 0)
    (hs : NilStack rest) : Rewrites (loopCfg a b t res rest) (final a b t res) :=
  (trans_multi (exit_leg a b t res rest h) (drain a b t res hs)).tran
    (epilogue_leg a b t res)

/-! ## The claim -/

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b : Int) : Pat := pat (init a b)

/-- Postcondition: terminated with `a`, `b` unchanged, `t ↦ 0` and
`res ↦ 2 * max (a - b) (b - a)` — twice the absolute difference. -/
def post (a b : Int) : Pat := pat (final a b 0 (2 * max (a - b) (b - a)))

/-- The ∃-packed loop invariant, shared by both loop-running cases and
parameterized by the branch-computed initial loop count `d` (`b - a` or
`a - b`): at the loop head with `0 ≤ u` remaining and the accumulator tied
by `r + 2*u = 2*d` — fully linear, plain `omega` throughout. -/
def inv (a b d : Int) : Pat := fun γ =>
  ∃ (u r : Int) (rest : SortK),
    γ = loopCfg a b u r rest ∧ NilStack rest ∧ 0 ≤ u ∧ r + 2 * u = 2 * d

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b d : Int) : Type where
  u : Int
  r : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ u
  h2 : r + 2 * u = 2 * d

/-- The invariant instance at one witness. -/
def φIter (a b d : Int) (v : Iter a b d) : Pat := pat (loopCfg a b v.u v.r v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (a b d : Int) :
    ∀ γ, inv a b d γ → ∃ v : Iter a b d, φIter a b d v γ :=
  fun _γ h => match h with
    | ⟨u, r, rest, hγ, hs, h1, h2⟩ => ⟨⟨u, r, rest, hs, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
re-packs at `(u - 1, r + 2)` (the flushed circularity as an Axiom of
`A ∪ C`); guard false exits with `u = 0` forced and `r = 2*d = 2*max(…)`
from the side fact `hd`. -/
theorem instF (a b d : Int) (hd : d = max (a - b) (b - a)) : ∀ v : Iter a b d,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b d, post a b) ClaimSet.empty) .one
      (φIter a b d v, post a b)
  | ⟨u, r, rest, hs, h1, h2⟩ =>
    if hlt : 0 < u then
      .trans (RL.rw_leg (body_leg a b u r rest hlt))
        (.conseq
          (fun _γ hγ => ⟨u - 1, r + 2, nilK rest, hγ, hs.cons, by omega, by omega⟩)
          (RL.axm' (c := (inv a b d, post a b)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b u r (by omega) hs))
        (fun _γ hγ => by
          have hu : u = 0 := by omega
          have hr : r = 2 * max (a - b) (b - a) := by omega
          show _γ = final a b 0 (2 * max (a - b) (b - a))
          rw [hγ, hu, hr])

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b d : Int) (hd : d = max (a - b) (b - a)) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b d, post a b) :=
  .circ (.conseq (reshape a b d) (.abstr (instF a b d hd)) (fun _ h => h))

/-! ## Case `a < b`: the `t = b - a` branch runs the loop -/

/-- `pre ∧ a < b ⇒ inv a b (b - a)`: the `<`-branch prologue leg as an
Axiom with the side condition as logical frame, Consequence packing the
invariant at `u = b - a`, `r = 0`. -/
theorem toInvLT (a b : Int) (h : a < b) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ a < b, inv a b (b - a)) :=
  .conseq (fun _ hp => hp)
    (RL.axm (c := (pat (init a b), pat (loopCfg a b (b - a) 0 loopRest))) (a < b)
      (Or.inl ⟨init a b, loopCfg a b (b - a) 0 loopRest, prologue_lt_leg a b h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, _⟩ => ⟨b - a, 0, loopRest, hγ, .base, by omega, by omega⟩)

/-- The `a < b` side of the split. -/
theorem caseLT (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ a < b, post a b) :=
  if h : a < b then
    .trans (toInvLT a b h) (fromInv a b (b - a) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## Case `b < a`: the `t = a - b` branch runs the loop -/

/-- `pre ∧ b < a ⇒ inv a b (a - b)`: the `≥`-branch prologue leg as an
Axiom, Consequence packing the invariant at `u = a - b`, `r = 0`. -/
theorem toInvGT (a b : Int) (h : b < a) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ b < a, inv a b (a - b)) :=
  .conseq (fun _ hp => hp)
    (RL.axm (c := (pat (init a b), pat (loopCfg a b (a - b) 0 loopRest))) (b < a)
      (Or.inl ⟨init a b, loopCfg a b (a - b) 0 loopRest,
        prologue_ge_leg a b (by omega : b ≤ a), rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, _⟩ => ⟨a - b, 0, loopRest, hγ, .base, by omega, by omega⟩)

/-- The `b < a` side of the split. -/
theorem caseGT (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ b < a, post a b) :=
  if h : b < a then
    .trans (toInvGT a b h) (fromInv a b (a - b) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## Case `a = b`: the loop never runs -/

/-- `a = b`: the `≥` branch computes `t = a - b = 0`, so the guard is false
on arrival — prologue, exit at the ground continuation, epilogue, all one
composed leg at the `Rewrites` level; both `a - b` and the `max` are 0. -/
theorem caseEQ (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ a = b, post a b) :=
  if h : a = b then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg ((prologue_ge_leg a b (by omega : b ≤ a)).tran
        (exit_all a b (a - b) 0 (by omega) .base)))
      (fun _γ hγ => by
        have h2 : 2 * max (a - b) (b - a) = 0 := by omega
        have h1 : a - b = 0 := by omega
        show _γ = final a b 0 (2 * max (a - b) (b - a))
        rw [hγ, h2, h1])
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## The derivation -/

/-- Every pre-state satisfies one of the three sides. -/
theorem split (a b : Int) : ∀ γ, pre a b γ →
    (pre a b γ ∧ a < b) ∨ ((pre a b γ ∧ b < a) ∨ (pre a b γ ∧ a = b)) :=
  fun _γ hγ =>
    if h : a < b then Or.inl ⟨hγ, h⟩
    else if h2 : b < a then Or.inr (Or.inl ⟨hγ, h2⟩)
    else Or.inr (Or.inr ⟨hγ, by omega⟩)

/-- C20. For all integers `a`, `b`, `kb_sumdiff` reaches the terminal state
with `a`, `b` unchanged, `t ↦ 0` and `res ↦ 2 * max (a - b) (b - a)` —
twice the absolute difference, derived with three-way Case Analysis over
the branch (`a < b` / `b < a` / `a = b`) plus Circularity on the shared
countdown invariant. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) :=
  .conseq (split a b)
    (.caseA (caseLT a b) (.caseA (caseGT a b) (caseEQ a b)))
    (fun _ h => h)

end C20KbSumdiff
