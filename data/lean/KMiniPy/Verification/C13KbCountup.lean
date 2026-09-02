import KMiniPy.Verification.C13KbCountupLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n r : Int) claim-family binders

/-! # C13: `kb_countup` — r climbs to `max n r`, with NO precondition

`spec n r : RLOne (pre n r) (post n r)` derives the one-path reachability
claim of C13: from `init n r` for ARBITRARY integers, the program reaches
the terminal state with `r ↦ max n r` (the K record's `maxInt(N, R)`
ensures) and `n` unchanged. Mirrors data/k/verification/c13_kb_countup;
upstream problem problems/imp/countup (programs/PROVENANCE.md).

The derivation extends the C12 architecture with a top-level **Case
Analysis** on whether the loop runs at all — the piecewise `max` closed
form splits into two linear sides:

* `n ≤ r` (no iterations): the guard is false on arrival, so the whole run
  is one composed `Rewrites` leg (prologue, exit at the ground continuation,
  epilogue) entering as an **Axiom** over `SRew`; `max n r = r` closes the
  slot.
* `r < n` (the loop runs): Transitivity through the ∃-packed invariant
  `inv` — loop value `y ≤ n` with the side condition `r < n` carried as a
  constant conjunct — then **Circularity**: guard true takes `body_leg` and
  re-packs at `y + 1`; guard false forces `y = n` (`n ≤ y` from the guard,
  `y ≤ n` from the invariant), and `max n r = n` closes the slot.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12. -/

open RLogic

namespace C13KbCountup

open C13KbCountupLegs

/-- One block-residue frame (shape from `body_leg`'s RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-- Continuations reachable at the loop head. -/
inductive NilStack : SortK → Prop
  | base : NilStack loopRest
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the residue frames after loop exit, one `nil_step` per layer. -/
theorem drain (n y : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n y rest) (loopExit n y loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n y _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (n y : Int) {rest : SortK} (h : n ≤ y)
    (hs : NilStack rest) : Rewrites (loopCfg n y rest) (final n y) :=
  (trans_multi (exit_leg n y rest h) (drain n y hs)).tran (epilogue_leg n y)

/-! ## The claim -/

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n r : Int) : Pat := pat (init n r)

/-- Postcondition: terminated with `n` unchanged and `r ↦ max n r`. -/
def post (n r : Int) : Pat := pat (final n (max n r))

/-- The ∃-packed loop invariant (loop side, `r < n` carried as a constant
conjunct): at the loop head with value `y ≤ n`. -/
def inv (n r : Int) : Pat := fun γ =>
  ∃ (y : Int) (rest : SortK),
    γ = loopCfg n y rest ∧ NilStack rest ∧ y ≤ n ∧ r < n

/-! ## The loop side: Circularity -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n r : Int) : Type where
  y : Int
  rest : SortK
  hs : NilStack rest
  h1 : y ≤ n
  h2 : r < n

def φIter (n r : Int) (v : Iter n r) : Pat := pat (loopCfg n v.y v.rest)

theorem reshape (n r : Int) : ∀ γ, inv n r γ → ∃ v : Iter n r, φIter n r v γ :=
  fun _γ h => match h with
    | ⟨y, rest, hγ, hs, h1, h2⟩ => ⟨⟨y, rest, hs, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
the flushed circularity (Axiom of `A ∪ C`); guard false exits with `y = n`
forced, and `max n r = n` from the carried `r < n`. -/
theorem instF (n r : Int) : ∀ v : Iter n r,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n r, post n r) ClaimSet.empty) .one
      (φIter n r v, post n r)
  | ⟨y, rest, hs, h1, h2⟩ =>
    if hlt : y < n then
      .trans (RL.rw_leg (body_leg n y rest hlt))
        (.conseq
          (fun _γ hγ => ⟨y + 1, nilK rest, hγ, hs.cons, by omega, h2⟩)
          (RL.axm' (c := (inv n r, post n r)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all n y (by omega) hs))
        (fun _γ hγ => by
          have hy : y = n := by omega
          have hm : max n r = n := by omega
          show _γ = final n (max n r)
          rw [hγ, hy, hm])

/-- `pre ∧ r < n ⇒ inv`: the prologue leg as an Axiom with the side
condition as logical frame, Consequence packing the invariant at `y = r`. -/
theorem toInv (n r : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n r γ ∧ r < n, inv n r) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n r), pat (loopCfg n r loopRest))) (r < n)
      (Or.inl ⟨init n r, loopCfg n r loopRest, prologue_leg n r, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hr⟩ => ⟨r, loopRest, hγ, .base, by omega, hr⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n r : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n r, post n r) :=
  .circ (.conseq (reshape n r) (.abstr (instF n r)) (fun _ h => h))

/-- The loop side of the split. -/
theorem loopSide (n r : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n r γ ∧ r < n, post n r) :=
  .trans (toInv n r) (fromInv n r)

/-! ## The no-loop side: one composed leg -/

/-- `n ≤ r`: the guard is false on arrival — prologue, exit at the ground
continuation, epilogue, all at the `Rewrites` level; `max n r = r`. -/
theorem noloopSide (n r : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n r γ ∧ n ≤ r, post n r) :=
  if h : n ≤ r then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg ((prologue_leg n r).tran (exit_all n r h .base)))
      (fun _γ hγ => by
        have hm : max n r = r := by omega
        show _γ = final n (max n r)
        rw [hγ, hm])
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two sides. -/
theorem split (n r : Int) : ∀ γ, pre n r γ →
    (pre n r γ ∧ r < n) ∨ (pre n r γ ∧ n ≤ r) :=
  fun _γ hγ => if h : r < n then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C13. For all integers `n`, `r`, `kb_countup` reaches the terminal state
with `n` unchanged and `r ↦ max n r` — the K claim's `maxInt(N, R)` ensures,
derived with Case Analysis over loop-runs/no-op plus Circularity. -/
theorem spec (n r : SortInt) : RLOne (pre n r) (post n r) :=
  .conseq (split n r) (.caseA (loopSide n r) (noloopSide n r)) (fun _ h => h)

end C13KbCountup
