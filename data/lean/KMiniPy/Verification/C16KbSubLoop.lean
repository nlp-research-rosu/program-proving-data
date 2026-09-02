import KMiniPy.Verification.C16KbSubLoopLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b : Int) claim-family binders

/-! # C16: `kb_sub_loop` — lockstep decrement drains `b` into `a`, with NO precondition

`spec a b : RLOne (pre a b) (post a b)` derives the one-path reachability
claim of C16: from `init a b` for ARBITRARY integers, the program reaches
the terminal state with `a ↦ a - max b 0` and `b ↦ min b 0` (the K record's
piecewise ensures). Mirrors data/k/verification/c16_kb_sub_loop; upstream
problem problems/imp/sub-loop (programs/PROVENANCE.md).

The derivation extends the C12 architecture with a top-level **Case
Analysis** on whether the loop runs at all — the piecewise `max`/`min`
closed form splits into two linear sides:

* `b ≤ 0` (no iterations): the guard is false on arrival, so the whole run
  is one composed `Rewrites` leg (prologue, exit at the ground continuation,
  epilogue) entering as an **Axiom** over `SRew`; `max b 0 = 0` and
  `min b 0 = b` close the slots.
* `0 < b` (the loop runs): Transitivity through the ∃-packed invariant
  `inv` — loop values `x`, `y` with `0 ≤ y` and the linear relation
  `x - y = a - b`, the side condition `0 < b` carried as a constant
  conjunct — then **Circularity**: guard true takes `body_leg` and re-packs
  at `(x - 1, y - 1)`; guard false forces `y = 0` (`y ≤ 0` from the guard,
  `0 ≤ y` from the invariant), so `x = a - b`, and `max b 0 = b`,
  `min b 0 = 0` close the slots.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12. -/

open RLogic

namespace C16KbSubLoop

open C16KbSubLoopLegs

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
theorem drain (x y : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit x y rest) (loopExit x y loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step x y _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (x y : Int) {rest : SortK} (h : y ≤ 0)
    (hs : NilStack rest) : Rewrites (loopCfg x y rest) (final x y) :=
  (trans_multi (exit_leg x y rest h) (drain x y hs)).tran (epilogue_leg x y)

/-! ## The claim -/

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b : Int) : Pat := pat (init a b)

/-- Postcondition: terminated with `a ↦ a - max b 0` and `b ↦ min b 0`. -/
def post (a b : Int) : Pat := pat (final (a - max b 0) (min b 0))

/-- The ∃-packed loop invariant (loop side, `0 < b` carried as a constant
conjunct): at the loop head with values `x`, `y`, `0 ≤ y`, and the lockstep
relation `x - y = a - b`. -/
def inv (a b : Int) : Pat := fun γ =>
  ∃ (x y : Int) (rest : SortK),
    γ = loopCfg x y rest ∧ NilStack rest ∧ 0 ≤ y ∧ x - y = a - b ∧ 0 < b

/-! ## The loop side: Circularity -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b : Int) : Type where
  x : Int
  y : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ y
  h2 : x - y = a - b
  h3 : 0 < b

def φIter (a b : Int) (v : Iter a b) : Pat := pat (loopCfg v.x v.y v.rest)

theorem reshape (a b : Int) : ∀ γ, inv a b γ → ∃ v : Iter a b, φIter a b v γ :=
  fun _γ h => match h with
    | ⟨x, y, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨x, y, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
the flushed circularity (Axiom of `A ∪ C`), re-packing at `(x - 1, y - 1)`;
guard false exits with `y = 0` forced, so `x = a - b`, and the carried
`0 < b` closes `max b 0 = b`, `min b 0 = 0`. -/
theorem instF (a b : Int) : ∀ v : Iter a b,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b, post a b) ClaimSet.empty) .one
      (φIter a b v, post a b)
  | ⟨x, y, rest, hs, h1, h2, h3⟩ =>
    if hlt : 0 < y then
      .trans (RL.rw_leg (body_leg x y rest hlt))
        (.conseq
          (fun _γ hγ => ⟨x - 1, y - 1, nilK rest, hγ, hs.cons, by omega, by omega, h3⟩)
          (RL.axm' (c := (inv a b, post a b)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all x y (by omega) hs))
        (fun _γ hγ => by
          have hx : x = a - b := by omega
          have hy : y = 0 := by omega
          have hm : max b 0 = b := by omega
          have hn : min b 0 = 0 := by omega
          show _γ = final (a - max b 0) (min b 0)
          rw [hγ, hx, hy, hm, hn])

/-- `pre ∧ 0 < b ⇒ inv`: the prologue leg as an Axiom with the side
condition as logical frame, Consequence packing the invariant at
`(x, y) = (a, b)`. -/
theorem toInv (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ 0 < b, inv a b) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init a b), pat (loopCfg a b loopRest))) (0 < b)
      (Or.inl ⟨init a b, loopCfg a b loopRest, prologue_leg a b, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hb⟩ => ⟨a, b, loopRest, hγ, .base, by omega, by omega, hb⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b, post a b) :=
  .circ (.conseq (reshape a b) (.abstr (instF a b)) (fun _ h => h))

/-- The loop side of the split. -/
theorem loopSide (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ 0 < b, post a b) :=
  .trans (toInv a b) (fromInv a b)

/-! ## The no-loop side: one composed leg -/

/-- `b ≤ 0`: the guard is false on arrival — prologue, exit at the ground
continuation, epilogue, all at the `Rewrites` level; `max b 0 = 0` and
`min b 0 = b`. -/
theorem noloopSide (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b γ ∧ b ≤ 0, post a b) :=
  if h : b ≤ 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg ((prologue_leg a b).tran (exit_all a b h .base)))
      (fun _γ hγ => by
        have hm : max b 0 = 0 := by omega
        have hn : min b 0 = b := by omega
        show _γ = final (a - max b 0) (min b 0)
        rw [hγ, hm, hn, Int.sub_zero])
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two sides. -/
theorem split (a b : Int) : ∀ γ, pre a b γ →
    (pre a b γ ∧ 0 < b) ∨ (pre a b γ ∧ b ≤ 0) :=
  fun _γ hγ => if h : 0 < b then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C16. For all integers `a`, `b`, `kb_sub_loop` reaches the terminal state
with `a ↦ a - max b 0` and `b ↦ min b 0` — the K claim's piecewise ensures,
derived with Case Analysis over loop-runs/no-op plus Circularity. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) :=
  .conseq (split a b) (.caseA (loopSide a b) (noloopSide a b)) (fun _ h => h)

end C16KbSubLoop
