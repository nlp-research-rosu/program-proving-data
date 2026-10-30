import KMiniPy.Verification.C32KbPipelineLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b n : Int) claim-family binders

/-! # C32: `kb_pipeline` — `res` climbs to `|a*b| * n + a`, with precondition `0 ≤ n`

`spec a b n : RLOne (pre a b n) (post a b n)` derives the one-path
reachability claim of C32: from `init a b n` with `0 ≤ n`, the program
reaches the terminal state with `t ↦ max (a*b) (0 - a*b)` (the absolute
value of the product, computed by the prologue branch), `i ↦ n` and
`res ↦ max (a*b) (0 - a*b) * n + a` (the loop accumulates `t` per
iteration, the epilogue adds `a`). Mirrors corpus/k/verification/c32_kb_pipeline.

The prologue computes `t = a*b` and flips its sign if negative, so the
piecewise `max` closed form forces a top-level **Case Analysis** on the
PROLOGUE branch — `a*b < 0` / `0 ≤ a*b` — with both sides converging on
the SAME postcondition:

* `a*b < 0`: `prologue_neg_leg` enters the loop at `t = 0 - a*b`;
* `0 ≤ a*b`: `prologue_nonneg_leg` enters at `t = a*b`.

Each side goes by **Transitivity** through the shared ∃-packed invariant
`inv a b n T`, parameterized by the frozen branch-computed loop constant
`T` (C20's refinement trick) with the side fact `T = max (a*b) (0 - a*b)`
carried as a meta-level theorem binder — only the exit uses it. The
invariant ties the accumulator by `r = T * j` with `0 ≤ j ≤ n`; then
**Circularity**: guard true takes `body_leg` and re-packs at
`(r + T, j + 1)` — the atom-product relation is re-established by
distribute/generalize/omega (C15's recipe); guard false forces `j = n`,
the relation collapses to `r = T*n`, the composed exit path drains the
residue and the epilogue adds `a`, and `hT` closes the `max` slots.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12/C13/C20. -/

open RLogic

namespace C32KbPipeline

open C32KbPipelineLegs

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
theorem drain (a b n t res i : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit a b n t res i rest) (loopExit a b n t res i loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b n t res i _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue (which adds `a` to `res`). -/
theorem exit_all (a b n t res i : Int) {rest : SortK} (h : n ≤ i)
    (hs : NilStack rest) :
    Rewrites (loopCfg a b n t res i rest) (final a b n t (res + a) i) :=
  (trans_multi (exit_leg a b n t res i rest h) (drain a b n t res i hs)).tran
    (epilogue_leg a b n t res i)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (a b n : Int) : Pat := fun γ => γ = init a b n ∧ 0 ≤ n

/-- Postcondition: terminated with `a`, `b`, `n` unchanged,
`t ↦ max (a*b) (0 - a*b)` (= `|a*b|`), `i ↦ n` and
`res ↦ max (a*b) (0 - a*b) * n + a`. -/
def post (a b n : Int) : Pat :=
  pat (final a b n (max (a * b) (0 - a * b))
    ((max (a * b) (0 - a * b)) * n + a) n)

/-- The ∃-packed loop invariant, shared by both prologue branches and
parameterized by the frozen branch-computed loop constant `T` (`0 - a*b`
or `a*b`): at the loop head with counter `0 ≤ j ≤ n` and accumulator
`r = T * j`. -/
def inv (a b n T : Int) : Pat := fun γ =>
  ∃ (r j : Int) (rest : SortK),
    γ = loopCfg a b n T r j rest ∧ NilStack rest ∧ 0 ≤ j ∧ j ≤ n ∧ r = T * j

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b n T : Int) : Type where
  r : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h0 : 0 ≤ j
  h1 : j ≤ n
  h2 : r = T * j

/-- The invariant instance at one witness. -/
def φIter (a b n T : Int) (v : Iter a b n T) : Pat :=
  pat (loopCfg a b n T v.r v.j v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (a b n T : Int) :
    ∀ γ, inv a b n T γ → ∃ v : Iter a b n T, φIter a b n T v γ :=
  fun _γ h => match h with
    | ⟨r, j, rest, hγ, hs, h0, h1, h2⟩ => ⟨⟨r, j, rest, hs, h0, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
re-packs at `(r + T, j + 1)` (the flushed circularity as an Axiom of
`A ∪ C`), the relation re-established by distribute/generalize/omega;
guard false exits with `j = n` forced, the relation collapses to
`r = T*n`, and the side fact `hT` closes the `max` slots. -/
theorem instF (a b n T : Int) (hT : T = max (a * b) (0 - a * b)) :
    ∀ v : Iter a b n T,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b n T, post a b n) ClaimSet.empty) .one
      (φIter a b n T v, post a b n)
  | ⟨r, j, rest, hs, h0, h1, h2⟩ =>
    if hlt : j < n then
      .trans (RL.rw_leg (body_leg a b n T r j rest hlt))
        (.conseq
          (fun _γ hγ => ⟨r + T, j + 1, nilK rest, hγ, hs.cons, by omega, by omega, by
            rw [Int.mul_add, Int.mul_one]
            revert h2
            generalize T * j = w
            intro h2
            omega⟩)
          (RL.axm' (c := (inv a b n T, post a b n))
            (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b n T r j (by omega) hs))
        (fun _γ hγ => by
          have hj : j = n := by omega
          have hr : r = T * n := by rw [h2, hj]
          show _γ = final a b n (max (a * b) (0 - a * b))
            ((max (a * b) (0 - a * b)) * n + a) n
          rw [hγ, hj, hr, hT])

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b n T : Int) (hT : T = max (a * b) (0 - a * b)) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b n T, post a b n) :=
  .circ (.conseq (reshape a b n T) (.abstr (instF a b n T hT)) (fun _ h => h))

/-! ## Case `a*b < 0`: the sign-flip branch enters at `T = 0 - a*b` -/

/-- `pre ∧ a*b < 0 ⇒ inv a b n (0 - a*b)`: the negative-branch prologue leg
as an Axiom with `0 ≤ n` as logical frame, Consequence packing the invariant
at `j = 0`, `r = 0`. -/
theorem toInvNeg (a b n : Int) (h : a * b < 0) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ a * b < 0, inv a b n (0 - a * b)) :=
  .conseq (fun _ hp => ⟨hp.1.1, hp.1.2⟩)
    (RL.axm (c := (pat (init a b n),
        pat (loopCfg a b n (0 - a * b) 0 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init a b n, loopCfg a b n (0 - a * b) 0 0 loopRest,
        prologue_neg_leg a b n h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, hn⟩ => ⟨0, 0, loopRest, hγ, .base, by omega, hn,
          (Int.mul_zero _).symm⟩)

/-- The `a*b < 0` side of the split. -/
theorem negSide (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ a * b < 0, post a b n) :=
  if h : a * b < 0 then
    .trans (toInvNeg a b n h) (fromInv a b n (0 - a * b) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## Case `0 ≤ a*b`: the fall-through branch enters at `T = a*b` -/

/-- `pre ∧ 0 ≤ a*b ⇒ inv a b n (a*b)`: the nonnegative-branch prologue leg
as an Axiom with `0 ≤ n` as logical frame, Consequence packing the invariant
at `j = 0`, `r = 0`. -/
theorem toInvNonneg (a b n : Int) (h : 0 ≤ a * b) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ 0 ≤ a * b, inv a b n (a * b)) :=
  .conseq (fun _ hp => ⟨hp.1.1, hp.1.2⟩)
    (RL.axm (c := (pat (init a b n),
        pat (loopCfg a b n (a * b) 0 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init a b n, loopCfg a b n (a * b) 0 0 loopRest,
        prologue_nonneg_leg a b n h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, hn⟩ => ⟨0, 0, loopRest, hγ, .base, by omega, hn,
          (Int.mul_zero _).symm⟩)

/-- The `0 ≤ a*b` side of the split. -/
theorem nonnegSide (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ 0 ≤ a * b, post a b n) :=
  if h : 0 ≤ a * b then
    .trans (toInvNonneg a b n h) (fromInv a b n (a * b) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## The derivation -/

/-- Every pre-state satisfies one of the two prologue branches. -/
theorem split (a b n : Int) : ∀ γ, pre a b n γ →
    (pre a b n γ ∧ a * b < 0) ∨ (pre a b n γ ∧ 0 ≤ a * b) :=
  fun _γ hγ =>
    if h : a * b < 0 then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C32. For all integers `a`, `b` and every `n ≥ 0`, `kb_pipeline` reaches
the terminal state with `a`, `b`, `n` unchanged, `t ↦ max (a*b) (0 - a*b)`,
`i ↦ n` and `res ↦ max (a*b) (0 - a*b) * n + a` — the K claim's `absInt`
ensures, derived with Case Analysis over the prologue branch plus
Circularity on the shared `T`-parameterized accumulator invariant. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) :=
  .conseq (split a b n)
    (.caseA (negSide a b n) (nonnegSide a b n))
    (fun _ h => h)

end C32KbPipeline
