import KMiniPy.Verification.C26KbPureNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b : Int) claim-family binders

/-! # C26: `kb_pure_nested` — the nested drain: `i` to 0, `j` to `min b 0`

`spec a b : RLOne (pre a b) (post a b)` derives the one-path reachability
claim of C26: from `init a b` with `1 ≤ a`, the program reaches the terminal
state with `i ↦ 0` and `j ↦ min b 0` (the K record's `minInt(B, 0)` ensures),
`a` and `b` unchanged. Mirrors data/k/verification/c26_kb_pure_nested;
upstream problem problems/imp/pure-nested (programs/PROVENANCE.md). This is
the first NESTED-loop mirror; the architecture (docs: nested-design) extends
C12/C13 with:

* **Inner loop as a ∀-quantified execution lemma** — a documented deviation
  from the K record, which uses a second circularity for the inner loop. Here
  `inner_all` proves `innerCfg a b i j irest ⇒ innerExit a b i (min j 0)
  irest` for ALL integers by induction on the fuel `j.toNat`
  (`inner_body_leg` per iteration, `inner_exit_leg` at the bottom, one
  `inner_nil_step` per layer draining the inner residue frames inside the
  induction). This is execution-leg gluing exactly like the NilStack `drain`,
  not a termination argument for the CLAIM: the derived claim is the same
  one-path reachability statement, and a derivation need not be isomorphic to
  kprove's.
* **Two outer loop-head shapes** — at the first outer arrival `j` is not yet
  bound (3-entry env, `outerCfg3`); afterwards it is (`outerCfg4`). The outer
  **Circularity** runs over `outerCfg4` only; `toInv` composes the whole
  FIRST outer iteration at the `Rewrites` level (prologue → `entry3_leg` →
  `inner_all` → `post_inner_leg`), mirroring the K entry claim's unfolding of
  iteration one before the outer circularity anchors. `1 ≤ a` guarantees the
  guard is true at first arrival, so the run reaches the 4-entry shape.
* **One opaque outer continuation** — the invariant carries `rest : SortK`
  with a `NilStack` predicate as in C12; the inner configurations sit over
  the CONCRETE mid-continuation `midK rest` (the outer body's tail), so the
  guard-true branch of the circularity body is ONE composed `Rewrites` leg
  `iter_leg` = `entry4_leg` ⋅ `inner_all` ⋅ `post_inner_leg`.

The invariant pins `j = min b 0` (established by every completed outer
iteration) and `0 ≤ i`; guard false forces `i = 0` and the composed exit
(`exit_leg`, NilStack drain, `epilogue_leg`) lands on `final a b 0 (min b 0)`.
Binder discipline as always: helpers at `Int` (definitionally `SortInt`) so
`omega` reads the side conditions and `min`; the frozen public `spec` stays
at `SortInt`. -/

open RLogic

namespace C26KbPureNested

open C26KbPureNestedLegs

/-- One block-residue frame (shape from the loop legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-! ## The inner loop, summarized as one ∀-quantified execution lemma -/

/-- Fuel-indexed inner drain: from the inner loop head with counter `j` the
inner loop rewrites to its exit with `j ↦ min j 0`, the inner continuation
`irest` restored (every inner residue frame drained inside the induction). -/
theorem inner_fuel (k : Nat) : ∀ (a b i j : Int) (irest : SortK), j.toNat = k →
    Rewrites (innerCfg a b i j irest) (innerExit a b i (min j 0) irest) := by
  induction k with
  | zero =>
    intro a b i j irest hk
    have hj : j ≤ 0 := by omega
    have hmin : min j 0 = j := by omega
    rw [hmin]
    exact inner_exit_leg a b i j irest hj
  | succ k ih =>
    intro a b i j irest hk
    have hj : 0 < j := by omega
    have hmin : min j 0 = min (j - 1) 0 := by omega
    rw [hmin]
    exact ((inner_body_leg a b i j irest hj).tran
        (ih a b i (j - 1) (nilK irest) (by omega))).tran
      (inner_nil_step a b i (min (j - 1) 0) irest)

/-- The inner loop, whole: the summary lemma the outer derivation applies
each time it walks the outer body (the Lean form of the K record's inner
circularity claim, total in all four variables). -/
theorem inner_all (a b i j : Int) (irest : SortK) :
    Rewrites (innerCfg a b i j irest) (innerExit a b i (min j 0) irest) :=
  inner_fuel j.toNat a b i j irest rfl

/-! ## Outer loop-head continuations and the composed legs -/

/-- Continuations reachable below the outer While: the ground entry
continuation under one `nilK` residue frame per completed outer iteration. -/
inductive NilStack : SortK → Prop
  | base : NilStack outerRest0
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the outer residue frames after loop exit, one `nil_step` per layer. -/
theorem drain (a b i j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (outerExit a b i j rest) (outerExit a b i j outerRest0) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b i j _) ih)

/-- Composed exit path from any invariant-shaped outer loop-head state with
the guard false: exit, drain, epilogue. -/
theorem exit_all (a b i j : Int) {rest : SortK} (h : i ≤ 0)
    (hs : NilStack rest) : Rewrites (outerCfg4 a b i j rest) (final a b i j) :=
  (trans_multi (exit_leg a b i j rest h) (drain a b i j hs)).tran
    (epilogue_leg a b i j)

/-- One full outer iteration from a later-arrival loop head, as ONE composed
`Rewrites` leg: `entry4_leg` into the inner loop, `inner_all` at bound `b`,
`post_inner_leg` back to the loop head at `i - 1`, `j ↦ min b 0`, one more
residue frame. -/
theorem iter_leg (a b i j : Int) (rest : SortK) (h : 0 < i) :
    Rewrites (outerCfg4 a b i j rest)
      (outerCfg4 a b (i - 1) (min b 0) (nilK rest)) :=
  ((entry4_leg a b i j rest h).tran (inner_all a b i b (midK rest))).tran
    (post_inner_leg a b i (min b 0) rest)

/-- The whole FIRST outer iteration (3-entry-env arrival), from program
start: prologue, `entry3_leg` (binding `j`), `inner_all`, `post_inner_leg` —
the Lean form of the K entry claim's unfolding of iteration one. -/
theorem first_iter (a b : Int) (h : 0 < a) :
    Rewrites (init a b) (outerCfg4 a b (a - 1) (min b 0) (nilK outerRest0)) :=
  (((prologue_leg a b).tran (entry3_leg a b a outerRest0 h)).tran
      (inner_all a b a b (midK outerRest0))).tran
    (post_inner_leg a b a (min b 0) outerRest0)

/-! ## The claim -/

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `i ↦ 0`, `j ↦ min b 0` (the K claim's
`?I2 = 0 ∧ ?J2 = minInt(B, 0)`), `a` and `b` unchanged. -/
def post (a b : Int) : Pat := pat (final a b 0 (min b 0))

/-- The ∃-packed outer loop invariant: at a 4-entry-env outer loop head with
`0 ≤ i`, `j` already drained to `min b 0`, over a residue-stack
continuation. -/
def inv (a b : Int) : Pat := fun γ =>
  ∃ (i j : Int) (rest : SortK),
    γ = outerCfg4 a b i j rest ∧ NilStack rest ∧ 0 ≤ i ∧ j = min b 0

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b : Int) : Type where
  i : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : j = min b 0

def φIter (a b : Int) (v : Iter a b) : Pat := pat (outerCfg4 a b v.i v.j v.rest)

theorem reshape (a b : Int) : ∀ γ, inv a b γ → ∃ v : Iter a b, φIter a b v γ :=
  fun _γ h => match h with
    | ⟨i, j, rest, hγ, hs, h1, h2⟩ => ⟨⟨i, j, rest, hs, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `iter_leg` (one
composed outer iteration) and re-packs at `i - 1` via the flushed circularity
(Axiom of `A ∪ C`); guard false forces `i = 0`, and the composed exit lands
on `post` with `j = min b 0` from the invariant. -/
theorem instF (a b : Int) : ∀ v : Iter a b,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b, post a b) ClaimSet.empty) .one
      (φIter a b v, post a b)
  | ⟨i, j, rest, hs, h1, h2⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (iter_leg a b i j rest hlt))
        (.conseq
          (fun _γ hγ => ⟨i - 1, min b 0, nilK rest, hγ, hs.cons, by omega, rfl⟩)
          (RL.axm' (c := (inv a b, post a b)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b i j (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          show _γ = final a b 0 (min b 0)
          rw [hγ, hi, h2])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the whole first outer iteration as an Axiom over `SRew`,
Consequence packing the invariant at `(a - 1, min b 0)` over one residue
frame; on `a < 1` the left pattern is empty and Reflexivity closes it
vacuously. -/
theorem toInv (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre a b, inv a b) :=
  if h : 1 ≤ a then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (first_iter a b (by omega)))
      (fun _γ hγ => ⟨a - 1, min b 0, nilK outerRest0, hγ, .cons .base, by omega, rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b, post a b) :=
  .circ (.conseq (reshape a b) (.abstr (instF a b)) (fun _ h => h))

/-- C26. For all integers `a ≥ 1` and `b`, `kb_pure_nested` reaches the
terminal state with `i ↦ 0` and `j ↦ min b 0` — the K claim's ensures,
derived with ONE Circularity (the outer loop) over the machine-checked legs
of `C26KbPureNestedLegs`, the inner loop entering as the ∀-quantified
`inner_all` execution lemma. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) :=
  .trans (toInv a b) (fromInv a b)

end C26KbPureNested
