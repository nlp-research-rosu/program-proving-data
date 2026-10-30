import KMiniPy.Verification.C30KbRowsSumNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b : Int) claim-family binders

/-! # C30: `kb_rows_sum_nested` — `a` rows, each adding `b + (b-1) + … + 1`

`spec a b : RLOne (pre a b) (post a b)` derives the one-path reachability
claim of C30: from `init a b` with `1 ≤ a`, the program reaches the terminal
state with `sum ↦ (max b 0 * (max b 0 + 1)) / 2 * a`, `i ↦ 0` and
`j ↦ min b 0`, `a` and `b` unchanged. The K record's ensures is
`2*sum = a * maxInt(b,0) * (maxInt(b,0)+1)`; the two are equivalent because
`max b 0 * (max b 0 + 1)` is a product of consecutive integers, hence even —
we state the divided orientation because it is the form the derivation
produces textually. Mirrors corpus/k/verification/c30_kb_rows_sum_nested;
upstream problem problems/imp/rows-sum-nested (programs/PROVENANCE.md).

The architecture is C26 (the nested-drain master) with a row-sum
accumulator threaded through:

* **Inner loop as a ∀-quantified execution lemma** — `inner_all` proves
  `innerCfg a b s i j irest ⇒ innerExit a b (s + (max j 0 * (max j 0+1))/2)
  i (min j 0) irest` for ALL integers by induction on the fuel `j.toNat`
  (`inner_body_leg` per iteration adds the DECREASING `j`, the Gauss patch
  `(s + j) + (j-1)*j/2 = s + j*(j+1)/2` re-folds the closed form, one
  `inner_nil_step` per layer drains the inner residue frames inside the
  induction). Execution-leg gluing, not a termination argument for the
  CLAIM.
* **Two outer loop-head shapes** — first arrival with `j` unbound
  (`outerCfg3`, 4-entry env), later arrivals with `j` bound (`outerCfg4`,
  5-entry env). The outer **Circularity** runs over `outerCfg4` only;
  `toInv` composes the whole FIRST outer iteration at the `Rewrites` level
  (prologue → `entry3_leg` → `inner_all` → `post_inner_leg`), guarded by
  the dite on `1 ≤ a` with the vacuous-else Reflexivity branch.
* **Invariant in the divided orientation** — with the per-row increment
  `H := (max b 0 * (max b 0 + 1)) / 2` (the exact term `inner_all` yields at
  `j := b`), the invariant ties `s + H*i = H*a`. Every re-establishment is
  LINEAR in the atoms `H`, `H*i`, `H*a` (generalize, then `omega`) — no
  explicit evenness of `max b 0 * (max b 0 + 1)` is ever needed, unlike the
  doubled `2*s + W*i = W*a` orientation whose repack and exit both consume
  `2 ∣ W`.

The invariant pins `j = min b 0` (established by every completed outer
iteration) and `0 ≤ i`; guard false forces `i = 0`, the relation
degenerates to `s = H*a`, and the composed exit (`exit_leg`, NilStack
drain, `epilogue_leg`) lands on `final a b (H*a) 0 (min b 0)` — the post.
Binder discipline as always: helpers at `Int` (definitionally `SortInt`) so
`omega` reads the side conditions, `min`/`max` and `/2`; the frozen public
`spec` stays at `SortInt`. -/

open RLogic

namespace C30KbRowsSumNested

open C30KbRowsSumNestedLegs

/-- One block-residue frame (shape from the loop legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-! ## The inner loop, summarized as one ∀-quantified execution lemma -/

/-- Fuel-indexed inner drain: from the inner loop head with counter `j` the
inner loop rewrites to its exit with `sum` grown by the row's Gauss closed
form `(max j 0 * (max j 0 + 1)) / 2` and `j ↦ min j 0`, the inner
continuation `irest` restored (every inner residue frame drained inside the
induction). -/
theorem inner_fuel (k : Nat) : ∀ (a b s i j : Int) (irest : SortK), j.toNat = k →
    Rewrites (innerCfg a b s i j irest)
      (innerExit a b (s + (max j 0 * (max j 0 + 1)) / 2) i (min j 0) irest) := by
  induction k with
  | zero =>
    intro a b s i j irest hk
    have hj : j ≤ 0 := by omega
    have hmin : min j 0 = j := by omega
    have hsum : s + (max j 0 * (max j 0 + 1)) / 2 = s := by
      have hmax : max j 0 = 0 := by omega
      rw [hmax]
      omega
    rw [hmin, hsum]
    exact inner_exit_leg a b s i j irest hj
  | succ k ih =>
    intro a b s i j irest hk
    have hj : 0 < j := by omega
    have hmin : min j 0 = min (j - 1) 0 := by omega
    have hsum : s + (max j 0 * (max j 0 + 1)) / 2
        = s + j + (max (j - 1) 0 * (max (j - 1) 0 + 1)) / 2 := by
      have hmax1 : max j 0 = j := by omega
      have hmax2 : max (j - 1) 0 = j - 1 := by omega
      have e : j - 1 + 1 = j := by omega
      rw [hmax1, hmax2, e]
      rw [Int.mul_add, Int.mul_one, Int.sub_mul, Int.one_mul]
      generalize j * j = w
      omega
    rw [hmin, hsum]
    exact ((inner_body_leg a b s i j irest hj).tran
        (ih a b (s + j) i (j - 1) (nilK irest) (by omega))).tran
      (inner_nil_step a b (s + j + (max (j - 1) 0 * (max (j - 1) 0 + 1)) / 2) i
        (min (j - 1) 0) irest)

/-- The inner loop, whole: the summary lemma the outer derivation applies
each time it walks the outer body (the Lean form of the K record's inner
circularity claim, total in all five variables). -/
theorem inner_all (a b s i j : Int) (irest : SortK) :
    Rewrites (innerCfg a b s i j irest)
      (innerExit a b (s + (max j 0 * (max j 0 + 1)) / 2) i (min j 0) irest) :=
  inner_fuel j.toNat a b s i j irest rfl

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
theorem drain (a b s i j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (outerExit a b s i j rest) (outerExit a b s i j outerRest0) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b s i j _) ih)

/-- Composed exit path from any invariant-shaped outer loop-head state with
the guard false: exit, drain, epilogue. -/
theorem exit_all (a b s i j : Int) {rest : SortK} (h : i ≤ 0)
    (hs : NilStack rest) : Rewrites (outerCfg4 a b s i j rest) (final a b s i j) :=
  (trans_multi (exit_leg a b s i j rest h) (drain a b s i j hs)).tran
    (epilogue_leg a b s i j)

/-- One full outer iteration from a later-arrival loop head, as ONE composed
`Rewrites` leg: `entry4_leg` into the inner loop, `inner_all` at bound `b`
(growing `sum` by the row sum `(max b 0 * (max b 0 + 1)) / 2`),
`post_inner_leg` back to the loop head at `i - 1`, `j ↦ min b 0`, one more
residue frame. -/
theorem iter_leg (a b s i j : Int) (rest : SortK) (h : 0 < i) :
    Rewrites (outerCfg4 a b s i j rest)
      (outerCfg4 a b (s + (max b 0 * (max b 0 + 1)) / 2) (i - 1) (min b 0)
        (nilK rest)) :=
  ((entry4_leg a b s i j rest h).tran (inner_all a b s i b (midK rest))).tran
    (post_inner_leg a b (s + (max b 0 * (max b 0 + 1)) / 2) i (min b 0) rest)

/-- The whole FIRST outer iteration (4-entry-env arrival), from program
start: prologue, `entry3_leg` (binding `j`), `inner_all`, `post_inner_leg` —
the Lean form of the K entry claim's unfolding of iteration one. -/
theorem first_iter (a b : Int) (h : 0 < a) :
    Rewrites (init a b)
      (outerCfg4 a b (0 + (max b 0 * (max b 0 + 1)) / 2) (a - 1) (min b 0)
        (nilK outerRest0)) :=
  (((prologue_leg a b).tran (entry3_leg a b 0 a outerRest0 h)).tran
      (inner_all a b 0 a b (midK outerRest0))).tran
    (post_inner_leg a b (0 + (max b 0 * (max b 0 + 1)) / 2) a (min b 0) outerRest0)

/-! ## The claim -/

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `sum ↦ (max b 0 * (max b 0 + 1)) / 2 * a`
(each of the `a` rows contributes the Gauss row sum; equivalent to the K
claim's `2*sum = a * maxInt(b,0) * (maxInt(b,0)+1)` by evenness of the
consecutive product), `i ↦ 0`, `j ↦ min b 0`, `a` and `b` unchanged. -/
def post (a b : Int) : Pat :=
  pat (final a b ((max b 0 * (max b 0 + 1)) / 2 * a) 0 (min b 0))

/-- The ∃-packed outer loop invariant: at a 5-entry-env outer loop head with
`0 ≤ i`, `j` already drained to `min b 0`, the accumulator tied by
`s + H*i = H*a` for the per-row increment `H = (max b 0 * (max b 0+1))/2`
(the exact term `inner_all` adds at `j := b`), over a residue-stack
continuation. -/
def inv (a b : Int) : Pat := fun γ =>
  ∃ (s i j : Int) (rest : SortK),
    γ = outerCfg4 a b s i j rest ∧ NilStack rest ∧ 0 ≤ i ∧ j = min b 0 ∧
      s + (max b 0 * (max b 0 + 1)) / 2 * i = (max b 0 * (max b 0 + 1)) / 2 * a

/-- Re-establish the accumulator relation after one outer iteration: linear
in the atoms once the row sum is generalized (no evenness needed in this
orientation). -/
theorem inv_step (a b s i : Int)
    (h : s + (max b 0 * (max b 0 + 1)) / 2 * i = (max b 0 * (max b 0 + 1)) / 2 * a) :
    s + (max b 0 * (max b 0 + 1)) / 2 + (max b 0 * (max b 0 + 1)) / 2 * (i - 1)
      = (max b 0 * (max b 0 + 1)) / 2 * a := by
  rw [Int.mul_sub, Int.mul_one]
  revert h
  generalize (max b 0 * (max b 0 + 1)) / 2 = w
  generalize w * i = P
  generalize w * a = Q
  intro h
  omega

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b : Int) : Type where
  s : Int
  i : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : j = min b 0
  h3 : s + (max b 0 * (max b 0 + 1)) / 2 * i = (max b 0 * (max b 0 + 1)) / 2 * a

def φIter (a b : Int) (v : Iter a b) : Pat :=
  pat (outerCfg4 a b v.s v.i v.j v.rest)

theorem reshape (a b : Int) : ∀ γ, inv a b γ → ∃ v : Iter a b, φIter a b v γ :=
  fun _γ h => match h with
    | ⟨s, i, j, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨s, i, j, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `iter_leg` (one
composed outer iteration) and re-packs at `(s + H, i - 1)` via the flushed
circularity (Axiom of `A ∪ C`); guard false forces `i = 0`, the relation
degenerates to `s = H*a`, and the composed exit lands on `post` with
`j = min b 0` from the invariant. -/
theorem instF (a b : Int) : ∀ v : Iter a b,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b, post a b) ClaimSet.empty) .one
      (φIter a b v, post a b)
  | ⟨s, i, j, rest, hs, h1, h2, h3⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (iter_leg a b s i j rest hlt))
        (.conseq
          (fun _γ hγ => ⟨s + (max b 0 * (max b 0 + 1)) / 2, i - 1, min b 0,
            nilK rest, hγ, hs.cons, by omega, rfl, inv_step a b s i h3⟩)
          (RL.axm' (c := (inv a b, post a b)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b s i j (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          have hs0 : s = (max b 0 * (max b 0 + 1)) / 2 * a := by
            rw [hi, Int.mul_zero, Int.add_zero] at h3
            exact h3
          show _γ = final a b ((max b 0 * (max b 0 + 1)) / 2 * a) 0 (min b 0)
          rw [hγ, hs0, hi, h2])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the whole first outer iteration as an Axiom over `SRew`,
Consequence packing the invariant at `(0 + H, a - 1, min b 0)` over one
residue frame; on `a < 1` the left pattern is empty and Reflexivity closes
it vacuously. -/
theorem toInv (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre a b, inv a b) :=
  if h : 1 ≤ a then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (first_iter a b (by omega)))
      (fun _γ hγ => ⟨0 + (max b 0 * (max b 0 + 1)) / 2, a - 1, min b 0,
        nilK outerRest0, hγ, .cons .base, by omega, rfl,
        inv_step a b 0 a (by generalize (max b 0 * (max b 0 + 1)) / 2 * a = q; omega)⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b, post a b) :=
  .circ (.conseq (reshape a b) (.abstr (instF a b)) (fun _ h => h))

/-- C30. For all integers `a ≥ 1` and `b`, `kb_rows_sum_nested` reaches the
terminal state with `sum ↦ (max b 0 * (max b 0 + 1)) / 2 * a`, `i ↦ 0` and
`j ↦ min b 0` — the K claim's ensures (divided orientation), derived with
ONE Circularity (the outer loop) over the machine-checked legs of
`C30KbRowsSumNestedLegs`, the inner loop entering as the ∀-quantified
`inner_all` execution lemma. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) :=
  .trans (toInv a b) (fromInv a b)

end C30KbRowsSumNested
