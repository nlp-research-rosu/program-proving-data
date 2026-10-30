import KMiniPy.Verification.C31KbNestedWithBranchLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b : Int) claim-family binders

/-! # C31: `kb_nested_with_branch` — the branch-guarded nested count reaches Gauss

`spec a b : RLOne (pre a b) (post a b)` derives the one-path reachability
claim of C31: from `init a b` with `1 ≤ a ∧ 1 ≤ b`, the program reaches the
terminal state with `res ↦ (min a b * (min a b + 1)) / 2` (the Gauss sum of
the ADMITTED outer iterations: the outer body's branch runs the inner loop
only when `i ≤ b`, so `res` collects `min a b + (min a b - 1) + ⋯ + 1`),
`i ↦ 0`, `j ↦ 0`. Mirrors corpus/k/verification/c31_kb_nested_with_branch;
upstream problem problems/imp/nested-with-branch (programs/PROVENANCE.md).
The architecture extends the C26 nested-loop template:

* **Inner loop as a ∀-quantified execution lemma** — `inner_all` is proved by
  induction on the fuel `j.toNat` (one `inner_body_leg` per iteration, the
  GROUND-`j` `inner_exit_leg` at the drained bound `0`, one `inner_nil_step`
  per layer), and ACCUMULATES: `res` grows to `res + j` across the drain.
* **A skipped-prefix lemma** — when `b < a` the first `a - b` outer
  iterations refuse the branch (`skip3_leg`: only `i -= 1`, one residue frame
  each, the env keeping its `j`-unbound 3-shape). `skip_all` composes them by
  a second fuel induction on `(i - b).toNat`, landing at `i = b` under
  `nilKn (i - b).toNat` iterated frames (`NilStack_nilKn` feeds the outer
  NilStack).
* **Two outer loop-head shapes** — `outerCfg3` (before `j` is bound) and
  `outerCfg4` (afterwards); the outer **Circularity** runs over `outerCfg4`
  only, and `toInv` composes the whole run up to the FIRST admitted outer
  iteration at the `Rewrites` level, split on `a ≤ b` (admit at `i = a`)
  vs `b < a` (`skip_all`, then admit at `i = b`) — in both cases arriving at
  `i = min a b - 1` with `res = min a b` and the invariant relation
  `2*res + i*(i+1) = min a b * (min a b + 1)` (the C22 Gauss algebra, with
  `min a b` generalized as an atom for `omega`).

The invariant pins `j = 0` (every completed admitted iteration drains it),
`0 ≤ i < min a b` (which re-admits the branch: `i ≤ b` by `omega` through
`min`), and the Gauss relation; guard false forces `i = 0`, so
`2*res = min a b * (min a b + 1)` yields the division slot. Binder
discipline as always: helpers at `Int` (definitionally `SortInt`), the
frozen public `spec` at `SortInt`. -/

open RLogic

namespace C31KbNestedWithBranch

open C31KbNestedWithBranchLegs

/-- One block-residue frame (shape from the loop legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-! ## The inner loop, summarized as one ∀-quantified execution lemma -/

/-- Fuel-indexed inner drain: from the inner loop head with counter `j ≥ 0`
the inner loop rewrites to its exit with `res ↦ res + j` and `j ↦ 0`, the
inner continuation `irest` restored (every inner residue frame drained
inside the induction). -/
theorem inner_fuel (k : Nat) : ∀ (a b res i j : Int) (irest : SortK),
    0 ≤ j → j.toNat = k →
    Rewrites (innerCfg a b res i j irest) (innerExit a b (res + j) i 0 irest) := by
  induction k with
  | zero =>
    intro a b res i j irest h0 hk
    have hj : j = 0 := by omega
    subst hj
    rw [Int.add_zero]
    exact inner_exit_leg a b res i irest
  | succ k ih =>
    intro a b res i j irest h0 hk
    have hj : 0 < j := by omega
    have hacc : res + j = res + 1 + (j - 1) := by omega
    rw [hacc]
    exact ((inner_body_leg a b res i j irest hj).tran
        (ih a b (res + 1) i (j - 1) (nilK irest) (by omega) (by omega))).tran
      (inner_nil_step a b (res + 1 + (j - 1)) i 0 irest)

/-- The inner loop, whole: the summary lemma the outer derivation applies
each time the branch admits the inner loop (total for `0 ≤ j`, the only
shape reachable here since the bound is the admitted outer counter). -/
theorem inner_all (a b res i j : Int) (irest : SortK) (h : 0 ≤ j) :
    Rewrites (innerCfg a b res i j irest) (innerExit a b (res + j) i 0 irest) :=
  inner_fuel j.toNat a b res i j irest h rfl

/-! ## Outer loop-head continuations and the composed legs -/

/-- Continuations reachable below the outer While: the ground entry
continuation under one `nilK` residue frame per completed outer iteration. -/
inductive NilStack : SortK → Prop
  | base : NilStack outerRest0
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

/-- `k` iterated residue frames (innermost-first recursion, so unfolding is
definitional along `skip_all`'s induction). -/
def nilKn : Nat → SortK → SortK
  | 0, r => r
  | k + 1, r => nilKn k (nilK r)

theorem NilStack_nilKn (k : Nat) {r : SortK} (hs : NilStack r) :
    NilStack (nilKn k r) := by
  induction k generalizing r with
  | zero => exact hs
  | succ k ih => exact ih hs.cons

theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the outer residue frames after loop exit, one `nil_step` per layer. -/
theorem drain (a b res i j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (outerExit a b res i j rest) (outerExit a b res i j outerRest0) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b res i j _) ih)

/-- Composed exit path from any invariant-shaped outer loop-head state with
the guard false: exit, drain, epilogue. -/
theorem exit_all (a b res i j : Int) {rest : SortK} (h : i ≤ 0)
    (hs : NilStack rest) :
    Rewrites (outerCfg4 a b res i j rest) (final a b res i j) :=
  (trans_multi (exit_leg a b res i j rest h) (drain a b res i j hs)).tran
    (epilogue_leg a b res i j)

/-- The skipped prefix, by fuel induction on `(i - b).toNat`: while `b < i`
every outer iteration refuses the branch (`skip3_leg`), so the run falls
from `i` to `b` leaving one residue frame per skip. `1 ≤ b` keeps the outer
guard true throughout (`i > b ≥ 1`). -/
theorem skip_fuel (k : Nat) : ∀ (a b res i : Int) (rest : SortK),
    1 ≤ b → b < i → (i - b).toNat = k →
    Rewrites (outerCfg3 a b res i rest) (outerCfg3 a b res b (nilKn k rest)) := by
  induction k with
  | zero =>
    intro a b res i rest hb hlt hk
    exact absurd hk (by omega)
  | succ k ih =>
    intro a b res i rest hb hlt hk
    have h1 : (0 : Int) < i := by omega
    have step := skip3_leg a b res i rest h1 hlt
    by_cases hbi : b < i - 1
    · exact step.tran (ih a b res (i - 1) (nilK rest) hb hbi (by omega))
    · have hib : i - 1 = b := by omega
      have hk0 : k = 0 := by omega
      subst hk0
      rw [hib] at step
      exact step

/-- The whole skipped prefix as one composed leg. -/
theorem skip_all (a b res i : Int) (rest : SortK) (hb : 1 ≤ b) (hlt : b < i) :
    Rewrites (outerCfg3 a b res i rest)
      (outerCfg3 a b res b (nilKn (i - b).toNat rest)) :=
  skip_fuel (i - b).toNat a b res i rest hb hlt rfl

/-- One full ADMITTED outer iteration from a later-arrival loop head, as ONE
composed `Rewrites` leg: `entry4_leg` (guard and branch true, `j := i`) into
the inner loop, `inner_all` at bound `i`, `post_inner_leg` back to the loop
head at `i - 1`, `res + i`, `j ↦ 0`, one more residue frame. -/
theorem iter_leg (a b res i j : Int) (rest : SortK) (h1 : 0 < i) (h2 : i ≤ b) :
    Rewrites (outerCfg4 a b res i j rest)
      (outerCfg4 a b (res + i) (i - 1) 0 (nilK rest)) :=
  ((entry4_leg a b res i j rest h1 h2).tran
      (inner_all a b res i i (midK rest) (by omega))).tran
    (post_inner_leg a b (res + i) i 0 rest)

/-- The whole FIRST outer iteration when `a ≤ b` (the branch admits at once):
prologue, `entry3_leg` (binding `j`), `inner_all`, `post_inner_leg`. -/
theorem first_iter_le (a b : Int) (ha : 0 < a) (hab : a ≤ b) :
    Rewrites (init a b) (outerCfg4 a b (0 + a) (a - 1) 0 (nilK outerRest0)) :=
  (((prologue_leg a b).tran (entry3_leg a b 0 a outerRest0 ha hab)).tran
      (inner_all a b 0 a a (midK outerRest0) (by omega))).tran
    (post_inner_leg a b (0 + a) a 0 outerRest0)

/-- The run up to the first ADMITTED outer iteration when `b < a`: prologue,
the skipped prefix `skip_all` down to `i = b`, then `entry3_leg` (`b ≤ b`),
`inner_all`, `post_inner_leg` — the residue stack is the skip frames under
one body frame. -/
theorem first_iter_gt (a b : Int) (hb : 1 ≤ b) (hab : b < a) :
    Rewrites (init a b)
      (outerCfg4 a b (0 + b) (b - 1) 0 (nilK (nilKn (a - b).toNat outerRest0))) :=
  ((((prologue_leg a b).tran (skip_all a b 0 a outerRest0 hb hab)).tran
        (entry3_leg a b 0 b (nilKn (a - b).toNat outerRest0)
          (by omega : (0 : Int) < b) (by omega : b ≤ b))).tran
      (inner_all a b 0 b b (midK (nilKn (a - b).toNat outerRest0)) (by omega))).tran
    (post_inner_leg a b (0 + b) b 0 (nilKn (a - b).toNat outerRest0))

/-! ## The claim -/

/-- Precondition: at program start, with the K claim's `A >=Int 1 ∧ B >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a ∧ 1 ≤ b

/-- Postcondition: terminated with the Gauss count of admitted iterations
`res ↦ (min a b * (min a b + 1)) / 2`, `i ↦ 0`, `j ↦ 0`. -/
def post (a b : Int) : Pat := pat (final a b ((min a b * (min a b + 1)) / 2) 0 0)

/-- The ∃-packed outer loop invariant: at a 5-entry-env outer loop head with
`0 ≤ i < min a b` (so the branch re-admits: `i ≤ b`), `j` drained to `0`,
and the Gauss relation on the accumulated `res`, over a residue-stack
continuation. -/
def inv (a b : Int) : Pat := fun γ =>
  ∃ (r i j : Int) (rest : SortK),
    γ = outerCfg4 a b r i j rest ∧ NilStack rest ∧ 0 ≤ i ∧ i < min a b ∧
      j = 0 ∧ 2*r + i*(i+1) = min a b * (min a b + 1)

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b : Int) : Type where
  r : Int
  i : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : i < min a b
  h3 : j = 0
  h4 : 2*r + i*(i+1) = min a b * (min a b + 1)

def φIter (a b : Int) (v : Iter a b) : Pat :=
  pat (outerCfg4 a b v.r v.i v.j v.rest)

theorem reshape (a b : Int) : ∀ γ, inv a b γ → ∃ v : Iter a b, φIter a b v γ :=
  fun _γ h => match h with
    | ⟨r, i, j, rest, hγ, hs, h1, h2, h3, h4⟩ =>
      ⟨⟨r, i, j, rest, hs, h1, h2, h3, h4⟩, hγ⟩

/-- One derivation per invariant instance: guard true re-admits the branch
(`i < min a b ≤ b`), takes `iter_leg` (one composed admitted iteration) and
re-packs at `(r + i, i - 1)` via the flushed circularity (Axiom of `A ∪ C`;
distribute, generalize `i*i` and the `min`-product, `omega`); guard false
forces `i = 0`, so `2*r = min a b * (min a b + 1)` gives the division slot
and the composed exit lands on `post`. -/
theorem instF (a b : Int) : ∀ v : Iter a b,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b, post a b) ClaimSet.empty) .one
      (φIter a b v, post a b)
  | ⟨r, i, j, rest, hs, h1, h2, h3, h4⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (iter_leg a b r i j rest hlt (by omega)))
        (.conseq
          (fun _γ hγ =>
            ⟨r + i, i - 1, 0, nilK rest, hγ, hs.cons, by omega, by omega, rfl, by
              revert h4
              generalize min a b * (min a b + 1) = w
              simp only [Int.mul_add, Int.mul_sub, Int.sub_mul,
                Int.one_mul, Int.mul_one]
              generalize i * i = u
              intro h4
              omega⟩)
          (RL.axm' (c := (inv a b, post a b)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b r i j (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          rw [hi] at h4
          have hgauss : r = min a b * (min a b + 1) / 2 := by
            revert h4
            generalize min a b * (min a b + 1) = w
            intro h4
            omega
          show _γ = final a b (min a b * (min a b + 1) / 2) 0 0
          rw [hγ, hi, h3, ← hgauss])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the whole run up to the first admitted outer iteration as
an Axiom over `SRew`, split on `a ≤ b` (first iteration admits at `i = a`)
vs `b < a` (`skip_all` then admit at `i = b`) — both land on the invariant
at `i = min a b - 1`, `res = min a b`; on `¬(1 ≤ a ∧ 1 ≤ b)` the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem toInv (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre a b, inv a b) :=
  if h : 1 ≤ a ∧ 1 ≤ b then
    if hab : a ≤ b then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (first_iter_le a b (by omega) hab))
        (fun _γ hγ =>
          ⟨0 + a, a - 1, 0, nilK outerRest0, hγ, .cons .base, by omega, by omega,
            rfl, by
              have hm : min a b = a := by omega
              rw [hm]
              simp only [Int.mul_add, Int.mul_sub, Int.sub_mul,
                Int.one_mul, Int.mul_one, Int.zero_add]
              generalize a * a = u
              omega⟩)
    else
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (first_iter_gt a b (by omega) (by omega)))
        (fun _γ hγ =>
          ⟨0 + b, b - 1, 0, nilK (nilKn (a - b).toNat outerRest0), hγ,
            (NilStack_nilKn (a - b).toNat .base).cons, by omega, by omega,
            rfl, by
              have hm : min a b = b := by omega
              rw [hm]
              simp only [Int.mul_add, Int.mul_sub, Int.sub_mul,
                Int.one_mul, Int.mul_one, Int.zero_add]
              generalize b * b = u
              omega⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b, post a b) :=
  .circ (.conseq (reshape a b) (.abstr (instF a b)) (fun _ h => h))

/-- C31. For all integers `a ≥ 1`, `b ≥ 1`, `kb_nested_with_branch` reaches
the terminal state with `res ↦ (min a b * (min a b + 1)) / 2`, `i ↦ 0`,
`j ↦ 0` — the K claim's ensures, derived with ONE Circularity (the outer
loop) over the machine-checked legs of `C31KbNestedWithBranchLegs`, the
inner loop entering as the ∀-quantified `inner_all` execution lemma and the
skipped `b < i` prefix as the `skip_all` fuel composition. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) :=
  .trans (toInv a b) (fromInv a b)

end C31KbNestedWithBranch
