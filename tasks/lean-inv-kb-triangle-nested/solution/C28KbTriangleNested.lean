import KMiniPy.Verification.C28KbTriangleNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n : Int) parameter on the claim family

/-! # C28: `kb_triangle_nested` — the nested triangle count reaches Gauss

`spec n : RLOne (pre n) (post n)` derives the one-path reachability claim of
C28: from `init n` with `1 ≤ n`, the program reaches the terminal state with
`count ↦ (n*(n+1))/2` and `i ↦ 0`, `j ↦ 0`. Mirrors the K record
corpus/k/verification/c28_kb_triangle_nested; upstream problem
problems/imp/triangle-nested (programs/PROVENANCE.md). Nested-loop
architecture exactly as C26 (the master nested template):

* **Inner loop as a ∀-quantified execution lemma** — `inner_all` proves
  `innerCfg n c i j irest ⇒ innerExit n (c + j) i 0 irest` for all `0 ≤ j`
  by induction on the fuel `j.toNat` (`inner_body_leg` per iteration, the
  GROUND-`j` `inner_exit_leg` at the bottom, one `inner_nil_step` per layer
  draining the inner residue frames inside the induction). The inner bound
  is the OUTER `i` (the entry legs land at `innerCfg n c i i _`), so each
  completed inner run adds exactly `i` to the accumulator.
* **Two outer loop-head shapes** — first arrival binds only `n count i`
  (`outerCfg3`); afterwards `j` is bound (`outerCfg4`). The outer
  **Circularity** runs over `outerCfg4` only; `toInv` composes the whole
  FIRST outer iteration at the `Rewrites` level (`prologue_leg` →
  `entry3_leg` → `inner_all` at bound `n` → `post_inner_leg`), guarded by
  the precondition `1 ≤ n` (vacuous Reflexivity on `n < 1`).
* **One opaque outer continuation** — the invariant carries `rest : SortK`
  with a `NilStack` predicate; the guard-true branch of the circularity
  body is ONE composed `Rewrites` leg `iter_leg` = `entry4_leg` ⋅
  `inner_all` ⋅ `post_inner_leg`.

The invariant pins `j = 0` (every completed outer iteration drains the
inner counter) and the descending-triangle relation
`2*count + i*(i+1) = n*(n+1)`; guard false forces `i = 0`, so
`2*count = n*(n+1)` yields the Gauss slot `count = (n*(n+1))/2` (Int `ediv`
by the literal 2, product generalized for `omega` — the C22 idiom).
Binder discipline as always: helpers at `Int` (definitionally `SortInt`),
the frozen public `spec` at `SortInt`. -/

open RLogic

namespace C28KbTriangleNested

open C28KbTriangleNestedLegs

/-- One block-residue frame (shape from the loop legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-! ## The inner loop, summarized as one ∀-quantified execution lemma -/

/-- Fuel-indexed inner drain: from the inner loop head with counter `j ≥ 0`
the inner loop rewrites to its exit with `count` grown by `j` and `j ↦ 0`,
the inner continuation `irest` restored (every inner residue frame drained
inside the induction). -/
theorem inner_fuel (k : Nat) : ∀ (n c i j : Int) (irest : SortK),
    0 ≤ j → j.toNat = k →
    Rewrites (innerCfg n c i j irest) (innerExit n (c + j) i 0 irest) := by
  induction k with
  | zero =>
    intro n c i j irest h0 hk
    have hj : j = 0 := by omega
    subst hj
    rw [Int.add_zero]
    exact inner_exit_leg n c i irest
  | succ k ih =>
    intro n c i j irest h0 hk
    have hj : 0 < j := by omega
    have hsum : c + j = c + 1 + (j - 1) := by omega
    rw [hsum]
    exact ((inner_body_leg n c i j irest hj).tran
        (ih n (c + 1) i (j - 1) (nilK irest) (by omega) (by omega))).tran
      (inner_nil_step n (c + 1 + (j - 1)) i 0 irest)

/-- The inner loop, whole: the summary lemma the outer derivation applies
each time it walks the outer body (the Lean form of the K record's inner
circularity claim, total in `0 ≤ j`). -/
theorem inner_all (n c i j : Int) (irest : SortK) (h : 0 ≤ j) :
    Rewrites (innerCfg n c i j irest) (innerExit n (c + j) i 0 irest) :=
  inner_fuel j.toNat n c i j irest h rfl

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
theorem drain (n c i j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (outerExit n c i j rest) (outerExit n c i j outerRest0) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n c i j _) ih)

/-- Composed exit path from any invariant-shaped outer loop-head state with
the guard false: exit, drain, epilogue. -/
theorem exit_all (n c i j : Int) {rest : SortK} (h : i ≤ 0)
    (hs : NilStack rest) : Rewrites (outerCfg4 n c i j rest) (final n c i j) :=
  (trans_multi (exit_leg n c i j rest h) (drain n c i j hs)).tran
    (epilogue_leg n c i j)

/-- One full outer iteration from a later-arrival loop head, as ONE composed
`Rewrites` leg: `entry4_leg` into the inner loop at bound `i`, `inner_all`
(needs `0 ≤ i`, from the guard), `post_inner_leg` back to the loop head at
`i - 1`, `count` grown by `i`, `j ↦ 0`, one more residue frame. -/
theorem iter_leg (n c i j : Int) (rest : SortK) (h : 0 < i) :
    Rewrites (outerCfg4 n c i j rest)
      (outerCfg4 n (c + i) (i - 1) 0 (nilK rest)) :=
  ((entry4_leg n c i j rest h).tran
      (inner_all n c i i (midK rest) (by omega))).tran
    (post_inner_leg n (c + i) i 0 rest)

/-- The whole FIRST outer iteration (3-entry-env arrival), from program
start: prologue, `entry3_leg` (binding `j := n`), `inner_all` at bound `n`,
`post_inner_leg` — the Lean form of the K entry claim's unfolding of
iteration one. -/
theorem first_iter (n : Int) (h : 0 < n) :
    Rewrites (init n) (outerCfg4 n n (n - 1) 0 (nilK outerRest0)) := by
  have hcomp : Rewrites (init n)
      (outerCfg4 n (0 + n) (n - 1) 0 (nilK outerRest0)) :=
    (((prologue_leg n).tran (entry3_leg n 0 n outerRest0 h)).tran
        (inner_all n 0 n n (midK outerRest0) (by omega))).tran
      (post_inner_leg n (0 + n) n 0 outerRest0)
  rw [Int.zero_add] at hcomp
  exact hcomp

/-! ## The claim -/

/-- Precondition: at program start, with the K claim's `N >=Int 1`. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 1 ≤ n

/-- Postcondition: terminated with the Gauss count `count ↦ (n*(n+1))/2`
and both loop counters drained (`i ↦ 0`, `j ↦ 0`), `n` unchanged. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1)) / 2) 0 0)

/-- The ∃-packed outer loop invariant: at a 4-entry-env outer loop head
with `0 ≤ i`, `j` already drained to `0`, the descending-triangle relation
`2*c + i*(i+1) = n*(n+1)`, over a residue-stack continuation. -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (c i j : Int) (rest : SortK),
    γ = outerCfg4 n c i j rest ∧ NilStack rest ∧ 0 ≤ i ∧ j = 0 ∧
      2*c + i*(i+1) = n*(n+1)

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n : Int) : Type where
  c : Int
  i : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : j = 0
  h3 : 2*c + i*(i+1) = n*(n+1)

def φIter (n : Int) (v : Iter n) : Pat := pat (outerCfg4 n v.c v.i v.j v.rest)

theorem reshape (n : Int) : ∀ γ, inv n γ → ∃ v : Iter n, φIter n v γ :=
  fun _γ h => match h with
    | ⟨c, i, j, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨c, i, j, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `iter_leg` (one
composed outer iteration) and re-packs at `(c + i, i - 1)` via the flushed
circularity (Axiom of `A ∪ C`; distribute, generalize `i*i` and `n*(n+1)`,
`omega`); guard false forces `i = 0`, so `2*c = n*(n+1)` gives the Gauss
slot and the invariant's `j = 0` closes the last slot. -/
theorem instF (n : Int) : ∀ v : Iter n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter n v, post n)
  | ⟨c, i, j, rest, hs, h1, h2, h3⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (iter_leg n c i j rest hlt))
        (.conseq
          (fun _γ hγ =>
            ⟨c + i, i - 1, 0, nilK rest, hγ, hs.cons, by omega, rfl, by
              have e : i - 1 + 1 = i := by omega
              rw [e, Int.mul_add, Int.sub_mul, Int.one_mul]
              rw [Int.mul_add, Int.mul_one] at h3
              revert h3
              generalize i * i = m
              generalize n * (n + 1) = w
              intro h3
              omega⟩)
          (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all n c i j (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          rw [hi] at h3
          have hgauss : c = (n * (n + 1)) / 2 := by
            revert h3
            generalize n * (n + 1) = w
            intro h3
            omega
          show _γ = final n ((n * (n + 1)) / 2) 0 0
          rw [hγ, hi, h2, hgauss])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the whole first outer iteration as an Axiom over `SRew`,
Consequence packing the invariant at `(c, i) = (n, n - 1)` over one residue
frame (`2*n + (n-1)*n = n*(n+1)` by the same distribute-and-generalize
idiom); on `n < 1` the left pattern is empty and Reflexivity closes it
vacuously. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n, inv n) :=
  if h : 1 ≤ n then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (first_iter n (by omega)))
      (fun _γ hγ =>
        ⟨n, n - 1, 0, nilK outerRest0, hγ, .cons .base, by omega, rfl, by
          have e : n - 1 + 1 = n := by omega
          rw [e, Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_one]
          generalize n * n = m
          omega⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n, post n) :=
  .circ (.conseq (reshape n) (.abstr (instF n)) (fun _ h => h))

/-- C28. For every integer `n ≥ 1`, `kb_triangle_nested` reaches the
terminal state with `count ↦ (n*(n+1))/2`, `i ↦ 0`, `j ↦ 0` — the K
claim's ensures, derived with ONE Circularity (the outer loop) over the
machine-checked legs of `C28KbTriangleNestedLegs`, the inner loop entering
as the ∀-quantified `inner_all` execution lemma. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) :=
  .trans (toInv n) (fromInv n)

end C28KbTriangleNested
