import KMiniPy.Verification.C29KbSquaresCubicLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n : Int) claim-family binders

/-! # C29: `kb_squares_cubic` — nested sum of squares reaches the cubic closed form

`spec n : RLOne (pre n) (post n)` derives the one-path reachability claim
of C29: from `init n` with `1 ≤ n`, the program reaches the terminal state
with `res ↦ n*(n+1)*(2*n+1)/6` (the square-pyramidal number
`1² + 2² + ⋯ + n²`), `i ↦ 0`, `j ↦ 0`. Mirrors the K record
data/k/verification/c29_kb_squares_cubic; upstream problem
problems/imp/squares-cubic (programs/PROVENANCE.md). Architecture as C26
(the nested master template), with two deltas:

* **Ground-`j` inner exit** — the inner guard `0 < j` leaves `j ↦ 0`
  exactly (no `min`), so `inner_all` carries `0 ≤ j` and its fuel
  induction (`inner_fuel` over `j.toNat`) exits through `inner_exit_leg`
  at the ground counter, draining one inner residue frame per layer.
  The inner body adds the OUTER counter `i` each pass, so the whole
  inner run at bound `j := i` adds `i*i` to `res`.
* **A cubic invariant relation** — the outer invariant carries the
  descending square-pyramidal identity
  `6*res + i*(i+1)*(2*i+1) = n*(n+1)*(2*n+1)`. The back edge is the
  cubic step `cube_step : i*(i+1)*(2*i+1) = (i-1)*i*(2*i-1) + 6*(i*i)`,
  proved by explicit distribution to identically-spelled monomials (no
  `ring` in this package) and closed by `omega` after generalizing the
  square `i*i` and the cube `(i*i)*i`.

Otherwise exactly C26: one opaque outer continuation with a `NilStack`
residue predicate, `toInv` composing the whole FIRST outer iteration at the
`Rewrites` level (prologue → `entry3_leg` → `inner_all` → `post_inner_leg`)
behind a dite whose `n < 1` else-branch is vacuous, ONE outer Circularity
over `outerCfg4`, and at guard false `i = 0` forces `6*res` equal to the
frozen product, whence the `/6` slot by `omega` divisibility. Binder
discipline as always: helpers at `Int` (definitionally `SortInt`), the
frozen public `spec` at `SortInt`. -/

open RLogic

namespace C29KbSquaresCubic

open C29KbSquaresCubicLegs

/-- One block-residue frame (shape from the loop legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-! ## The cubic step identity (the back edge's arithmetic) -/

/-- Square-pyramidal step: what one outer iteration moves from the
"remaining" product to the accumulator. Proved by explicit distribution
(`a1`/`a2` open the compound factors, `b1`/`b2` pull the literal `2` out so
both sides spell every monomial identically), then `generalize` the square
and the cube for `omega`. -/
theorem cube_step (i : Int) :
    i * (i + 1) * (2 * i + 1) = (i - 1) * i * (2 * i - 1) + 6 * (i * i) := by
  have a1 : i * (i + 1) = i * i + i := by rw [Int.mul_add, Int.mul_one]
  have a2 : (i - 1) * i = i * i - i := by rw [Int.sub_mul, Int.one_mul]
  have b1 : i * (2 * i) = 2 * (i * i) := by
    rw [Int.mul_comm i (2 * i), Int.mul_assoc]
  have b2 : i * i * (2 * i) = 2 * (i * i * i) := by
    rw [Int.mul_comm (i * i) (2 * i), Int.mul_assoc, Int.mul_comm i (i * i)]
  rw [a1, a2, Int.add_mul, Int.sub_mul, Int.mul_add (i * i) (2 * i) 1,
    Int.mul_add i (2 * i) 1, Int.mul_sub (i * i) (2 * i) 1,
    Int.mul_sub i (2 * i) 1, Int.mul_one, Int.mul_one, b1, b2]
  generalize i * i = w
  generalize w * i = v
  omega

/-! ## The inner loop, summarized as one ∀-quantified execution lemma -/

/-- Fuel-indexed inner drain: from the inner loop head with counter
`0 ≤ j` the inner loop rewrites to its exit with `res` grown by `i*j` and
`j ↦ 0` (ground), the inner continuation `irest` restored (every inner
residue frame drained inside the induction). -/
theorem inner_fuel (k : Nat) : ∀ (n r i j : Int) (irest : SortK), 0 ≤ j →
    j.toNat = k →
    Rewrites (innerCfg n r i j irest) (innerExit n (r + i * j) i 0 irest) := by
  induction k with
  | zero =>
    intro n r i j irest h0 hk
    have hj : j = 0 := by omega
    subst hj
    rw [Int.mul_zero, Int.add_zero]
    exact inner_exit_leg n r i irest
  | succ k ih =>
    intro n r i j irest h0 hk
    have hj : 0 < j := by omega
    have hacc : r + i * j = r + i + i * (j - 1) := by
      rw [Int.mul_sub, Int.mul_one]
      generalize i * j = w
      omega
    rw [hacc]
    exact ((inner_body_leg n r i j irest hj).tran
        (ih n (r + i) i (j - 1) (nilK irest) (by omega) (by omega))).tran
      (inner_nil_step n (r + i + i * (j - 1)) i 0 irest)

/-- The inner loop, whole: the summary lemma the outer derivation applies
each time it walks the outer body (the Lean form of the K record's inner
circularity claim, total in `0 ≤ j`). -/
theorem inner_all (n r i j : Int) (irest : SortK) (h0 : 0 ≤ j) :
    Rewrites (innerCfg n r i j irest) (innerExit n (r + i * j) i 0 irest) :=
  inner_fuel j.toNat n r i j irest h0 rfl

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
theorem drain (n r i j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (outerExit n r i j rest) (outerExit n r i j outerRest0) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n r i j _) ih)

/-- Composed exit path from any invariant-shaped outer loop-head state with
the guard false: exit, drain, epilogue. -/
theorem exit_all (n r i j : Int) {rest : SortK} (h : i ≤ 0)
    (hs : NilStack rest) : Rewrites (outerCfg4 n r i j rest) (final n r i j) :=
  (trans_multi (exit_leg n r i j rest h) (drain n r i j hs)).tran
    (epilogue_leg n r i j)

/-- One full outer iteration from a later-arrival loop head, as ONE composed
`Rewrites` leg: `entry4_leg` into the inner loop at bound `j := i`,
`inner_all` adding `i*i`, `post_inner_leg` back to the loop head at `i - 1`,
`j ↦ 0`, one more residue frame. -/
theorem iter_leg (n r i j : Int) (rest : SortK) (h : 0 < i) :
    Rewrites (outerCfg4 n r i j rest)
      (outerCfg4 n (r + i * i) (i - 1) 0 (nilK rest)) :=
  ((entry4_leg n r i j rest h).tran
      (inner_all n r i i (midK rest) (by omega))).tran
    (post_inner_leg n (r + i * i) i 0 rest)

/-- The whole FIRST outer iteration (3-entry-env arrival), from program
start: prologue, `entry3_leg` (binding `j`), `inner_all` at bound `n`,
`post_inner_leg` — the Lean form of the K entry claim's unfolding of
iteration one. -/
theorem first_iter (n : Int) (h : 0 < n) :
    Rewrites (init n) (outerCfg4 n (0 + n * n) (n - 1) 0 (nilK outerRest0)) :=
  (((prologue_leg n).tran (entry3_leg n 0 n outerRest0 h)).tran
      (inner_all n 0 n n (midK outerRest0) (by omega))).tran
    (post_inner_leg n (0 + n * n) n 0 outerRest0)

/-! ## The claim -/

/-- Precondition: at program start, with the K claim's `N >=Int 1`. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 1 ≤ n

/-- Postcondition: terminated with `res ↦ n*(n+1)*(2*n+1)/6` (the K claim's
square-pyramidal ensures), both counters at `0`, `n` unchanged. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1) * (2 * n + 1)) / 6) 0 0)

/-- The ∃-packed outer loop invariant: at a 4-entry-env outer loop head with
`0 ≤ i`, `j` drained to ground `0`, the square-pyramidal relation between
the accumulator and the descending counter, over a residue-stack
continuation. -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (r i j : Int) (rest : SortK),
    γ = outerCfg4 n r i j rest ∧ NilStack rest ∧ 0 ≤ i ∧ j = 0 ∧
      6 * r + i * (i + 1) * (2 * i + 1) = n * (n + 1) * (2 * n + 1)

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n : Int) : Type where
  r : Int
  i : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : j = 0
  h3 : 6 * r + i * (i + 1) * (2 * i + 1) = n * (n + 1) * (2 * n + 1)

def φIter (n : Int) (v : Iter n) : Pat := pat (outerCfg4 n v.r v.i v.j v.rest)

theorem reshape (n : Int) : ∀ γ, inv n γ → ∃ v : Iter n, φIter n v γ :=
  fun _γ h => match h with
    | ⟨r, i, j, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨r, i, j, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `iter_leg` (one
composed outer iteration, `res` grown by `i*i`) and re-packs at `i - 1` via
the flushed circularity (Axiom of `A ∪ C`), the relation repaired by
`cube_step`; guard false forces `i = 0`, so the relation freezes
`6*res = n*(n+1)*(2*n+1)` and the composed exit lands on `post` with the
`/6` slot from `omega` divisibility. -/
theorem instF (n : Int) : ∀ v : Iter n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter n v, post n)
  | ⟨r, i, j, rest, hs, h1, h2, h3⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (iter_leg n r i j rest hlt))
        (.conseq
          (fun _γ hγ =>
            ⟨r + i * i, i - 1, 0, nilK rest, hγ, hs.cons, by omega, rfl, by
              have e1 : i - 1 + 1 = i := by omega
              have e2 : 2 * (i - 1) + 1 = 2 * i - 1 := by omega
              rw [e1, e2, Int.mul_add 6 r (i * i)]
              rw [cube_step i] at h3
              revert h3
              generalize (i - 1) * i * (2 * i - 1) = A
              generalize i * i = B
              generalize n * (n + 1) * (2 * n + 1) = C
              intro h3
              omega⟩)
          (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all n r i j (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          have hr : r = n * (n + 1) * (2 * n + 1) / 6 := by
            rw [hi] at h3
            revert h3
            generalize n * (n + 1) * (2 * n + 1) = C
            intro h3
            omega
          show _γ = final n ((n * (n + 1) * (2 * n + 1)) / 6) 0 0
          rw [hγ, hi, h2, hr])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the whole first outer iteration as an Axiom over `SRew`,
Consequence packing the invariant at `(res, i, j) = (0 + n*n, n - 1, 0)`
over one residue frame (the relation is `cube_step` at `n`); on `n < 1` the
left pattern is empty and Reflexivity closes it vacuously. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n, inv n) :=
  if h : 1 ≤ n then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (first_iter n (by omega)))
      (fun _γ hγ =>
        ⟨0 + n * n, n - 1, 0, nilK outerRest0, hγ, .cons .base, by omega, rfl, by
          have e1 : n - 1 + 1 = n := by omega
          have e2 : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
          rw [e1, e2, Int.zero_add, cube_step n]
          generalize (n - 1) * n * (2 * n - 1) = A
          generalize n * n = B
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

/-- C29. For every integer `n ≥ 1`, `kb_squares_cubic` reaches the terminal
state with `res ↦ n*(n+1)*(2*n+1)/6` and both counters at `0` — the K
claim's square-pyramidal ensures, derived with ONE Circularity (the outer
loop) over the machine-checked legs of `C29KbSquaresCubicLegs`, the inner
loop entering as the ∀-quantified `inner_all` execution lemma. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) :=
  .trans (toInv n) (fromInv n)

end C29KbSquaresCubic
