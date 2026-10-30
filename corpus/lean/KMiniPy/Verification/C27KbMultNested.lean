import KMiniPy.Verification.C27KbMultNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b : Int) claim-family binders

/-! # C27: `kb_mult_nested` — multiplication by nested repeated addition

`spec a b : RLOne (pre a b) (post a b)` derives the one-path reachability
claim of C27: from `init a b` with `1 ≤ a`, the program reaches the terminal
state with `res ↦ a * maxInt(b, 0)` (stated as `max b 0 * a`), `i ↦ 0`,
`j ↦ min b 0`, `a` and `b` unchanged. Mirrors
corpus/k/verification/c27_kb_mult_nested; upstream problem
problems/imp/mult-nested (programs/PROVENANCE.md). Second NESTED-loop mirror;
same architecture as C26 (inner loop as the ∀-quantified execution lemma
`inner_all` by fuel induction on `j.toNat`, two outer loop-head shapes with
the Circularity anchored at `outerCfg4`, one opaque outer continuation with
a `NilStack` residue predicate) with an accumulator `res`:

* `inner_all` adds `max j 0` to `res` while draining `j` to `min j 0`
  (each iteration is `+1` on `res`, `-1` on `j`; the fuel step patches the
  accumulator slot by `(res + 1) + max (j - 1) 0 = res + max j 0` under
  `0 < j`, `omega` with `max` as an atom).
* The outer invariant carries the product relation
  `res + max b 0 * i = max b 0 * a`; each outer iteration (the composed
  `iter_leg` = `entry4_leg` ⋅ `inner_all` at `j := b` ⋅ `post_inner_leg`)
  re-packs it at `res + max b 0`, `i - 1` by distribute + generalize the
  var*var products + `omega` (core omega treats `max b 0` as an atom but
  rejects distributed var*var).
* Guard false forces `i = 0`, so the relation collapses to
  `res = max b 0 * a` and the composed exit lands on `post`.

Binder discipline as always: helpers at `Int` (definitionally `SortInt`) so
`omega` reads the side conditions, `min`/`max`; the frozen public `spec`
stays at `SortInt`. -/

open RLogic

namespace C27KbMultNested

open C27KbMultNestedLegs

/-- One block-residue frame (shape from the loop legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-! ## The inner loop, summarized as one ∀-quantified execution lemma -/

/-- Fuel-indexed inner drain: from the inner loop head with counter `j` and
accumulator `res` the inner loop rewrites to its exit with
`res ↦ res + max j 0`, `j ↦ min j 0`, the inner continuation `irest`
restored (every inner residue frame drained inside the induction). -/
theorem inner_fuel (k : Nat) : ∀ (a b res i j : Int) (irest : SortK), j.toNat = k →
    Rewrites (innerCfg a b res i j irest)
      (innerExit a b (res + max j 0) i (min j 0) irest) := by
  induction k with
  | zero =>
    intro a b res i j irest hk
    have hj : j ≤ 0 := by omega
    have hacc : res + max j 0 = res := by omega
    have hmin : min j 0 = j := by omega
    rw [hacc, hmin]
    exact inner_exit_leg a b res i j irest hj
  | succ k ih =>
    intro a b res i j irest hk
    have hj : 0 < j := by omega
    have hacc : res + max j 0 = (res + 1) + max (j - 1) 0 := by omega
    have hmin : min j 0 = min (j - 1) 0 := by omega
    rw [hacc, hmin]
    exact ((inner_body_leg a b res i j irest hj).tran
        (ih a b (res + 1) i (j - 1) (nilK irest) (by omega))).tran
      (inner_nil_step a b ((res + 1) + max (j - 1) 0) i (min (j - 1) 0) irest)

/-- The inner loop, whole: the summary lemma the outer derivation applies
each time it walks the outer body (the Lean form of the K record's inner
circularity claim, total in all five variables). -/
theorem inner_all (a b res i j : Int) (irest : SortK) :
    Rewrites (innerCfg a b res i j irest)
      (innerExit a b (res + max j 0) i (min j 0) irest) :=
  inner_fuel j.toNat a b res i j irest rfl

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

/-- One full outer iteration from a later-arrival loop head, as ONE composed
`Rewrites` leg: `entry4_leg` into the inner loop, `inner_all` at bound `b`
(adding `max b 0` to `res`), `post_inner_leg` back to the loop head at
`i - 1`, `j ↦ min b 0`, one more residue frame. -/
theorem iter_leg (a b res i j : Int) (rest : SortK) (h : 0 < i) :
    Rewrites (outerCfg4 a b res i j rest)
      (outerCfg4 a b (res + max b 0) (i - 1) (min b 0) (nilK rest)) :=
  ((entry4_leg a b res i j rest h).tran (inner_all a b res i b (midK rest))).tran
    (post_inner_leg a b (res + max b 0) i (min b 0) rest)

/-- The whole FIRST outer iteration (3-entry-env arrival), from program
start: prologue (binding `res = 0`, `i = a`), `entry3_leg` (binding `j`),
`inner_all`, `post_inner_leg` — the Lean form of the K entry claim's
unfolding of iteration one. The accumulator lands as the literal
`0 + max b 0` (patched into the invariant by the caller). -/
theorem first_iter (a b : Int) (h : 0 < a) :
    Rewrites (init a b)
      (outerCfg4 a b (0 + max b 0) (a - 1) (min b 0) (nilK outerRest0)) :=
  (((prologue_leg a b).tran (entry3_leg a b 0 a outerRest0 h)).tran
      (inner_all a b 0 a b (midK outerRest0))).tran
    (post_inner_leg a b (0 + max b 0) a (min b 0) outerRest0)

/-! ## The claim -/

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `res ↦ max b 0 * a` (the K claim's
`?RES = A *Int maxInt(B, 0)`, omega-equal orientation), `i ↦ 0`,
`j ↦ min b 0`, `a` and `b` unchanged. -/
def post (a b : Int) : Pat := pat (final a b (max b 0 * a) 0 (min b 0))

/-- The ∃-packed outer loop invariant: at a 4-entry-env outer loop head with
`0 ≤ i`, `j` already drained to `min b 0`, the accumulator relation
`res + max b 0 * i = max b 0 * a`, over a residue-stack continuation. -/
def inv (a b : Int) : Pat := fun γ =>
  ∃ (res i j : Int) (rest : SortK),
    γ = outerCfg4 a b res i j rest ∧ NilStack rest ∧ 0 ≤ i ∧ j = min b 0 ∧
      res + max b 0 * i = max b 0 * a

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b : Int) : Type where
  res : Int
  i : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : j = min b 0
  h3 : res + max b 0 * i = max b 0 * a

/-- The invariant instance at one witness. -/
def φIter (a b : Int) (v : Iter a b) : Pat :=
  pat (outerCfg4 a b v.res v.i v.j v.rest)

theorem reshape (a b : Int) : ∀ γ, inv a b γ → ∃ v : Iter a b, φIter a b v γ :=
  fun _γ h => match h with
    | ⟨res, i, j, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨res, i, j, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `iter_leg` (one
composed outer iteration) and re-packs at `res + max b 0`, `i - 1` via the
flushed circularity (Axiom of `A ∪ C`), the product relation re-established
by distribute + generalize + `omega`; guard false forces `i = 0`, the
relation collapses to `res = max b 0 * a`, and the composed exit lands on
`post`. -/
theorem instF (a b : Int) : ∀ v : Iter a b,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b, post a b) ClaimSet.empty) .one
      (φIter a b v, post a b)
  | ⟨res, i, j, rest, hs, h1, h2, h3⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (iter_leg a b res i j rest hlt))
        (.conseq
          (fun _γ hγ => ⟨res + max b 0, i - 1, min b 0, nilK rest, hγ, hs.cons,
            by omega, rfl, by
              simp only [Int.mul_sub, Int.mul_one] at h3 ⊢
              generalize hmi : max b 0 * i = m at h3 ⊢
              generalize hma : max b 0 * a = w at h3 ⊢
              omega⟩)
          (RL.axm' (c := (inv a b, post a b)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b res i j (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          have hres : res = max b 0 * a := by
            subst hi
            simp only [Int.mul_zero] at h3
            generalize hma : max b 0 * a = w at h3 ⊢
            omega
          show _γ = final a b (max b 0 * a) 0 (min b 0)
          rw [hγ, hi, h2, hres])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the whole first outer iteration as an Axiom over `SRew`,
Consequence packing the invariant at `(0 + max b 0, a - 1, min b 0)` over
one residue frame (the entry relation `0 + max b 0 + max b 0 * (a - 1) =
max b 0 * a` by distribute + generalize + `omega`); on `a < 1` the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem toInv (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre a b, inv a b) :=
  if h : 1 ≤ a then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (first_iter a b (by omega)))
      (fun _γ hγ => ⟨0 + max b 0, a - 1, min b 0, nilK outerRest0, hγ,
        .cons .base, by omega, rfl, by
          simp only [Int.mul_sub, Int.mul_one]
          generalize hma : max b 0 * a = w
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

/-- C27. For all integers `a ≥ 1` and `b`, `kb_mult_nested` reaches the
terminal state with `res ↦ max b 0 * a`, `i ↦ 0` and `j ↦ min b 0` — the K
claim's ensures, derived with ONE Circularity (the outer loop) over the
machine-checked legs of `C27KbMultNestedLegs`, the inner loop entering as
the ∀-quantified `inner_all` execution lemma. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) :=
  .trans (toInv a b) (fromInv a b)

end C27KbMultNested
