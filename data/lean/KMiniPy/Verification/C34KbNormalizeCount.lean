import KMiniPy.Verification.C34KbNormalizeCountLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b n : Int) claim-family binders

/-! # C34: `kb_normalize_count` — `res` lands on `|n| * a + b`, with NO precondition

`spec a b n : RLOne (pre a b n) (post a b n)` derives the one-path
reachability claim of C34: from `init a b n` for ARBITRARY integers, the
program reaches the terminal state with `n ↦ 0`, `count ↦ max n (0 - n)`
(the absolute value of the input `n`) and `res ↦ (max n (0 - n)) * a + b`.
Mirrors data/k/verification/c34_kb_normalize_count.

The program first normalizes `n` to `|n|` (the prologue branch replaces
`n` by `0 - n` when `n < 0`), zeroes `count`, then counts `n` down to 0
incrementing `count` each iteration; the epilogue computes
`res = count * a + b`. The piecewise `max` closed form forces a top-level
**Case Analysis** on the sign of `n`; BOTH sides run the shared loop
machinery (the `0 ≤ n` side includes `n = 0`, where the invariant enters
with zero iterations left and exits immediately):

* `n < 0`: `prologue_neg_leg` enters the loop at `(0 - n, 0)`;
  **Transitivity** through the ∃-packed invariant `inv a b (0 - n)` —
  `count + n' = 0 - n`, fully linear, plain `omega` — then **Circularity**.
* `0 ≤ n`: symmetric via `prologue_nonneg_leg` and `inv a b n` — the
  invariant machinery is shared, parameterized by the frozen normalized
  entry value `N0` with the side fact `N0 = max n (0 - n)` carried at the
  meta level.

Inside the circularity: guard true takes `body_leg` and re-packs at
`(v - 1, c + 1)`; guard false forces `v = 0` — the exit/epilogue legs are
GROUND at the drained loop-counter slot, so the γ-equation is rewritten to
the pinned `0` BEFORE entering the composed exit leg — and `c = N0` plus
the side fact close the `res` slot by pure term rewriting (no product
arithmetic: `c * a + b` becomes `(max n (0 - n)) * a + b` under
`c = N0 = max n (0 - n)`).

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12/C13/C20. -/

open RLogic

namespace C34KbNormalizeCount

open C34KbNormalizeCountLegs

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
theorem drain (a b n count : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit a b n count rest) (loopExit a b n count loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b n count _) ih)

/-- Composed exit path from the invariant-shaped loop-head state at the
pinned drained counter (the exit and epilogue legs are ground at `n = 0`,
no guard hypothesis): exit, drain, epilogue. -/
theorem exit_all (a b count : Int) {rest : SortK} (hs : NilStack rest) :
    Rewrites (loopCfg a b 0 count rest) (final a b count (count * a + b)) :=
  (trans_multi (exit_leg a b count rest) (drain a b 0 count hs)).tran
    (epilogue_leg a b count)

/-! ## The claim -/

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b n : Int) : Pat := pat (init a b n)

/-- Postcondition: terminated with `a`, `b` unchanged, `n ↦ 0`,
`count ↦ max n (0 - n)` (= `|n|`) and `res ↦ (max n (0 - n)) * a + b`. -/
def post (a b n : Int) : Pat := pat (final a b (max n (0 - n)) ((max n (0 - n)) * a + b))

/-- The ∃-packed loop invariant, shared by both sign cases and
parameterized by the frozen normalized entry value `N0` (`0 - n` or `n`):
at the loop head with `0 ≤ v` remaining and the counter tied by
`c + v = N0` — fully linear, plain `omega` throughout. -/
def inv (a b N0 : Int) : Pat := fun γ =>
  ∃ (v c : Int) (rest : SortK),
    γ = loopCfg a b v c rest ∧ NilStack rest ∧ 0 ≤ v ∧ c + v = N0

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b N0 : Int) : Type where
  v : Int
  c : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ v
  h2 : c + v = N0

/-- The invariant instance at one witness. -/
def φIter (a b N0 : Int) (w : Iter a b N0) : Pat := pat (loopCfg a b w.v w.c w.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (a b N0 : Int) :
    ∀ γ, inv a b N0 γ → ∃ w : Iter a b N0, φIter a b N0 w γ :=
  fun _γ h => match h with
    | ⟨v, c, rest, hγ, hs, h1, h2⟩ => ⟨⟨v, c, rest, hs, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
re-packs at `(v - 1, c + 1)` (the flushed circularity as an Axiom of
`A ∪ C`); guard false forces `v = 0` — rewritten into the γ-equation FIRST,
since the composed exit leg is ground at the pinned `0` slot — then
`c = N0` and the side fact `hN` close the `res` slot by term rewriting. -/
theorem instF (a b n N0 : Int) (hN : N0 = max n (0 - n)) : ∀ w : Iter a b N0,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b N0, post a b n) ClaimSet.empty) .one
      (φIter a b N0 w, post a b n)
  | ⟨v, c, rest, hs, h1, h2⟩ =>
    if hlt : 0 < v then
      .trans (RL.rw_leg (body_leg a b v c rest hlt))
        (.conseq
          (fun _γ hγ => ⟨v - 1, c + 1, nilK rest, hγ, hs.cons, by omega, by omega⟩)
          (RL.axm' (c := (inv a b N0, post a b n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq
        (fun _γ hγ => by
          have hv : v = 0 := by omega
          have hγ' : _γ = loopCfg a b v c rest := hγ
          show _γ = loopCfg a b 0 c rest
          rw [hγ', hv])
        (RL.rw_leg (exit_all a b c hs))
        (fun _γ hγ => by
          have hc : c = N0 := by omega
          show _γ = final a b (max n (0 - n)) ((max n (0 - n)) * a + b)
          rw [hγ, hc, hN])

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b n N0 : Int) (hN : N0 = max n (0 - n)) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b N0, post a b n) :=
  .circ (.conseq (reshape a b N0) (.abstr (instF a b n N0 hN)) (fun _ h => h))

/-! ## Case `n < 0`: the prologue negates `n` -/

/-- `pre ∧ n < 0 ⇒ inv a b (0 - n)`: the negative-branch prologue leg as an
Axiom with the side condition as logical frame, Consequence packing the
invariant at `v = 0 - n`, `c = 0`. -/
theorem toInvNeg (a b n : Int) (h : n < 0) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ n < 0, inv a b (0 - n)) :=
  .conseq (fun _ hp => hp)
    (RL.axm (c := (pat (init a b n), pat (loopCfg a b (0 - n) 0 loopRest))) (n < 0)
      (Or.inl ⟨init a b n, loopCfg a b (0 - n) 0 loopRest, prologue_neg_leg a b n h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, _⟩ => ⟨0 - n, 0, loopRest, hγ, .base, by omega, by omega⟩)

/-- The `n < 0` side of the split; `0 - n = max n (0 - n)` there. -/
theorem caseNeg (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ n < 0, post a b n) :=
  if h : n < 0 then
    .trans (toInvNeg a b n h) (fromInv a b n (0 - n) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## Case `0 ≤ n`: `n` is already normalized -/

/-- `pre ∧ 0 ≤ n ⇒ inv a b n`: the nonnegative-branch prologue leg as an
Axiom, Consequence packing the invariant at `v = n`, `c = 0`. -/
theorem toInvNonneg (a b n : Int) (h : 0 ≤ n) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ 0 ≤ n, inv a b n) :=
  .conseq (fun _ hp => hp)
    (RL.axm (c := (pat (init a b n), pat (loopCfg a b n 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init a b n, loopCfg a b n 0 loopRest, prologue_nonneg_leg a b n h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, _⟩ => ⟨n, 0, loopRest, hγ, .base, by omega, by omega⟩)

/-- The `0 ≤ n` side of the split; `n = max n (0 - n)` there. -/
theorem caseNonneg (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ 0 ≤ n, post a b n) :=
  if h : 0 ≤ n then
    .trans (toInvNonneg a b n h) (fromInv a b n n (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## The derivation -/

/-- Every pre-state satisfies one of the two sides. -/
theorem split (a b n : Int) : ∀ γ, pre a b n γ →
    (pre a b n γ ∧ n < 0) ∨ (pre a b n γ ∧ 0 ≤ n) :=
  fun _γ hγ => if h : n < 0 then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C34. For all integers `a`, `b`, `n`, `kb_normalize_count` reaches the
terminal state with `a`, `b` unchanged, `n ↦ 0`, `count ↦ max n (0 - n)`
(the absolute value of the input) and `res ↦ (max n (0 - n)) * a + b` —
derived with Case Analysis over the sign of `n` plus Circularity on the
shared countdown invariant parameterized by the normalized entry value. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) :=
  .conseq (split a b n)
    (.caseA (caseNeg a b n) (caseNonneg a b n))
    (fun _ h => h)

end C34KbNormalizeCount
