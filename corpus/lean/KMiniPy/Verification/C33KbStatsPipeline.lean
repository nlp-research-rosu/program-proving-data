import KMiniPy.Verification.C33KbStatsPipelineLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a b n : Int) claim-family binders

/-! # C33: `kb_stats_pipeline` — `res` climbs to `(max a b - min a b) * n + min a b`

`spec a b n : RLOne (pre a b n) (post a b n)` derives the one-path
reachability claim of C33: from `init a b n` with PRECONDITION `0 ≤ n`, the
program reaches the terminal state with `m ↦ min a b`, `x ↦ max a b`,
`t ↦ max a b - min a b`, `res ↦ (max a b - min a b) * n + min a b` and
`i ↦ n` (`a`, `b`, `n` unchanged).

The program branches before the loop — `m, x = a, b` if `a ≤ b` else
`m, x = b, a` — then sets `t = x - m`, accumulates `t` for `n` iterations,
and finally adds `m` back. The piecewise `min`/`max` closed form forces a
top-level **Case Analysis** (`a ≤ b` / `b < a`), but both sides end at the
SAME postcondition and share the invariant machinery, parameterized (the
C20 trick) by the frozen branch-computed triple `M`/`X`/`T` with the side
facts `M = min a b`, `X = max a b`, `T = max a b - min a b` carried at the
meta level:

* each side's prologue leg enters as an **Axiom** with the precondition
  `0 ≤ n` as logical frame, Consequence packing the invariant at
  `r = 0`, `j = 0` (`j ≤ n` is exactly the precondition);
* **Circularity** on `inv`: counter `0 ≤ j ≤ n` and accumulator tied by
  `r = T * j` (an atom product — the body re-pack rewrites
  `T * (j + 1) = T * j + T` and closes by `hr`); guard false forces
  `j = n`, and the side facts rewrite `final … M X T (T*n + M) n` into the
  `min`/`max` form of `post`.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12/C13/C20. -/

open RLogic

namespace C33KbStatsPipeline

open C33KbStatsPipelineLegs

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
theorem drain (a b n m x t res i : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit a b n m x t res i rest)
      (loopExit a b n m x t res i loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a b n m x t res i _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue (`res += m`). -/
theorem exit_all (a b n m x t res i : Int) {rest : SortK} (h : n ≤ i)
    (hs : NilStack rest) :
    Rewrites (loopCfg a b n m x t res i rest) (final a b n m x t (res + m) i) :=
  (trans_multi (exit_leg a b n m x t res i rest h)
    (drain a b n m x t res i hs)).tran
    (epilogue_leg a b n m x t res i)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n`. -/
def pre (a b n : Int) : Pat := fun γ => γ = init a b n ∧ 0 ≤ n

/-- Postcondition: terminated with `a`, `b`, `n` unchanged, `m ↦ min a b`,
`x ↦ max a b`, `t ↦ max a b - min a b`,
`res ↦ (max a b - min a b) * n + min a b` and `i ↦ n`. -/
def post (a b n : Int) : Pat :=
  pat (final a b n (min a b) (max a b) (max a b - min a b)
    ((max a b - min a b) * n + min a b) n)

/-- The ∃-packed loop invariant, shared by both branch cases and
parameterized by the frozen branch-computed triple `M`/`X`/`T`: at the loop
head with counter `0 ≤ j ≤ n` and accumulator `r = T * j` (an atom
product — never distributed). -/
def inv (a b n M X T : Int) : Pat := fun γ =>
  ∃ (r j : Int) (rest : SortK),
    γ = loopCfg a b n M X T r j rest ∧ NilStack rest ∧ 0 ≤ j ∧ j ≤ n ∧
      r = T * j

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a b n M X T : Int) : Type where
  r : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h0 : 0 ≤ j
  h1 : j ≤ n
  hr : r = T * j

/-- The invariant instance at one witness. -/
def φIter (a b n M X T : Int) (v : Iter a b n M X T) : Pat :=
  pat (loopCfg a b n M X T v.r v.j v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (a b n M X T : Int) :
    ∀ γ, inv a b n M X T γ → ∃ v : Iter a b n M X T, φIter a b n M X T v γ :=
  fun _γ h => match h with
    | ⟨r, j, rest, hγ, hs, h0, h1, hr⟩ => ⟨⟨r, j, rest, hs, h0, h1, hr⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
re-packs at `(r + T, j + 1)` — the flushed circularity (Axiom of `A ∪ C`);
guard false exits with `j = n` forced, `r = T * n`, and the side facts
`hM`/`hX`/`hT` rewrite the frozen triple into the `min`/`max` slots. -/
theorem instF (a b n M X T : Int) (hM : M = min a b) (hX : X = max a b)
    (hT : T = max a b - min a b) : ∀ v : Iter a b n M X T,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a b n M X T, post a b n) ClaimSet.empty) .one
      (φIter a b n M X T v, post a b n)
  | ⟨r, j, rest, hs, h0, h1, hr⟩ =>
    if hlt : j < n then
      .trans (RL.rw_leg (body_leg a b n M X T r j rest hlt))
        (.conseq
          (fun _γ hγ =>
            ⟨r + T, j + 1, nilK rest, hγ, hs.cons, by omega, by omega, by
              rw [Int.mul_add, Int.mul_one, hr]⟩)
          (RL.axm' (c := (inv a b n M X T, post a b n))
            (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a b n M X T r j (by omega) hs))
        (fun _γ hγ => by
          have hj : j = n := by omega
          rw [hj] at hr
          show _γ = final a b n (min a b) (max a b) (max a b - min a b)
            ((max a b - min a b) * n + min a b) n
          rw [hγ, hj, hr, hM, hX, hT])

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a b n M X T : Int) (hM : M = min a b) (hX : X = max a b)
    (hT : T = max a b - min a b) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a b n M X T, post a b n) :=
  .circ (.conseq (reshape a b n M X T) (.abstr (instF a b n M X T hM hX hT))
    (fun _ h => h))

/-! ## Case `a ≤ b`: the `m, x = a, b` branch -/

/-- `pre ∧ a ≤ b ⇒ inv a b n a b (b - a)`: the `≤`-branch prologue leg as
an Axiom with the precondition `0 ≤ n` as logical frame, Consequence
packing the invariant at `r = 0`, `j = 0`. -/
theorem toInvLE (a b n : Int) (h : a ≤ b) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ a ≤ b, inv a b n a b (b - a)) :=
  .conseq (fun _γ hp => hp.1)
    (RL.axm (c := (pat (init a b n),
        pat (loopCfg a b n a b (b - a) 0 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init a b n, loopCfg a b n a b (b - a) 0 0 loopRest,
        prologue_le_leg a b n h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, hn⟩ =>
        ⟨0, 0, loopRest, hγ, .base, by omega, hn, (Int.mul_zero _).symm⟩)

/-- The `a ≤ b` side of the split. -/
theorem caseLE (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ a ≤ b, post a b n) :=
  if h : a ≤ b then
    .trans (toInvLE a b n h)
      (fromInv a b n a b (b - a) (by omega) (by omega) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## Case `b < a`: the `m, x = b, a` branch -/

/-- `pre ∧ b < a ⇒ inv a b n b a (a - b)`: the `>`-branch prologue leg as
an Axiom, Consequence packing the invariant at `r = 0`, `j = 0`. -/
theorem toInvGT (a b n : Int) (h : b < a) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ b < a, inv a b n b a (a - b)) :=
  .conseq (fun _γ hp => hp.1)
    (RL.axm (c := (pat (init a b n),
        pat (loopCfg a b n b a (a - b) 0 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init a b n, loopCfg a b n b a (a - b) 0 0 loopRest,
        prologue_gt_leg a b n h, rfl⟩))
    (fun _γ hp => match hp with
      | ⟨hγ, hn⟩ =>
        ⟨0, 0, loopRest, hγ, .base, by omega, hn, (Int.mul_zero _).symm⟩)

/-- The `b < a` side of the split. -/
theorem caseGT (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre a b n γ ∧ b < a, post a b n) :=
  if h : b < a then
    .trans (toInvGT a b n h)
      (fromInv a b n b a (a - b) (by omega) (by omega) (by omega))
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-! ## The derivation -/

/-- Every pre-state satisfies one of the two sides. -/
theorem split (a b n : Int) : ∀ γ, pre a b n γ →
    (pre a b n γ ∧ a ≤ b) ∨ (pre a b n γ ∧ b < a) :=
  fun _γ hγ => if h : a ≤ b then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C33. For all integers `a`, `b` and `0 ≤ n`, `kb_stats_pipeline` reaches
the terminal state with `a`, `b`, `n` unchanged, `m ↦ min a b`,
`x ↦ max a b`, `t ↦ max a b - min a b`,
`res ↦ (max a b - min a b) * n + min a b` and `i ↦ n` — derived with
two-way Case Analysis over the branch (`a ≤ b` / `b < a`) plus Circularity
on the shared `M`/`X`/`T`-parameterized accumulator invariant. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) :=
  .conseq (split a b n)
    (.caseA (caseLE a b n) (caseGT a b n))
    (fun _ h => h)

end C33KbStatsPipeline
