import Smoke2Lean.Rewrite

/-! Experiment: many-step rewriting, reachability, and execution theorems on
top of the klean-generated `Rewrites` relation, for the counter semantics
  bump:   run(I) => run(I + 1)  requires I < 10
  finish: run(I) => done(I)     requires I >= 10
-/

-- ---------------------------------------------------------------------------
-- Generic closures (what klean does not provide)
-- ---------------------------------------------------------------------------

/-- Reflexive-transitive closure: many-step rewriting `=>*`. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl {a : α} : Star R a a
  | head {a b c : α} : R a b → Star R b c → Star R a c

theorem Star.trans {α} {R : α → α → Prop} {a b c : α} :
    Star R a b → Star R b c → Star R a c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | head h _ ih => exact Star.head h (ih hbc)

theorem Star.single {α} {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
  Star.head h Star.refl

/-- n-step rewriting. -/
inductive StepN {α : Type} (R : α → α → Prop) : Nat → α → α → Prop where
  | zero {a : α} : StepN R 0 a a
  | succ {n : Nat} {a b c : α} : R a b → StepN R n b c → StepN R (n + 1) a c

/-- Divergence: arbitrarily long rewrite sequences exist from `a`. -/
def Diverges {α : Type} (R : α → α → Prop) (a : α) : Prop :=
  ∀ n : Nat, ∃ b, StepN R n a b

/-- Reachability with pre/post-condition semantics: either the start state
diverges, or it rewrites to the target in finitely many steps. On a
deterministic relation this is one-path = all-path reachability. -/
def Reaches {α : Type} (R : α → α → Prop) (a b : α) : Prop :=
  Diverges R a ∨ Star R a b

-- ---------------------------------------------------------------------------
-- Configurations
-- ---------------------------------------------------------------------------

def cfg (s : SortState) : SortGeneratedTopCell :=
  { k := { val := SortK.kseq (Inj.inj s) SortK.dotk },
    generatedCounter := { val := 0 } }

def run' (i : SortInt) : SortGeneratedTopCell := cfg (SortState.«run(_)_SMOKE2_State_Int» i)
def done' (i : SortInt) : SortGeneratedTopCell := cfg (SortState.«done(_)_SMOKE2_State_Int» i)

-- ---------------------------------------------------------------------------
-- A concrete execution trace as a theorem: run 8 =>* done 10
-- ---------------------------------------------------------------------------

theorem step_8_9 : Rewrites (run' 8) (run' 9) :=
  Rewrites.bump rfl rfl (by decide)

theorem step_9_10 : Rewrites (run' 9) (run' 10) :=
  Rewrites.bump rfl rfl (by decide)

theorem step_10_done : Rewrites (run' 10) (done' 10) :=
  Rewrites.finish rfl (by decide)

theorem run8_evaluates : Star Rewrites (run' 8) (done' 10) :=
  Star.head step_8_9 (Star.head step_9_10 (Star.single step_10_done))

theorem run8_reaches : Reaches Rewrites (run' 8) (done' 10) :=
  Or.inr run8_evaluates

-- ---------------------------------------------------------------------------
-- A symbolic theorem: for any i with 8 <= i < 10, run i steps to run (i + 1)
-- ---------------------------------------------------------------------------

theorem step_symbolic (i : SortInt) (h : i < 10) : Rewrites (run' i) (run' (i + 1)) :=
  Rewrites.bump rfl rfl (decide_eq_true h)
