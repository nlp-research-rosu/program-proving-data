import Smoke2Lean.Prelude

structure SortGeneratedCounterCell : Type where
  val : SortInt

inductive SortState : Type where
  | «done(_)_SMOKE2_State_Int» (x0 : SortInt) : SortState
  | «run(_)_SMOKE2_State_Int» (x0 : SortInt) : SortState

mutual
  structure SortGeneratedTopCell : Type where
    k : SortKCell
    generatedCounter : SortGeneratedCounterCell

  inductive SortK : Type where
    | dotk : SortK
    | kseq (x0 : SortKItem) (x1 : SortK) : SortK

  structure SortKCell : Type where
    val : SortK

  inductive SortKItem : Type where
    | inj_SortBool (x : SortBool) : SortKItem
    | inj_SortGeneratedCounterCell (x : SortGeneratedCounterCell) : SortKItem
    | inj_SortGeneratedTopCell (x : SortGeneratedTopCell) : SortKItem
    | inj_SortInt (x : SortInt) : SortKItem
    | inj_SortKCell (x : SortKCell) : SortKItem
    | inj_SortState (x : SortState) : SortKItem
end