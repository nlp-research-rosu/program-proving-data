// reference/src/lemmas.k — MPY-LEMMAS: the proof-only lemma layer, ASSEMBLED.
//
// Loaded by every proof (questions/*/verification.k requires this file); never read by krun.
// Imported whole so the full re-verify sweep is a global consistency check.
//
// Placement rule: a lemma about symbols declared in semantics/X.k lives in lemmas/X.k; a layer
// declaring its own symbols gets its own file; K-prelude (Int/Bool) facts go in arith.k.
//
// Files:
//   lemmas/casts.k            CASTS-LEMMAS            total casts projectIntTotal/projectBoolTotal + #Ceil + round-trip
//   lemmas/preconds.k         PRECONDS-LEMMAS         domain predicates allInt / allBool
//   lemmas/operators.k        OPERATORS-LEMMAS        applyBin/applyCmp Val->Int cast echo
//   lemmas/list.k             LIST-LEMMAS             valSeqConcat assoc / unit / single-cons
//   lemmas/str.k              STR-LEMMAS              seqConcat assoc / unit
//   lemmas/core.k             CORE-LEMMAS             iCons equality decomposition
//   lemmas/subscript.k        SUBSCRIPT-LEMMAS        valSeqAt element bridges under allInt
//   lemmas/float.k            FLOAT-LEMMAS            projectFloatTotal + allFloat (float bridge infra)
//   lemmas/builtins.k         BUILTINS-LEMMAS         intOf on symbolic int/bool Vals
//   lemmas/arith.k            ARITH-LEMMAS            Int normalization (floored-div collapse)
//   lemmas/sort.k             SORT-LEMMAS             facts over the opaque sortVS
//   lemmas/str-int-decimal.k  STR-INT-DECIMAL-LEMMAS  intOfD decimal-digit carrier bridge

requires "semantics.k"
requires "lemmas/casts.k"
requires "lemmas/preconds.k"
requires "lemmas/operators.k"
requires "lemmas/list.k"
requires "lemmas/str.k"
requires "lemmas/core.k"
requires "lemmas/subscript.k"
requires "lemmas/float.k"
requires "lemmas/builtins.k"
requires "lemmas/arith.k"
requires "lemmas/sort.k"
requires "lemmas/str-int-decimal.k"
requires "lemmas/heap.k"

module MPY-LEMMAS
  imports MPY
  imports CASTS-LEMMAS
  imports PRECONDS-LEMMAS
  imports OPERATORS-LEMMAS
  imports LIST-LEMMAS
  imports STR-LEMMAS
  imports CORE-LEMMAS
  imports SUBSCRIPT-LEMMAS
  imports FLOAT-LEMMAS
  imports BUILTINS-LEMMAS
  imports ARITH-LEMMAS
  imports SORT-LEMMAS
  imports STR-INT-DECIMAL-LEMMAS
  imports HEAP-LEMMAS
endmodule
