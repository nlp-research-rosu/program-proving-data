// reference/src/lemmas/operators.k — OPERATORS-LEMMAS
// Operator cast echoes: Val operands that ARE ints cast to Int so applyBin/applyCmp reduce.

requires "../semantics.k"

module OPERATORS-LEMMAS
  imports MPY

  rule applyBin(OP:String, V:Val, W:Val) => applyBin(OP, {V}:>Int, {W}:>Int)
    requires isInt(V) andBool isInt(W)
    [simplification]

  rule applyCmp(OP:String, V:Val, W:Val) => applyCmp(OP, {V}:>Int, {W}:>Int)
    requires isInt(V) andBool isInt(W)
    [simplification]

  // str + echo: concatenation of symbolic code sequences folds through seqConcat
  rule applyBin("+", str(A:IntSeq), str(B:IntSeq)) => str(seqConcat(A, B)) [simplification]
endmodule
