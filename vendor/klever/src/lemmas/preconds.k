// reference/src/lemmas/preconds.k — PRECONDS-LEMMAS
// Domain predicates for claims: List[int] / List[bool] preconditions.

requires "../semantics.k"

module PRECONDS-LEMMAS
  imports MPY

  syntax Bool ::= allInt(ValSeq) [function, total]
  rule allInt(.ValSeq)                => true
  rule allInt(vCons(V:Val, R:ValSeq)) => isInt(V) andBool allInt(R)
  // distributes over append (accumulator re-entry in loop invariants)
  rule allInt(valSeqConcat(A:ValSeq, B:ValSeq)) => allInt(A) andBool allInt(B) [simplification]

  syntax Bool ::= allBool(ValSeq) [function, total]
  rule allBool(.ValSeq)                => true
  rule allBool(vCons(V:Val, R:ValSeq)) => isBool(V) andBool allBool(R)

  syntax Bool ::= allStr(ValSeq) [function, total]
  rule allStr(.ValSeq)                => true
  rule allStr(vCons(V:Val, R:ValSeq)) => isStr(V) andBool allStr(R)

  // mixed numeric lists (float-or-int elements)
  syntax Bool ::= allNum(ValSeq) [function, total]
  rule allNum(.ValSeq)                => true
  rule allNum(vCons(V:Val, R:ValSeq)) => (isFloat(V) orBool isInt(V)) andBool allNum(R)
  // split never yields a non-str token
  rule allStr(splitSep(_:IntSeq, _:Int, _:IntSeq)) => true [simplification]
  // the trusted sort is a permutation
  rule allStr(sortVS(VS:ValSeq)) => allStr(VS) [simplification]
  rule allInt(sortVS(VS:ValSeq)) => allInt(VS) [simplification]
endmodule
