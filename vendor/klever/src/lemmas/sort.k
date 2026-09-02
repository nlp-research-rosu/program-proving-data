// reference/src/lemmas/sort.k — SORT-LEMMAS
// Facts over the opaque sortVS (semantics/sort.k). The trusted [simplification] facts are
// TRUE of the concrete insertion sort (Lean-dischargeable): length preservation, sortedness,
// permutation-invariance (per-element count), and element preservation (allInt).

requires "../semantics.k"
requires "casts.k"
requires "preconds.k"

module SORT-LEMMAS
  imports MPY
  imports CASTS-LEMMAS
  imports PRECONDS-LEMMAS

  // sort preserves length — lets len()/index-normalization reduce over the opaque sortVS
  rule vsLen(sortVS(VS:ValSeq)) => vsLen(VS) [simplification]

  // sortedness: adjacent elements are ordered (junk-tolerant projection per the idx2 pattern)
  syntax Bool ::= sortedVS(ValSeq) [function, total]
  rule sortedVS(.ValSeq)                => true
  rule sortedVS(vCons(_:Val, .ValSeq)) => true
  rule sortedVS(vCons(X:Val, vCons(Y:Val, R:ValSeq)))
    => projectIntTotal(X) <=Int projectIntTotal(Y) andBool sortedVS(vCons(Y, R))
  rule sortedVS(sortVS(_VS:ValSeq)) => true [simplification]

  // permutation-invariance: per-element multiplicity is preserved
  syntax Int ::= countV(Val, ValSeq) [function, total]
  rule countV(_:Val, .ValSeq) => 0
  rule countV(X:Val, vCons(Y:Val, R:ValSeq)) => #if X ==K Y #then 1 #else 0 #fi +Int countV(X, R)
  rule countV(X:Val, sortVS(VS:ValSeq)) => countV(X, VS) [simplification]

  // element preservation: an all-int list sorts to an all-int list
  rule allInt(sortVS(VS:ValSeq)) => allInt(VS) [simplification]

  // ==== the keyed sort mirrors sortVS's trusted facts ========================
  rule vsLen(sortKeyVS(VS:ValSeq, _:Val)) => vsLen(VS) [simplification]
  rule countV(X:Val, sortKeyVS(VS:ValSeq, _:Val)) => countV(X, VS) [simplification]
  rule vsLen(revVS(VS:ValSeq)) => vsLen(VS) [simplification]
  rule countV(X:Val, revVS(VS:ValSeq)) => countV(X, VS) [simplification]
endmodule
