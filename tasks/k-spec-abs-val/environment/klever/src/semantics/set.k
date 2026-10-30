// reference/src/semantics/set.k — MPY-SET

module MPY-SET
  imports MPY-CORE

  // a set value, carried as its distinct codes in first-seen order (order is irrelevant
  // to membership/cardinality — the two observations sets support here).
  syntax Val ::= setV(IntSeq)

  // membership of a code in the accumulated distinct-code sequence
  syntax Bool ::= codeIn(Int, IntSeq) [function, total]
  rule codeIn(_:Int, .IntSeq)                => false
  rule codeIn(C:Int, iCons(H:Int, T:IntSeq)) => C ==Int H orBool codeIn(C, T)

  // the distinct codes of CS (insert-if-absent fold, first-seen order)
  syntax IntSeq ::= dedupCodes(IntSeq)         [function, total]
                  | dedupFrom(IntSeq, IntSeq)  [function, total]
  rule dedupCodes(CS:IntSeq) => dedupFrom(CS, .IntSeq)
  rule dedupFrom(.IntSeq, ACC:IntSeq) => ACC
  rule dedupFrom(iCons(C:Int, S:IntSeq), ACC:IntSeq) => dedupFrom(S, ACC)
       requires codeIn(C, ACC)
  rule dedupFrom(iCons(C:Int, S:IntSeq), ACC:IntSeq) => dedupFrom(S, snocCode(ACC, C))
       requires notBool codeIn(C, ACC)

  syntax IntSeq ::= snocCode(IntSeq, Int) [function, total]
  rule snocCode(.IntSeq, C:Int)                => iCons(C, .IntSeq)
  rule snocCode(iCons(H:Int, T:IntSeq), C:Int) => iCons(H, snocCode(T, C))

  // ==== set equality: two sets are equal iff mutually subsuming ==============
  // subsetCodes(A, B) — every code of A occurs in B (duplicates in A are harmless).
  syntax Bool ::= subsetCodes(IntSeq, IntSeq) [function, total]
  rule subsetCodes(.IntSeq, _:IntSeq)                => true
  rule subsetCodes(iCons(C:Int, S:IntSeq), B:IntSeq) => codeIn(C, B) andBool subsetCodes(S, B)

  syntax Bool ::= sameSet(IntSeq, IntSeq) [function, total]
  rule sameSet(A:IntSeq, B:IntSeq) => subsetCodes(A, B) andBool subsetCodes(B, A)

  // set == set  (the only comparison sets support here)
  rule applyCmp("==", setV(A:IntSeq), setV(B:IntSeq)) => sameSet(A, B)
endmodule
