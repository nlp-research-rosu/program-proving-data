// reference/src/semantics/str.k — MPY-STR

module MPY-STR
  imports MPY-CORE
  imports MPY-ITER

  // ==== iteration (the iterator protocol's str case; yields 1-char strings) ==
  rule <k> #iterNext(str(.IntSeq))                 => #iterDone ... </k>
  rule <k> #iterNext(str(iCons(C:Int, R:IntSeq)))
        => #iterYield(str(iCons(C, .IntSeq)), str(R)) ... </k>

  // ==== str literal (ASCII-only) ============================================
  syntax IntSeq ::= strToCodes(String) [function]
  rule <k> Str(S:String) => str(strToCodes(S)) ... </k>
  rule strToCodes("") => .IntSeq
  rule strToCodes(S:String) => iCons(ordChar(substrString(S, 0, 1)), strToCodes(substrString(S, 1, lengthString(S))))
    requires S =/=String "" andBool ordChar(substrString(S, 0, 1)) <Int 128

  // ==== operators: + / == / != / in =========================================
  syntax IntSeq ::= seqConcat(IntSeq, IntSeq) [function, total]
  rule seqConcat(.IntSeq, T:IntSeq)                => T
  rule seqConcat(iCons(I:Int, S:IntSeq), T:IntSeq) => iCons(I, seqConcat(S, T))

  rule applyBin("+",  str(A:IntSeq), str(B:IntSeq)) => str(seqConcat(A, B))
  rule applyCmp("==", str(A:IntSeq), str(B:IntSeq)) => A ==K B
  rule applyCmp("!=", str(A:IntSeq), str(B:IntSeq)) => notBool (A ==K B)

  // substring membership: `P in X` iff the code-seq P occurs contiguously in X
  rule applyCmp("in",     str(P:IntSeq), str(X:IntSeq)) => strContains(P, X)
  rule applyCmp("not in", str(P:IntSeq), str(X:IntSeq)) => notBool strContains(P, X)

  syntax Bool ::= strPrefix(IntSeq, IntSeq) [function, total]
  rule strPrefix(.IntSeq, _:IntSeq)               => true
  rule strPrefix(iCons(_:Int, _:IntSeq), .IntSeq) => false
  rule strPrefix(iCons(A:Int, As:IntSeq), iCons(B:Int, Bs:IntSeq)) => A ==Int B andBool strPrefix(As, Bs)

  syntax Bool ::= strContains(IntSeq, IntSeq) [function, total]
  rule strContains(P:IntSeq, X:IntSeq) => true  requires strPrefix(P, X)
  rule strContains(P:IntSeq, .IntSeq)  => false requires notBool strPrefix(P, .IntSeq)
  rule strContains(P:IntSeq, iCons(C:Int, Xs:IntSeq)) => strContains(P, Xs)
       requires notBool strPrefix(P, iCons(C, Xs))

  // ==== lexicographic order: < / <= / > / >= by code point (= Python str order on the code
  // model). strLt reduces on GROUND code-seqs (krun) but is inert/OPAQUE on symbolic ones
  // (a proof's codesProj(V) is an abstract IntSeq — no constructor rule matches), so a symbolic
  // str `<` stays a trusted opaque term the way sortVS / intFloatDiv do. Additive: fires only on
  // str </<=/>/>= comparisons.
  syntax Bool ::= strLt(IntSeq, IntSeq) [function, total]
  rule strLt(.IntSeq, .IntSeq)                => false
  rule strLt(.IntSeq, iCons(_:Int, _:IntSeq)) => true
  rule strLt(iCons(_:Int, _:IntSeq), .IntSeq) => false
  rule strLt(iCons(A:Int, As:IntSeq), iCons(B:Int, Bs:IntSeq)) => true          requires A  <Int B
  rule strLt(iCons(A:Int, As:IntSeq), iCons(B:Int, Bs:IntSeq)) => false         requires A  >Int B
  rule strLt(iCons(A:Int, As:IntSeq), iCons(B:Int, Bs:IntSeq)) => strLt(As, Bs) requires A ==Int B

  rule applyCmp("<",  str(A:IntSeq), str(B:IntSeq)) => strLt(A, B)
  rule applyCmp(">",  str(A:IntSeq), str(B:IntSeq)) => strLt(B, A)
  rule applyCmp("<=", str(A:IntSeq), str(B:IntSeq)) => notBool strLt(B, A)
  rule applyCmp(">=", str(A:IntSeq), str(B:IntSeq)) => notBool strLt(A, B)
endmodule
