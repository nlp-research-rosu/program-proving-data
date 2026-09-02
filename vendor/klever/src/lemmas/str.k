// reference/src/lemmas/str.k — STR-LEMMAS
// Facts over seqConcat (semantics/str.k): loops fold result = result + piece left-to-right.

requires "../semantics.k"

module STR-LEMMAS
  imports MPY

  rule seqConcat(seqConcat(A:IntSeq, B:IntSeq), C:IntSeq) => seqConcat(A, seqConcat(B, C)) [simplification]
  rule seqConcat(S:IntSeq, .IntSeq) => S [simplification]

  // length is additive over concatenation, and never negative
  rule isLen(seqConcat(A:IntSeq, B:IntSeq)) => isLen(A) +Int isLen(B) [simplification]
  rule isLen(_:IntSeq) >=Int 0 => true [simplification]
  rule 0 <=Int isLen(_:IntSeq) => true [simplification]
  rule isLen(_:IntSeq) <Int 0 => false [simplification]
  // the shifted spellings a concrete prefix leaves behind (isLen unfolds over
  // iCons heads, so bounds land as C1 <= isLen(tail) + C2)
  rule C1:Int <=Int isLen(_:IntSeq) +Int C2:Int => true
    requires C1 <=Int C2 [simplification]
  rule C1:Int <Int isLen(_:IntSeq) +Int C2:Int => true
    requires C1 <Int C2 [simplification]
  rule isLen(_:IntSeq) +Int C2:Int >Int C1:Int => true
    requires C1 <Int C2 [simplification]

  // the Str projection: a str Val's code sequence (opaque on a symbolic element)
  syntax IntSeq ::= codesProj(Val) [function, total, symbol(codesProj), no-evaluators]
  rule codesProj(str(CS:IntSeq)) => CS [simplification]

  // str is injective: canonicalize value equality to the code sequences
  rule str(A:IntSeq) ==K str(B:IntSeq) => A ==K B [simplification]

  // ---- the list[str] element discipline (shared; kprove-only — lemmas are
  // not part of the llvm build). strP: opaque str-ness with per-shape kills
  // (the auto-generated isStr's owise misfires on opaque fold terms, and
  // #loop does NOT narrow a raw Val across the Iterable injection, so an
  // abstract str element needs this identity bridge to start iterating:
  // str(codesProj(V)) == V whenever V is a string).
  syntax Bool ::= strP(Val) [function, total, no-evaluators, symbol(strP)]
  rule strP(str(_:IntSeq)) => true [simplification]
  rule strP(ref(_:Int))          => false [simplification]
  rule strP(cellRef(_:Int))      => false [simplification]
  rule strP(list(_:ValSeq))      => false [simplification]
  rule strP(tuple(_:ValSeq))     => false [simplification]
  rule strP(rangeObj(_:Int, _:Int, _:Int))       => false [simplification]
  rule strP(zipObj(_:ValSeq, _:ValSeq))          => false [simplification]
  rule strP(zipObjS(_:IntSeq, _:IntSeq))         => false [simplification]

  // the CONSTRUCTOR case dispatches like the shared rule (echoed one notch
  // above the bridge — at 40 alone the bridge self-looped on str(CS):
  // codesProj(str(CS)) collapses back to the identical term)
  rule <k> #loop(str(CS:IntSeq), T:Expr, B:Stmts)
        => #iterNext(str(CS)) ~> #loopStep(T, B) ... </k>
    [priority(39)]
  // the ABSTRACT case aligns with the claims' codesProj spelling
  rule <k> #loop(V:Val, T:Expr, B:Stmts) => #loop(str(codesProj(V)), T, B) ... </k>
    requires strP(V)
    [priority(40)]
endmodule
