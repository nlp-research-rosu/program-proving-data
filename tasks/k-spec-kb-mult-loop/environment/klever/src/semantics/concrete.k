// reference/src/semantics/concrete.k — MPY-CONCRETE
// Concrete-execution-only rules, visible ONLY to the llvm build (run.sh kompiles
// MPY-CONCRETE; verification builds import MPY and never see these). Rationale:
// a k-cell rule matching value constructors NARROWS abstract Vals in the haskell
// backend ([concrete] is not respected on rewrite rules) — probed on
// 26-remove-duplicates, where element compares branched into deepEqVS.

module MPY-CONCRETE
  imports MPY

  // deep equality for list compares whose elements are heap objects
  // (list-of-lists): Python == is structural at every depth.
  rule <k> Compare(list(A:ValSeq), CmpOp("==", list(B:ValSeq))) => deepEqVS(A, B, HP) ... </k>
       <heap> HP:Map </heap>
       requires hasRefVS(A) orBool hasRefVS(B)
  rule <k> Compare(list(A:ValSeq), CmpOp("!=", list(B:ValSeq))) => notBool deepEqVS(A, B, HP) ... </k>
       <heap> HP:Map </heap>
       requires hasRefVS(A) orBool hasRefVS(B)

  // ==== keyed sort, concrete leg ============================================
  // Computes each key by a REAL call through the uniform #callee machinery
  // (closures, len, type objects all work), stable-inserts on the key, and
  // allocates the result. priority(40) beats sort.k's opaque rules, so krun
  // runs this and proofs (which never see MPY-CONCRETE) keep sortKeyVS.
  syntax Val ::= kvP(Val, Val)
  syntax KItem ::= #ksort(ValSeq, Val, ValSeq, Bool)
                 | #ksIns(Val, ValSeq, Val, ValSeq, Bool)
  rule <k> #applyK(toCall(builtinV("sorted")), (list(VS:ValSeq), kwV("key", KV:Val), .Vals))
        => #ksort(VS, KV, .ValSeq, false) ... </k>
       [priority(40)]
  rule <k> #applyK(toCall(builtinV("sorted")), (list(VS:ValSeq), kwV("key", KV:Val), kwV("reverse", RB:Bool), .Vals))
        => #ksort(VS, KV, .ValSeq, RB) ... </k>
       [priority(40)]
  rule <k> #ksort(.ValSeq, _:Val, ACC:ValSeq, RB:Bool)
        => #alloc(list(condRev(unpairVS(ACC), RB))) ... </k>
  rule <k> #ksort(vCons(V:Val, R:ValSeq), KV:Val, ACC:ValSeq, RB:Bool)
        => KV ~> #callee((V, .Exprs)) ~> #ksIns(V, R, KV, ACC, RB) ... </k>
  rule <k> K:Val ~> #ksIns(V:Val, R:ValSeq, KV:Val, ACC:ValSeq, RB:Bool)
        => #ksort(R, KV, insPair(ACC, K, V), RB) ... </k>
       requires notBool isKwV(K)

  syntax ValSeq ::= insPair(ValSeq, Val, Val) [function]
  rule insPair(.ValSeq, K:Val, V:Val) => vCons(kvP(K, V), .ValSeq)
  rule insPair(vCons(kvP(K2:Val, V2:Val), R:ValSeq), K:Val, V:Val)
    => vCons(kvP(K, V), vCons(kvP(K2, V2), R))
       requires kLt(K, K2)
  rule insPair(vCons(kvP(K2:Val, V2:Val), R:ValSeq), K:Val, V:Val)
    => vCons(kvP(K2, V2), insPair(R, K, V))
       requires notBool kLt(K, K2)

  syntax Bool ::= kLt(Val, Val) [function]
  rule kLt(I1:Int, I2:Int)             => I1 <Int I2
  rule kLt(F1:Float, F2:Float)         => F1 <Float F2
  rule kLt(str(A:IntSeq), str(B:IntSeq)) => strLt(A, B)

  syntax ValSeq ::= unpairVS(ValSeq) [function, total]
  rule unpairVS(.ValSeq) => .ValSeq
  rule unpairVS(vCons(kvP(_:Val, V:Val), R:ValSeq)) => vCons(V, unpairVS(R))
  rule unpairVS(vCons(V:Val, R:ValSeq)) => vCons(V, unpairVS(R)) [owise]
endmodule
