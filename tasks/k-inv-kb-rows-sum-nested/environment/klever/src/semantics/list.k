// reference/src/semantics/list.k — MPY-LIST

module MPY-LIST
  imports MPY-CORE
  imports MPY-ITER
  imports MPY-OPERATORS

  // ==== iteration (the iterator protocol's list case) =======================
  rule <k> #iterNext(list(.ValSeq))                => #iterDone ... </k>
  rule <k> #iterNext(list(vCons(V:Val, R:ValSeq))) => #iterYield(V, list(R)) ... </k>

  // ==== ListExpr: [...] literal -> a fresh heap object =======================
  syntax ApplyK ::= "toList"
  rule <k> ListExpr(ES:Exprs) => #evalArgs(ES, .Vals, toList) ... </k>
  rule <k> #applyK(toList, ACC:Vals) => #alloc(list(vals2valSeq(ACC))) ... </k>

  // ==== list ops: + / == / != ===============================================
  syntax ValSeq ::= valSeqConcat(ValSeq, ValSeq) [function, total]
  rule valSeqConcat(.ValSeq, T:ValSeq)                => T
  rule valSeqConcat(vCons(V:Val, S:ValSeq), T:ValSeq) => vCons(V, valSeqConcat(S, T))

  // list + list constructs a NEW object (k-cell — it allocates; operands land here
  // already deref'd). priority(45) beats the generic BinOp dispatch.
  rule <k> BinOp("+", list(A:ValSeq), list(B:ValSeq)) => #alloc(list(valSeqConcat(A, B))) ... </k>
       [priority(45)]

  rule applyCmp("==", list(A:ValSeq), list(B:ValSeq)) => A ==K B
  rule applyCmp("!=", list(A:ValSeq), list(B:ValSeq)) => notBool (A ==K B)

  // ==== deep equality when elements are heap objects (list-of-lists) ========
  // Python == is structural at every depth. Fires ONLY when a ref is present
  // (the guard decides on concrete seqs); the plain ==K path above is unchanged.
  syntax Bool ::= hasRefVS(ValSeq) [function, total]
  rule hasRefVS(.ValSeq)                => false
  rule hasRefVS(vCons(V:Val, R:ValSeq)) => isRefV(V) orBool hasRefVS(R)

  syntax Bool ::= deepEqVS(ValSeq, ValSeq, Map) [function]
                | deepEqV(Val, Val, Map)        [function]
  rule deepEqVS(.ValSeq, .ValSeq, _:Map)                   => true
  rule deepEqVS(.ValSeq, vCons(_:Val, _:ValSeq), _:Map)    => false
  rule deepEqVS(vCons(_:Val, _:ValSeq), .ValSeq, _:Map)    => false
  rule deepEqVS(vCons(A:Val, As:ValSeq), vCons(B:Val, Bs:ValSeq), HP:Map)
    => deepEqV(A, B, HP) andBool deepEqVS(As, Bs, HP)

  rule deepEqV(ref(H:Int), B:Val, HP:Map) => deepEqV({HP[H]}:>Val, B, HP)
       requires H in_keys(HP)
  rule deepEqV(A:Val, ref(H:Int), HP:Map) => deepEqV(A, {HP[H]}:>Val, HP)
       requires notBool isRefV(A) andBool H in_keys(HP)
  rule deepEqV(list(A:ValSeq), list(B:ValSeq), HP:Map) => deepEqVS(A, B, HP)
  rule deepEqV(A:Val, B:Val, _:Map) => A ==K B [owise]

  // ==== mutator: xs.append(v) — an in-place heap write ======================
  rule <k> #applyK(toCall(boundMethodV(ref(H:Int), "append")), (V:Val, .Vals)) => noneV ... </k>
       <heap> ... H |-> list(VS:ValSeq => valSeqConcat(VS, vCons(V, .ValSeq))) ... </heap>
       [priority(40)]

  // ==== `x in list` — a <k>-cell fold over #iterNext ========================
  syntax KItem ::= #memberAcc(Val, Iterable) | #memberCont(Val) | "#notB"
  rule <k> Compare(LV:Val, CmpOp("in",     list(VS:ValSeq))) => #memberAcc(LV, list(VS)) ... </k>
  rule <k> Compare(LV:Val, CmpOp("not in", list(VS:ValSeq))) => #memberAcc(LV, list(VS)) ~> #notB ... </k>
  rule <k> #memberAcc(V:Val, IT:Iterable) => #iterNext(IT) ~> #memberCont(V) ... </k>
  rule <k> #iterDone ~> #memberCont(_V:Val) => false ... </k>
  rule <k> #iterYield(E:Val, _:Iterable) ~> #memberCont(V:Val) => true ... </k>
       requires E ==K V
  rule <k> #iterYield(E:Val, R:Iterable) ~> #memberCont(V:Val) => #memberAcc(V, R) ... </k>
       requires notBool (E ==K V)
  rule <k> B:Bool ~> #notB => notBool B ... </k>
endmodule
