// reference/src/semantics/tuple.k — MPY-TUPLE

module MPY-TUPLE
  imports MPY-CORE
  imports MPY-ITER
  imports MPY-LIST
  imports MPY-METHODS

  // ==== iteration (the iterator protocol's tuple case) ======================
  rule <k> #iterNext(tuple(.ValSeq))                => #iterDone ... </k>
  rule <k> #iterNext(tuple(vCons(V:Val, R:ValSeq))) => #iterYield(V, tuple(R)) ... </k>

  // ==== TupleExpr: tuple(ValSeq) literal + == != ===========================
  syntax ApplyK ::= "toTuple"
  rule <k> TupleExpr(ES:Exprs) => #evalArgs(ES, .Vals, toTuple) ... </k>
  rule <k> #applyK(toTuple, ACC:Vals) => tuple(vals2valSeq(ACC)) ... </k>

  rule applyCmp("==", tuple(A:ValSeq), tuple(B:ValSeq)) => A ==K B
  // membership routes through the same k-cell fold as lists (list.k)
  rule <k> Compare(LV:Val, CmpOp("in",     tuple(VS:ValSeq))) => #memberAcc(LV, tuple(VS)) ... </k>
  rule <k> Compare(LV:Val, CmpOp("not in", tuple(VS:ValSeq))) => #memberAcc(LV, tuple(VS)) ~> #notB ... </k>
  // t.index(v): first index of v (ValueError out of subset)
  rule applyMethod(tuple(VS:ValSeq), "index", V:Val, .Vals) => idxOfVS(VS, V, 0)
  syntax Int ::= idxOfVS(ValSeq, Val, Int) [function]
  rule idxOfVS(vCons(A:Val, _:ValSeq), V:Val, I:Int) => I requires A ==K V
  rule idxOfVS(vCons(A:Val, R:ValSeq), V:Val, I:Int) => idxOfVS(R, V, I +Int 1)
       requires notBool (A ==K V)
  rule applyCmp("!=", tuple(A:ValSeq), tuple(B:ValSeq)) => notBool (A ==K B)

  // ==== target binding: bind a Name or a TupleExpr target to a value ========
  syntax KItem ::= #bindTgt(Expr, Val)
  rule <k> #bindTgt(Name(X:String), V:Val) => .K ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map => M [ X <- V ], _) ... </scopes>
  rule <k> #bindTgt(Name(X:String), V:Val) => #cellW({M[X]}:>Val, V) ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map, _) ... </scopes>
       requires "$cells" in_keys(M)
        andBool pnMember(X, cellsOf({M["$cells"]}:>Val))
        andBool X in_keys(M) andBool isCellRef({M[X]}:>Val)
       [priority(40)]
  rule <k> #bindTgt(TupleExpr(TS:Exprs), tuple(VS:ValSeq)) => #unpackSeq(TS, VS) ... </k>
  rule <k> #bindTgt(TupleExpr(TS:Exprs), list(VS:ValSeq))  => #unpackSeq(TS, VS) ... </k>
  rule <k> #bindTgt(TupleExpr(TS:Exprs), ref(H:Int)) => #bindTgt(TupleExpr(TS), V) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]

  // ==== unpacking: a, b = <tuple|list> (RHS evaluated by strictness) ========
  syntax KItem ::= #unpackSeq(Exprs, ValSeq)
  rule <k> Assign(TupleExpr(TS:Exprs), tuple(VS:ValSeq)) => #unpackSeq(TS, VS) ... </k>
  rule <k> Assign(TupleExpr(TS:Exprs), list(VS:ValSeq))  => #unpackSeq(TS, VS) ... </k>
  rule <k> Assign(TupleExpr(TS:Exprs), ref(H:Int)) => Assign(TupleExpr(TS), V) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]
  rule <k> #unpackSeq((T:Expr, TS:Exprs), vCons(V:Val, VS:ValSeq))
        => #bindTgt(T, V) ~> #unpackSeq(TS, VS) ... </k>
  rule <k> #unpackSeq(.Exprs, .ValSeq) => .K ... </k>
endmodule
