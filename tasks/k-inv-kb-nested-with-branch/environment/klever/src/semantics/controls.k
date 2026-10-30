// reference/src/semantics/controls.k — MPY-CONTROLS

module MPY-CONTROLS
  imports MPY-CORE
  imports MPY-TUPLE
  imports MPY-ITER

  // ==== Assign / AugAssign (write the current scope; RHS evaluated by strictness) ==
  rule <k> Assign(Name(X:String), V:Val) => .K ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map => M [ X <- V ], _) ... </scopes>
  rule <k> Assign(Name(X:String), V:Val) => #cellW({M[X]}:>Val, V) ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map, _) ... </scopes>
       requires "$cells" in_keys(M)
        andBool pnMember(X, cellsOf({M["$cells"]}:>Val))
        andBool X in_keys(M) andBool isCellRef({M[X]}:>Val)
       [priority(40)]

  rule <k> AugAssign(Name(X:String), OP:String, V:Val) => .K ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map => M [ X <- applyBin(OP, {M[X]}:>Val, V) ], _) ... </scopes>
       requires X in_keys(M)

  // ==== import trivia: `from math import floor, ceil` binds the supported
  // names as builtins in the current scope; every other import is a no-op
  rule <k> ImportFrom("math", NS:ParamNames) => #bindImports(NS) ... </k>
  rule <k> ImportFrom(_:String, _:ParamNames) => .K ... </k> [owise]
  syntax KItem ::= #bindImports(ParamNames)
  rule <k> #bindImports(.ParamNames) => .K ... </k>
  rule <k> #bindImports((N:String, NS:ParamNames)) => #bindImports(NS) ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map => M [ N <- builtinV(N) ], _) ... </scopes>
       requires N ==String "floor" orBool N ==String "ceil"
  rule <k> #bindImports((N:String, NS:ParamNames)) => #bindImports(NS) ... </k>
       requires notBool (N ==String "floor" orBool N ==String "ceil")

  // ==== Expr statement: evaluate for effect, discard the value ===============
  // (bare calls — mutator methods, docstrings; the WP0 statement-trivia rung)
  rule <k> Expr(_:Val) => .K ... </k>

  // ==== If (condition evaluated by strictness) ==============================
  syntax KItem ::= #branch(Bool, Stmts, Stmts)
  rule <k> If(C:Val, T:Stmts, E:Stmts) => #branch(truthy(C), T, E) ... </k>
  rule <k> #branch(true,  T:Stmts, _:Stmts) => T ... </k>
  rule <k> #branch(false, _:Stmts, E:Stmts) => E ... </k>

  // ==== IfExp: ternary T if C else E ========================================
  rule <k> IfExp(V:Val, T:Expr, _:Expr) => T ... </k>
       requires truthy(V)
  rule <k> IfExp(V:Val, _:Expr, E:Expr) => E ... </k>
       requires notBool truthy(V)

  // ==== For: one loop, in-cell continuation, over #iterNext =================
  // (the iterable is evaluated once, by strictness; the protocol stays rewrites —
  // circularities anchor on #loop and narrowing substitutes the structure)
  syntax KItem ::= #loop(Val, Expr, Stmts) | #loopStep(Expr, Stmts)
                 | #while(Expr, Stmts) | #whileCond(Expr, Stmts)
                 | #loopLbl(K) | "#cont" | "#brk"

  rule <k> For(T:Expr, OBJ:Val, B:Stmts) => #loop(OBJ, T, B) ... </k>

  rule <k> #loop(IT:Iterable, T:Expr, B:Stmts) => #iterNext(IT) ~> #loopStep(T, B) ... </k>
  rule <k> #iterDone ~> #loopStep(_:Expr, _:Stmts) => .K ... </k>
  rule <k> #iterYield(V:Val, REST:Iterable) ~> #loopStep(T:Expr, B:Stmts)
        => #bindTgt(T, V) ~> B ~> #loopLbl(#loop(REST, T, B)) ... </k>

  // ==== While ==============================================================
  rule <k> While(C:Expr, B:Stmts) => #while(C, B) ... </k>
  rule <k> #while(C:Expr, B:Stmts) => C ~> #whileCond(C, B) ... </k>
  rule <k> V:Val ~> #whileCond(C:Expr, B:Stmts) => B ~> #loopLbl(#while(C, B)) ... </k>
       requires truthy(V)
  rule <k> V:Val ~> #whileCond(_C:Expr, _B:Stmts) => .K ... </k>
       requires notBool truthy(V)

  // ==== loop control (break / continue) =====================================
  rule <k> #loopLbl(NEXT:K) => NEXT ... </k>
  rule <k> Continue => #cont ... </k>
  rule <k> Break => #brk ... </k>
  rule <k> #cont ~> #loopLbl(NEXT:K) => NEXT ... </k>
  rule <k> #cont ~> (_:KItem => .K) ... </k> [owise]
  rule <k> #brk ~> #loopLbl(_:K) => .K ... </k>
  rule <k> #brk ~> (_:KItem => .K) ... </k> [owise]

  // ==== heap-object deref at the truthiness/iteration consumers ==============
  // (priority(40) preempts the generic Val rules so truthy/#loop never see a ref)
  rule <k> If(ref(H:Int), T:Stmts, E:Stmts) => If(V, T, E) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]
  rule <k> IfExp(ref(H:Int), T:Expr, E:Expr) => IfExp(V, T, E) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]
  rule <k> ref(H:Int) ~> #whileCond(C:Expr, B:Stmts) => V ~> #whileCond(C, B) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]
  // For derefs its iterable ONCE at loop start (iteration is over the snapshot;
  // mutating the iterated list inside its own loop is outside the subset)
  rule <k> For(T:Expr, ref(H:Int), B:Stmts) => For(T, V, B) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]
endmodule
