// reference/src/semantics/core.k — MPY-CORE

module MPY-CORE
  imports MPY-SYNTAX
  imports INT
  imports BOOL
  imports STRING
  imports MAP
  imports LIST
  imports K-EQUAL

  // ==== values, the algebraic lists, and the scope heap =====================
  syntax IntSeq ::= ".IntSeq" | iCons(Int, IntSeq)
  syntax ValSeq ::= ".ValSeq" | vCons(Val, ValSeq)
  syntax Str    ::= str(IntSeq)

  // the iterable values, grouped under one sort (typing only — dispatch is <k>-cell)
  syntax Iterable ::= list(ValSeq)
                    | tuple(ValSeq)
                    | Str
                    | rangeObj(Int, Int, Int)
                    | zipObj(ValSeq, ValSeq)
                    | zipObjS(IntSeq, IntSeq)

  syntax Val      ::= Int
                    | Bool
                    | "noneV"
                    | Iterable
                    | ref(Int)          // a heap object: <heap> holds its list(VS)
                    | cellRef(Int)      // a closure cell: <heap> holds cellV(V)
                    | closureVal(ParamNames, Stmts, Int)
                    | typeV(String)     // a type object (int/str), resolved from the builtins frame
                    | builtinV(String)  // a builtin function, resolved like any name (LEGB fallthrough)
                    | boundMethodV(Val, String)   // a cooled Attribute: obj.method

  syntax Parent   ::= "root" | parent(Int)
  syntax Scope    ::= scope(Map, Parent)
  syntax KResult  ::= Val
  syntax Expr     ::= Val   // cooling puts results back into expression holes
  syntax Vals     ::= List{Val, ","}
  syntax Exc      ::= "NoExc" | "AssertionError"
  syntax RetState ::= "noRet" | retV(Val)

  // ==== configuration =======================================================
  // The builtins namespace is a real scope at reserved location -1 (the bottom of every
  // chain; scopeLoc only allocates >=1, so -1 never collides). The module scope (loc 0)
  // has it as parent, so an unbound name resolves there last — exactly LEGB. `int`/`str`
  // resolve to their type objects; any local/global binding shadows them via normal lookup.
  configuration
    <k>       #loadAll($PGM:Module) </k>
    <env>     0 </env>
    <scopes>   0     |-> scope(.Map, parent(-1))
              -1    |-> builtinsScope </scopes>
    <scopeLoc> 1 </scopeLoc>
    <heap>    .Map </heap>
    <heapLoc> 0 </heapLoc>
    <stack>   .List </stack>
    <ret>     noRet </ret>
    <exc>     NoExc </exc>
    <exit-code exit=""> 0 </exit-code>

  // ==== heap allocation (constructed lists become objects) ==================
  // Cons-form emission with a freshness guard (the heap-list-probe discipline:
  // an update-form H[N <- _] never re-normalizes symbolically). heapLoc is
  // monotonic — it does NOT wind back at #pop: returned lists escape by ref.
  // A bare list(VS) Val stays legal (read-only inputs in claims flow unboxed);
  // only CONSTRUCTORS in program syntax allocate.
  syntax Bool ::= isRefV(Val) [function, total]
  rule isRefV(ref(_:Int)) => true
  rule isRefV(_:Val)      => false [owise]

  // closure cells (Python-faithful capture): the heap holds cellV(V); a
  // cellRef surfacing as the k-redex reads through (lookup is the only use —
  // cellRefs never escape to user-visible values)
  syntax HeapVal ::= cellV(Val)
  syntax Bool ::= isCellRef(Val) [function, total]
  rule isCellRef(cellRef(_:Int)) => true
  rule isCellRef(_:Val)          => false [owise]
  // k-top deref for cell-bound reads surfacing INSIDE the annotated frame
  // (AugAssign's in-place read and friends). The "$cells" guard keeps this
  // DECIDABLY inapplicable in plain frames — an unguarded rule lets the
  // prover narrow abstract k-top values into cellRef junk (probed on
  // 26-remove-duplicates). Cross-frame reads (a comprehension closure
  // reading the enclosing function's cellvar) deref inside #look instead.
  rule <k> cellRef(H:Int) => V ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map, _) ... </scopes>
       <heap> ... H |-> cellV(V:Val) ... </heap>
       requires "$cells" in_keys(M)
       [priority(40)]

  // write through a cell (Assign / #bindP / #bindTgt dispatch here on
  // cell-bound names)
  // a keyword argument cools to a TAGGED value (consumed by kw-aware builtins)
  syntax Val ::= kwV(String, Val)
  syntax KItem ::= #kwTag(String)
  rule <k> KwArg(N:String, E:Expr) => E ~> #kwTag(N) ... </k>
  rule <k> V:Val ~> #kwTag(N:String) => kwV(N, V) ... </k>
       requires notBool isKwV(V)
  syntax Bool ::= isKwV(Val) [function, total]
  rule isKwV(kwV(_:String, _:Val)) => true
  rule isKwV(_:Val)                => false [owise]

  // the frame marker carries the CONCRETE cellvar list, so cell-write dispatch
  // decides by pnMember even over an abstract frame rest (no prover branching)
  syntax Val ::= cellsMark(ParamNames)
  syntax ParamNames ::= cellsOf(Val) [function]
  rule cellsOf(cellsMark(CVS:ParamNames)) => CVS
  syntax Bool ::= pnMember(String, ParamNames) [function, total]
  rule pnMember(_:String, .ParamNames) => false
  rule pnMember(X:String, (P:String, R:ParamNames)) => X ==String P orBool pnMember(X, R)

  syntax KItem ::= #cellW(Val, Val)
  rule <k> #cellW(cellRef(H:Int), V:Val) => .K ... </k>
       <heap> ... H |-> cellV(_:Val => V) ... </heap>

  syntax KItem ::= #alloc(Val)
  rule <k> #alloc(V:Val) => ref(N) ... </k>
       <heap>    H:Map => (N |-> V) H </heap>
       <heapLoc> N:Int => N +Int 1 </heapLoc>
       requires notBool N in_keys(H)

  // ==== module load + statement sequencing ==================================
  syntax KItem ::= #loadAll(Module)
  rule <k> #loadAll(Module(SS:Stmts)) => SS ... </k>
  rule <k> (S:Stmt SS:Stmts):Stmts => S ~> SS ... </k>
  rule <k> .Stmts => .K ... </k>

  // ==== Name lookup (walk the scope chain; builtins live in the -1 scope) ====
  syntax KItem ::= #look(String, Int)
  rule <k> Name(X:String) => #look(X, L) ... </k> <env> L:Int </env>
  rule <k> #look(X:String, L:Int) => {M[X]}:>Val ... </k>
       <scopes> ... L |-> scope(M:Map, _:Parent) ... </scopes>
       requires X in_keys(M)
  // a SYNTACTICALLY cell-bound name reads through the heap cell AT THE
  // LOOKUP (higher priority beats the plain return above on concrete cell
  // bindings; abstract claim values take the plain rule unchanged) — this
  // covers cross-frame cell reads (a comprehension closure reading the
  // enclosing function's cellvar) without a narrowing-prone k-top redex
  // guarded on the FOUND frame's DECLARED cellvars (pnMember over the
  // cellsMark): decidable for every concrete frame pin — plain frames and
  // non-cell names prune outright, so an abstract looked-up value never
  // drags a narrowing cellV heap match along (probed on 5-intersperse and
  // Q4's abstract `numbers` in the annotated frame)
  rule <k> #look(X:String, L:Int) => V ... </k>
       <scopes> ... L |-> scope(M:Map, _:Parent) ... </scopes>
       <heap> ... H |-> cellV(V:Val) ... </heap>
       requires X in_keys(M) andBool "$cells" in_keys(M)
        andBool pnMember(X, cellsOf({M["$cells"]}:>Val))
        andBool {M[X]}:>Val ==K cellRef(H)
       [priority(40)]
  rule <k> #look(X:String, L:Int) => #look(X, P) ... </k>
       <scopes> ... L |-> scope(M:Map, parent(P:Int)) ... </scopes>
       requires notBool (X in_keys(M))

  // the ONE predefined builtins scope (the -1 frame; claims write `-1 |-> builtinsScope`)
  syntax Scope ::= "builtinsScope" [function, total]
  rule builtinsScope
    => scope(.Map [ "len"    <- builtinV("len")    ]
                  [ "set"    <- builtinV("set")    ]
                  [ "sum"    <- builtinV("sum")    ]
                  [ "abs"    <- builtinV("abs")    ]
                  [ "min"    <- builtinV("min")    ]
                  [ "max"    <- builtinV("max")    ]
                  [ "ord"    <- builtinV("ord")    ]
                  [ "chr"    <- builtinV("chr")    ]
                  [ "range"  <- builtinV("range")  ]
                  [ "all"    <- builtinV("all")    ]
                  [ "any"    <- builtinV("any")    ]
                  [ "zip"    <- builtinV("zip")    ]
                  [ "isinstance" <- builtinV("isinstance") ]
                  [ "sorted" <- builtinV("sorted") ]
                  [ "list"   <- builtinV("list")   ]
                  [ "round"  <- builtinV("round")  ]
                  [ "bin"    <- builtinV("bin")    ]
                  [ "enumerate" <- builtinV("enumerate") ]
                  [ "map"    <- builtinV("map")    ]
                  [ "eval"   <- builtinV("eval")   ]
                  [ "int"    <- typeV("int")       ]
                  [ "str"    <- typeV("str")       ]
                  [ "float"  <- typeV("float")     ], root)

  // ==== argument/element evaluation: ONE left-to-right loop, tagged by destination ==
  // (list/tuple literals and calls all use it; modules extend ApplyK with their tags)
  syntax ApplyK ::= toCall(Val)
  syntax KItem  ::= #evalArgs(Exprs, Vals, ApplyK)
                  | #evalArgCont(Exprs, Vals, ApplyK)
                  | #applyK(ApplyK, Vals)
  rule <k> #evalArgs((A:Expr, REST:Exprs), ACC:Vals, K:ApplyK) => A ~> #evalArgCont(REST, ACC, K) ... </k>
  rule <k> V:Val ~> #evalArgCont(REST:Exprs, ACC:Vals, K:ApplyK) => #evalArgs(REST, appendVal(ACC, V), K) ... </k>
  rule <k> #evalArgs(.Exprs, ACC:Vals, K:ApplyK) => #applyK(K, ACC) ... </k>

  // ==== Int / Bool / None literals ==========================================
  rule <k> Int(I:Int)   => I ... </k>
  rule <k> Bool(B:Bool) => B ... </k>
  rule <k> NoneVal      => noneV ... </k>

  // ==== truthy (If, Assert, BoolOp, IfExp, not, While) ======================
  syntax Bool ::= truthy(Val) [function]
  rule truthy(B:Bool)          => B
  rule truthy(noneV)           => false
  rule truthy(I:Int)           => I =/=Int 0
  rule truthy(str(S:IntSeq))   => notBool (S ==K .IntSeq)
  rule truthy(list(V:ValSeq))  => notBool (V ==K .ValSeq)
  rule truthy(tuple(V:ValSeq)) => notBool (V ==K .ValSeq)

  // ==== extensible operator dispatch (cases added by the construct modules) ==
  syntax Val  ::= applyUn(String, Val) [function]
  syntax Val  ::= applyBin(String, Val, Val) [function]
  syntax Bool ::= applyCmp(String, Val, Val) [function]

  // ==== shared list helpers =================================================
  syntax Vals ::= appendVal(Vals, Val) [function, total]
  rule appendVal(.Vals, V:Val)              => V , .Vals
  rule appendVal((V0:Val, VS:Vals), V:Val)  => V0 , appendVal(VS, V)

  syntax ValSeq ::= vals2valSeq(Vals) [function, total]
  rule vals2valSeq(.Vals)            => .ValSeq
  rule vals2valSeq((V:Val, VS:Vals)) => vCons(V, vals2valSeq(VS))

  // ==== shared sequence length (len / summaries across many modules) ========
  // (positional access valSeqAt/intSeqAt + normIdx live in subscript.k)
  syntax Int ::= vsLen(ValSeq) [function, total]
  rule vsLen(.ValSeq)                => 0
  rule vsLen(vCons(_:Val, S:ValSeq)) => 1 +Int vsLen(S)

  syntax Int ::= isLen(IntSeq) [function, total]
  rule isLen(.IntSeq)                => 0
  rule isLen(iCons(_:Int, S:IntSeq)) => 1 +Int isLen(S)

  // in-bounds positional write (list subscript-assign); OOB leaves the seq unchanged
  // (valid programs write in-bounds — mirrors valSeqAt's total-but-underspecified stance)
  syntax ValSeq ::= setVSAt(ValSeq, Int, Val) [function, total]
  rule setVSAt(.ValSeq, _:Int, _:Val)               => .ValSeq
  rule setVSAt(vCons(_:Val, S:ValSeq), 0, V:Val)    => vCons(V, S)
  rule setVSAt(vCons(W:Val, S:ValSeq), I:Int, V:Val) => vCons(W, setVSAt(S, I -Int 1, V))
       requires I >Int 0
  rule setVSAt(VS:ValSeq, I:Int, _:Val)             => VS
       requires I <Int 0
endmodule
