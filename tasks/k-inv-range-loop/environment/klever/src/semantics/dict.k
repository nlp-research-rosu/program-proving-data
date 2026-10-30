// reference/src/semantics/dict.k — MPY-DICT
//
// Minimal dict support. A dict value is `dictV(KS, VS)`: PARALLEL insertion-ordered key/value
// ValSeqs (Python dict order; keys distinct; re-inserting a key updates its value in place, keeping
// the original position). Concrete for krun (the ordered build + `.keys()` are the real ops); a proof
// over a SYMBOLIC dict passes `dictV(KS, WS)` with a symbolic key sequence KS and reads
// `d.keys() = list(KS)`, then keeps each key opaque problem-locally.
//
// Only the pieces needed so far: a dict VALUE (so `{}` inside a mixed list evaluates and
// `isinstance(x, int)` rejects it), the `{k: v, ...}` literal, and `.keys()`. More dict ops (subscript
// / `.get()` / `.values()` / dict `==`) are added as dict problems need them — kept minimal + additive.

module MPY-DICT
  imports MPY-CORE
  imports MPY-ITER
  imports MPY-METHODS
  imports MPY-LIST

  // dict as PARALLEL ordered key/value ValSeqs (same length; keys distinct).
  syntax Val ::= dictV(ValSeq, ValSeq)

  // ==== DictExpr: {k: v, ...} literal. Eval each key then value, left to right, insert-with-dedup.
  syntax KItem ::= #dictAcc(Entries, ValSeq, ValSeq)
                 | #dictKey(Expr, Entries, ValSeq, ValSeq)
                 | #dictVal(Val, Entries, ValSeq, ValSeq)
  rule <k> DictExpr(ES:Entries) => #dictAcc(ES, .ValSeq, .ValSeq) ... </k>
  rule <k> #dictAcc(.Entries, KS:ValSeq, VS:ValSeq) => dictV(KS, VS) ... </k>
  rule <k> #dictAcc((Entry(K:Expr, V:Expr), REST:Entries), KS:ValSeq, VS:ValSeq)
        => K ~> #dictKey(V, REST, KS, VS) ... </k>
  rule <k> KV:Val ~> #dictKey(V:Expr, REST:Entries, KS:ValSeq, VS:ValSeq)
        => V ~> #dictVal(KV, REST, KS, VS) ... </k>
  rule <k> VV:Val ~> #dictVal(KV:Val, REST:Entries, KS:ValSeq, VS:ValSeq)
        => #dictAcc(REST, dPutK(KS, KV), dPutV(KS, VS, KV, VV)) ... </k>

  // insert-with-dedup helpers (concrete Val key equality via ==K). [total] so buildFold over a dict is
  // total (its #Ceil is #Top) — needed when a symbolic proof carries a built dict as a config value.
  syntax Bool ::= dHasKey(ValSeq, Val) [function, total]
  rule dHasKey(.ValSeq, _:Val)                => false
  rule dHasKey(vCons(A:Val, _:ValSeq), K:Val) => true          requires A ==K K
  rule dHasKey(vCons(A:Val, R:ValSeq), K:Val) => dHasKey(R, K) requires notBool (A ==K K)

  // dPutK: KS unchanged if K already present, else append K (keep-first-position).
  syntax ValSeq ::= dPutK(ValSeq, Val) [function, total]
  rule dPutK(KS:ValSeq, K:Val) => KS                                  requires dHasKey(KS, K)
  rule dPutK(KS:ValSeq, K:Val) => valSeqConcat(KS, vCons(K, .ValSeq)) requires notBool dHasKey(KS, K)

  // dPutV: parallel to KS — set the value at K's position if present, else append V at the end. The
  // [owise] catch-all covers the degenerate mismatched-length case (never reached for a well-formed dict).
  syntax ValSeq ::= dPutV(ValSeq, ValSeq, Val, Val) [function, total]
  rule dPutV(vCons(A:Val, _:ValSeq), vCons(_:Val, VR:ValSeq), K:Val, V:Val)  => vCons(V, VR)
       requires A ==K K
  rule dPutV(vCons(A:Val, KR:ValSeq), vCons(B:Val, VR:ValSeq), K:Val, V:Val) => vCons(B, dPutV(KR, VR, K, V))
       requires notBool (A ==K K)
  rule dPutV(_KS:ValSeq, VS:ValSeq, _K:Val, V:Val) => valSeqConcat(VS, vCons(V, .ValSeq)) [owise]

  // ==== dict methods ========================================================
  // d.keys() -> a FRESH list object of the ordered keys (k-cell: it allocates).
  rule <k> #applyK(toCall(boundMethodV(dictV(KS:ValSeq, _:ValSeq), "keys")), .Vals)
        => #alloc(list(KS)) ... </k>
       [priority(40)]

  // ==== dict subscript READ: d[k] (assoc lookup; KeyError is out of subset) ==
  rule applyIndexD(dictV(KS:ValSeq, VS:ValSeq), K:Val) => dGet(KS, VS, K)
  syntax Val ::= applyIndexD(Val, Val) [function]
  rule <k> Subscript(dictV(KS:ValSeq, VS:ValSeq), K:Val) => applyIndexD(dictV(KS, VS), K) ... </k>
       [priority(45)]

  // ==== dict subscript-assign: d[k] = v (insert/update in place) =============
  // Only for a LOCAL dict variable X (the current scope holds it). Reuses dPutK/dPutV.
  syntax Val ::= dictSet(Val, Val, Val) [function]
  rule dictSet(dictV(KS:ValSeq, VS:ValSeq), K:Val, V:Val) => dictV(dPutK(KS, K), dPutV(KS, VS, K, V))

  // RHS evaluates first (Assign strictness), then the key. Dispatch on the scope
  // value: a bare dict updates in the scope (dicts stay values); a ref (a heap
  // list — or a heap dict later) writes the heap in place.
  syntax KItem ::= #dsetK(String, Val)
  rule <k> Assign(Subscript(Name(X:String), K:Expr), VV:Val) => K ~> #dsetK(X, VV) ... </k>
  rule <k> KV:Val ~> #dsetK(X:String, VV:Val) => .K ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map => M [ X <- dictSet({M[X]}:>Val, KV, VV) ], _) ... </scopes>
       requires X in_keys(M) andBool notBool isRefV({M[X]}:>Val)
  rule <k> KV:Val ~> #dsetK(X:String, VV:Val) => #dsetV({M[X]}:>Val, KV, VV) ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map, _) ... </scopes>
       requires X in_keys(M) andBool isRefV({M[X]}:>Val)
  syntax KItem ::= #dsetV(Val, Val, Val)
  rule <k> #dsetV(ref(H:Int), I:Int, VV:Val) => .K ... </k>
       <heap> ... H |-> list(VS:ValSeq => setVSAt(VS, normIdxD(I, vsLen(VS)), VV)) ... </heap>
  // negative-index normalization local to the write (subscript.k's is not imported here)
  syntax Int ::= normIdxD(Int, Int) [function, total]
  rule normIdxD(I:Int, LEN:Int) => I +Int LEN requires I  <Int 0
  rule normIdxD(I:Int, _:Int)   => I          requires I >=Int 0

  // ==== dict == (order-insensitive: same size + same key->value pairs) =======
  rule applyCmp("==", dictV(KS1:ValSeq, VS1:ValSeq), dictV(KS2:ValSeq, VS2:ValSeq))
    => (vsLen(KS1) ==Int vsLen(KS2)) andBool dSubset(KS1, VS1, KS2, VS2)
  syntax Bool ::= dSubset(ValSeq, ValSeq, ValSeq, ValSeq) [function]
  rule dSubset(.ValSeq, .ValSeq, _:ValSeq, _:ValSeq) => true
  rule dSubset(vCons(K:Val, KR:ValSeq), vCons(V:Val, VR:ValSeq), KS2:ValSeq, VS2:ValSeq)
    => dHasKey(KS2, K) andBool (dGet(KS2, VS2, K) ==K V) andBool dSubset(KR, VR, KS2, VS2)
  syntax Val ::= dGet(ValSeq, ValSeq, Val) [function]
  rule dGet(vCons(A:Val, _:ValSeq), vCons(B:Val, _:ValSeq), K:Val) => B                requires A ==K K
  rule dGet(vCons(A:Val, KR:ValSeq), vCons(_:Val, VR:ValSeq), K:Val) => dGet(KR, VR, K) requires notBool (A ==K K)
endmodule
