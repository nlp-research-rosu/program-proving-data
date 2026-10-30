// reference/src/semantics/sort.k — MPY-SORT
// Trusted sorted(): sorted(list) as an opaque ascending permutation `sortVS` — opaque symbolic
// for kprove (a trusted primitive, correctness/ordering proved in Lean / notes/sort-probe),
// and a concrete insertion sort for krun. Wrappers verify the logic AROUND the sort (index /
// slice / filter / dedup); indexing an opaque sortVS(VS) carries through as an opaque term, so
// no ordering lemma is needed in K — the trust (sortVS = real sorted) is discharged by each
// problem's differential test. Only int lists (compared by projectIntTotal); keyed / string
// sorts are separate. Fires only via the "sorted" builtin, so inert for non-sorting programs.

module MPY-SORT
  imports MPY-BUILTINS
  imports MPY-SUBSCRIPT

  // sortVS(VS): the ascending sort of the Val list VS. Opaque for symbolic VS (no-evaluators);
  // concrete insertion sort for krun.
  // Concrete sort matches Int-sorted elements directly (an int Val IS an Int); projectIntTotal
  // (lemmas-only) is not available in the semantics. Int and str lists.
  syntax ValSeq ::= sortVS(ValSeq) [function, total, symbol(sortVS), no-evaluators]
  syntax ValSeq ::= insVS(Int, ValSeq) [function]
  rule sortVS(.ValSeq)                => .ValSeq          [concrete]
  rule sortVS(vCons(X:Int, R:ValSeq)) => insVS(X, sortVS(R)) [concrete]
  rule insVS(X:Int, .ValSeq)                => vCons(X, .ValSeq) [concrete]
  rule insVS(X:Int, vCons(Y:Int, R:ValSeq)) => vCons(X, vCons(Y, R)) requires X <=Int Y [concrete]
  rule insVS(X:Int, vCons(Y:Int, R:ValSeq)) => vCons(Y, insVS(X, R)) requires X  >Int Y [concrete]
  // str elements insert by the shared lexicographic strLt (methods.k)
  syntax ValSeq ::= insVSs(IntSeq, ValSeq) [function]
  rule sortVS(vCons(str(CS:IntSeq), R:ValSeq)) => insVSs(CS, sortVS(R)) [concrete]
  rule insVSs(A:IntSeq, .ValSeq) => vCons(str(A), .ValSeq) [concrete]
  rule insVSs(A:IntSeq, vCons(str(B:IntSeq), R:ValSeq)) => vCons(str(A), vCons(str(B), R))
       requires strLt(A, B) orBool A ==K B [concrete]
  rule insVSs(A:IntSeq, vCons(str(B:IntSeq), R:ValSeq)) => vCons(str(B), insVSs(A, R))
       requires notBool (strLt(A, B) orBool A ==K B) [concrete]

  // sorted(list) constructs a NEW object: k-cell pre-dispatch (beats the [owise]
  // applyBuiltin routing in call.k) so the result allocates.
  rule <k> #applyK(toCall(builtinV("sorted")), (list(VS:ValSeq), .Vals))
        => #alloc(list(sortVS(VS))) ... </k>

  // mutator: xs.sort() — the in-place heap write over the same trusted sortVS
  rule <k> #applyK(toCall(boundMethodV(ref(H:Int), "sort")), .Vals) => noneV ... </k>
       <heap> ... H |-> list(VS:ValSeq => sortVS(VS)) ... </heap>
       [priority(40)]

  // ==== keyed / reversed sorted() (WP2) =====================================
  // sortKeyVS(VS, KV): the stable ascending sort of VS by the key value KV
  // (a closure/builtin/type — anything callable). OPAQUE here; the concrete
  // leg (MPY-CONCRETE, llvm only) computes keys by REAL calls and stable-
  // inserts, at priority(40) over these.
  syntax ValSeq ::= sortKeyVS(ValSeq, Val) [function, total, symbol(sortKeyVS), no-evaluators]

  syntax ValSeq ::= revVS(ValSeq) [function, total]
                  | revVSAcc(ValSeq, ValSeq) [function, total]
  rule revVS(S:ValSeq) => revVSAcc(S, .ValSeq)
  rule revVSAcc(.ValSeq, A:ValSeq) => A
  rule revVSAcc(vCons(V:Val, R:ValSeq), A:ValSeq) => revVSAcc(R, vCons(V, A))

  syntax ValSeq ::= condRev(ValSeq, Bool) [function, total]
  rule condRev(S:ValSeq, false) => S
  rule condRev(S:ValSeq, true)  => revVS(S)

  rule <k> #applyK(toCall(builtinV("sorted")), (list(VS:ValSeq), kwV("key", KV:Val), .Vals))
        => #alloc(list(sortKeyVS(VS, KV))) ... </k>
  rule <k> #applyK(toCall(builtinV("sorted")), (list(VS:ValSeq), kwV("key", KV:Val), kwV("reverse", RB:Bool), .Vals))
        => #alloc(list(condRev(sortKeyVS(VS, KV), RB))) ... </k>
  rule <k> #applyK(toCall(builtinV("sorted")), (list(VS:ValSeq), kwV("reverse", RB:Bool), .Vals))
        => #alloc(list(condRev(sortVS(VS), RB))) ... </k>

  // Indexing the opaque sorted list: `valSeqAt(sortVS(VS), I)` is DEFINED because valSeqAt is
  // [total] (subscript.k) — it stays an abstract total value for a symbolic sort and reduces
  // over the concrete sort for krun. No separate sortedAt indirection is needed; wrappers write
  // their postcondition directly as valSeqAt(sortVS(VS), …).
endmodule
