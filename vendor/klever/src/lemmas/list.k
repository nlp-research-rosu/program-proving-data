// reference/src/lemmas/list.k — LIST-LEMMAS
// Facts over valSeqConcat (semantics/list.k): loops fold result = result + [e] left-to-right.

requires "../semantics.k"

module LIST-LEMMAS
  imports MPY

  rule valSeqConcat(valSeqConcat(A:ValSeq, B:ValSeq), C:ValSeq) => valSeqConcat(A, valSeqConcat(B, C)) [simplification]
  rule valSeqConcat(S:ValSeq, .ValSeq) => S [simplification]
  rule valSeqConcat(vCons(V:Val, .ValSeq), R:ValSeq) => vCons(V, R) [simplification]

  // membership as a defined total fold: EXACTLY the value the k-cell
  // #memberAcc/#memberCont fold computes (same ==K leaves, same order), so
  // reducing the fold to it is a faithful equation — the k-cell fold cannot
  // step over a symbolic tail, while the function form stays a case-splittable
  // atom (kprove-only; krun runs the real fold)
  // stepwise-guarded, NOT an orBool unfold: on a concrete spine with a
  // symbolic element the guards stay undecided and the whole application
  // remains ONE partial-free atom (which #branch lifts), where an eager
  // orBool tree of equations lifts as nothing
  // [simplification]-defined (declare-then-guard): a function with plain
  // undecided-guard rules is "conditionally applicable" and its atom never
  // lifts; with simplification-only rules the application is cleanly opaque
  // until a guard is entailed
  syntax Bool ::= memberVS(Val, ValSeq) [function, total, symbol(memberVS)]
  rule memberVS(_:Val, .ValSeq) => false [simplification]
  rule memberVS(V:Val, vCons(E:Val, _:ValSeq)) => true
    requires E ==K V [simplification]
  rule memberVS(V:Val, vCons(E:Val, R:ValSeq)) => memberVS(V, R)
    requires notBool (E ==K V) [simplification]
  rule <k> #memberAcc(V:Val, list(VS:ValSeq))  => memberVS(V, VS) ... </k> [priority(40)]
  rule <k> #memberAcc(V:Val, tuple(VS:ValSeq)) => memberVS(V, VS) ... </k> [priority(40)]
  // ...and already at the Compare dispatch: the heap-deref narrowers sit at
  // priority 40 and would split a symbolic element into ref/cellRef junk
  // branches before the default-priority membership dispatch runs
  rule <k> Compare(LV:Val, CmpOp("in",     list(VS:ValSeq))) => memberVS(LV, VS) ... </k>
    [priority(39)]
  rule <k> Compare(LV:Val, CmpOp("not in", list(VS:ValSeq))) => notBool memberVS(LV, VS) ... </k>
    [priority(39)]
endmodule
