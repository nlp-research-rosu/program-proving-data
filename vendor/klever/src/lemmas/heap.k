// reference/src/lemmas/heap.k — HEAP-LEMMAS
// Proof-side discipline for the <heap> cell (semantics/core.k #alloc, cons-form
// emission). Two jobs: (1) discharge the allocation freshness guard
// `notBool N in_keys(H)` under a GROWING heap (loop bodies allocate garbage the
// invariant never reads) via the keysBelow bound the claims carry; (2) the
// heap-list-probe's update-vs-cons decomposition, kept as belt and suspenders.

requires "../semantics.k"

module HEAP-LEMMAS
  imports MPY
  imports K-EQUAL
  imports MAP-SYMBOLIC

  // keysBelow(M, B): every key of M is an Int < B. Uninterpreted over a symbolic
  // rest (no evaluator rules) + sound axioms. An invariant whose loop allocates
  // carries `keysBelow(HREST, HL)` (HREST its abstract heap rest, HL its heapLoc);
  // the axioms peel concrete entries, absorb heapLoc offsets, and turn the
  // allocator's in_keys test false.
  syntax Bool ::= keysBelow(Map, Int) [function, total, symbol(keysBelow), no-evaluators]

  rule keysBelow(.Map, _:Int) => true
    [simplification]
  rule keysBelow((K:Int |-> _:KItem) M:Map, B:Int) => keysBelow(M, B)
    requires K <Int B
    [simplification]
  // heapLoc only grows: bounded below B implies bounded below B + K. Reduces to
  // true with the B-bound in the REQUIRES (not by rewriting the bound down): an
  // eager bound-lowering rewrite fires before the concrete entries peel and makes
  // a key equal to the lowered bound unpeelable — probed (plus-builder leg).
  rule keysBelow(M:Map, B:Int +Int K:Int) => true
    requires K >=Int 0 andBool keysBelow(M, B)
    [simplification]

  // the bridge: no key at or above the bound — with B := K itself, every variable
  // is LHS-bound, so this is a legal simplification
  rule K:Int in_keys(M:Map) => false
    requires keysBelow(M, K)
    [simplification]

  // (The generic cons/update map laws that briefly lived here were removed:
  // the closed-frame claim discipline made them dead weight, and their per-
  // lookup SMT guards slowed every proof — probed on 91-is-bored.)

  // membership decomposition over a cons entry (Int-keyed cells: <heap>, <scopes>)
  rule K1:Int in_keys((K2:Int |-> _:KItem) M:Map) => K1 ==Int K2 orBool K1 in_keys(M)
    [simplification]

  // update-vs-cons map equation decomposition (heap-list-probe fix 1): with K fresh
  // for both rests, the maps agree iff the K-values agree and the rests agree
  rule { M:Map [ K:KItem <- V:KItem ] #Equals (K |-> W:KItem REST:Map) }
    => { V #Equals W } #And { M #Equals REST }
    requires notBool K in_keys(M) andBool notBool K in_keys(REST)
    [simplification]
  rule { (K |-> W:KItem REST:Map) #Equals M:Map [ K:KItem <- V:KItem ] }
    => { V #Equals W } #And { M #Equals REST }
    requires notBool K in_keys(M) andBool notBool K in_keys(REST)
    [simplification]
endmodule
