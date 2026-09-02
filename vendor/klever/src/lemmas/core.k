// reference/src/lemmas/core.k — CORE-LEMMAS
// Facts over the core sequence constructors (semantics/core.k).

requires "../semantics.k"

module CORE-LEMMAS
  imports MPY
  imports K-EQUAL

  // equality decomposition: compare code sequences element by element
  rule iCons(C:Int, S1:IntSeq) ==K iCons(D:Int, S2:IntSeq) => C ==Int D andBool S1 ==K S2 [simplification]

  // the shared plain `truthy(B:Bool) => B` uses MATCHING, which refuses a
  // function-headed Bool payload (a real isdigit/compare composite); this
  // unification-based twin is the same equation and fires on those terms
  rule truthy(B:Bool) => B [simplification]

  // equation-shaping for branchable atoms: kore case-splits #Equals-liftable
  // equations but not opaque Bool atoms; these sound identities restate the
  // common opaque atoms as hooked equations
  rule S:IntSeq ==K .IntSeq => isLen(S) ==Int 0 [simplification]
  rule .IntSeq ==K S:IntSeq => isLen(S) ==Int 0 [simplification]
  syntax Int ::= dgN(IntSeq) [function, total]
  rule dgN(.IntSeq) => 1
  rule dgN(iCons(C:Int, R:IntSeq)) => #if isDigitC(C) #then dgN(R) #else 0 #fi
  rule allDigit(S:IntSeq) => dgN(S) ==Int 1 [simplification]

  // BoolOp head dispatch via literal-unification (the #branch mechanism):
  // the shared and/or rules guard on truthy(V), and a possibly-partial guard
  // STICKS rather than branching; staging the decision through true/false
  // literal rules lets the prover case-split symbolic head values. Same
  // semantics, kprove-only (lemmas are not in the llvm build).
  syntax KItem ::= #boolAndK(Bool, Val, Expr, Exprs) | #boolOrK(Bool, Val, Expr, Exprs)
  rule <k> BoolOp("and", (V:Val, A:Expr, REST:Exprs)) => #boolAndK(truthy(V), V, A, REST) ... </k>
    [priority(40)]
  rule <k> #boolAndK(true,  _:Val, A:Expr, REST:Exprs) => BoolOp("and", (A, REST)) ... </k>
  rule <k> #boolAndK(false, V:Val, _:Expr, _:Exprs) => V ... </k>
  rule <k> BoolOp("or", (V:Val, A:Expr, REST:Exprs)) => #boolOrK(truthy(V), V, A, REST) ... </k>
    [priority(40)]
  rule <k> #boolOrK(true,  V:Val, _:Expr, _:Exprs) => V ... </k>
  rule <k> #boolOrK(false, _:Val, A:Expr, REST:Exprs) => BoolOp("or", (A, REST)) ... </k>
  // guarded twins: decided-by-entailment head values step without waiting
  // for a literal
  rule <k> #boolAndK(B:Bool, _:Val, A:Expr, REST:Exprs) => BoolOp("and", (A, REST)) ... </k>
    requires B [priority(51)]
  rule <k> #boolAndK(B:Bool, V:Val, _:Expr, _:Exprs) => V ... </k>
    requires notBool B [priority(51)]
  rule <k> #boolOrK(B:Bool, V:Val, _:Expr, _:Exprs) => V ... </k>
    requires B [priority(51)]
  rule <k> #boolOrK(B:Bool, _:Val, A:Expr, REST:Exprs) => BoolOp("or", (A, REST)) ... </k>
    requires notBool B [priority(51)]
  // exhaustive fallback: sequential literal unification leaves a ghost
  // remainder branch (neither true nor false) on an opaque atom; the built-in
  // ite lifts two-way with no remainder
  rule <k> #boolAndK(B:Bool, V:Val, A:Expr, REST:Exprs)
        => #if B #then BoolOp("and", (A, REST)) ~> .K #else V ~> .K #fi ... </k>
    [priority(52)]
  rule <k> #boolOrK(B:Bool, V:Val, A:Expr, REST:Exprs)
        => #if B #then V ~> .K #else BoolOp("or", (A, REST)) ~> .K #fi ... </k>
    [priority(52)]

  // the shared Compare cooling is [owise], which REFUSES symbolic operands
  // (it cannot prove no other rule matches) — this unification echo of the
  // same equation dispatches cooled fn-term operands. Sort-typed k-cell
  // patterns (IV:Int) are WRONG here: kore coerces Val-sorted operands
  // toward the Int injection as a live branch whose atoms miss fold guards
  // (probed on 26-remove-duplicates).
  rule <k> Compare(LV:Val, CmpOp(OP:String, RV:Val)) => applyCmp(OP, LV, RV) ... </k>
    [priority(45)]

  // Int compares on symbolic operands reduce at applyCmp: Val-sorted variable
  // patterns unify with fn terms (subsort-cast patterns do not), and the
  // structural isInt guards decide on Int-injected operands while staying
  // undecided (no fire) on raw Val terms — those keep their own routes
  rule applyCmp("==", V:Val, W:Val) => {V}:>Int ==Int {W}:>Int
    requires isInt(V) andBool isInt(W) [simplification]
  rule applyCmp("!=", V:Val, W:Val) => notBool ({V}:>Int ==Int {W}:>Int)
    requires isInt(V) andBool isInt(W) [simplification]
  rule applyCmp("<", V:Val, W:Val) => {V}:>Int <Int {W}:>Int
    requires isInt(V) andBool isInt(W) [simplification]
  rule applyCmp(">", V:Val, W:Val) => {V}:>Int >Int {W}:>Int
    requires isInt(V) andBool isInt(W) [simplification]
  rule applyCmp("<=", V:Val, W:Val) => notBool ({V}:>Int >Int {W}:>Int)
    requires isInt(V) andBool isInt(W) [simplification]
  rule applyCmp(">=", V:Val, W:Val) => notBool ({V}:>Int <Int {W}:>Int)
    requires isInt(V) andBool isInt(W) [simplification]

  // a returned ternary is the same as a branching return (sound identity);
  // routing it through If lets the prover split on symbolic conditions the
  // IfExp value rules cannot decide (their truthy guards are partial)
  rule <k> Return(IfExp(C:Expr, T:Expr, E:Expr))
        => If(C, Return(T) .Stmts, Return(E) .Stmts) ... </k>
    [priority(40)]
endmodule
