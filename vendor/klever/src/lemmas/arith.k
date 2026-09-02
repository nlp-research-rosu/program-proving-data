// reference/src/lemmas/arith.k — ARITH-LEMMAS
// Normalization facts on the K-prelude Int sort.

requires "../semantics.k"

module ARITH-LEMMAS
  imports MPY

  // Python // (floored div) on NON-NEGATIVE operands = K's /Int (truncated):
  // applyBin("//", N, M) expands to (N -Int pyMod(N, M)) /Int M with pyMod(N,M) =
  // ((N %Int M) +Int M) %Int M; for N >= 0, M > 0 that collapses to N /Int M. TRUE
  // (Python // = floor = trunc for non-negative). Lets claims use the clean N /Int M.
  rule (N:Int -Int ((N %Int M:Int) +Int M) %Int M) /Int M => N /Int M
       requires N >=Int 0 andBool M >Int 0 [simplification]

  // Odd-branch companion: after a parity case-split the path condition's pyMod(N,2) == 1
  // equation substitutes into N -Int pyMod(N,2) BEFORE the rule above can match, leaving
  // (N +Int -1) /Int 2. For odd N > 0, (N-1)/2 = N/2 under truncated /Int (NOT true for
  // negative N). Guard atoms match the path condition syntactically.
  rule (N:Int +Int -1) /Int 2 => N /Int 2
       requires ((N %Int 2) +Int 2) %Int 2 ==Int 1 andBool N >Int 0 [simplification]

  // range count normalization: remaining-iterations N - (I+1) matches the invariant's N - I - 1
  rule N:Int -Int (I:Int +Int 1) => N -Int I -Int 1 [simplification]

  // slice-width cancellation: (B + L) - B (the lo:hi window i : i+l) is L;
  // the backend does not cancel symbolic linear terms on its own
  rule (X:Int +Int Y:Int) -Int X:Int => Y [simplification]
  rule (Y:Int +Int X:Int) -Int X:Int => Y [simplification]
  rule X:Int -Int (X:Int -Int Y:Int) => Y [simplification]
  rule X:Int *Int 1 => X [simplification]
  rule 1 *Int X:Int => X [simplification]

  // symbolic ** : kprove reasoning about ^Int with a symbolic exponent hangs
  // (nonlinear); ipow is the same power kept as an opaque atom — the
  // [concrete] rule computes the real power on literals, and the k-cell
  // bridge catches ** before applyBin forms ^Int (a negative exponent is a
  // float in python, outside the modeled subset)
  syntax Int ::= ipow(Int, Int) [function, total, symbol(ipow), no-evaluators]
  rule ipow(B:Int, E:Int) => B ^Int E [concrete]
  rule <k> BinOp("**", LV:Int, RV:Int) => ipow(LV, RV) ... </k>
    requires RV >=Int 0
    [priority(40)]

  // euclidean-mod range facts on the expanded pyMod spelling (pyMod(X,M)
  // reduces to ((X %Int M) +Int M) %Int M, which lands in [0, M) for M > 0;
  // Z3 does not decide mod atoms over a symbolic modulus)
  rule ((X:Int %Int M:Int) +Int M:Int) %Int M:Int >=Int 0 => true
    requires M >Int 0 [simplification]
  rule 0 <=Int ((X:Int %Int M:Int) +Int M:Int) %Int M:Int => true
    requires M >Int 0 [simplification]
  rule ((X:Int %Int M:Int) +Int M:Int) %Int M:Int <Int C:Int => true
    requires M >Int 0 andBool M <=Int C [simplification]

  // Bool equality trivia
  rule B:Bool ==Bool true  => B         [simplification]
  rule B:Bool ==Bool false => notBool B [simplification]
endmodule
