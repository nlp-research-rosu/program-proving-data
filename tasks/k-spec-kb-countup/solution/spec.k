requires "verification.k"

module KB-COUNTUP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): r climbs to n; if it starts at or above n it stays put ----
  claim
    <k>
      #while(Compare(Name("r"), CmpOp("<", Name("n"))),
        Assign(Name("r"), BinOp("+", Name("r"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "r" <- I:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "r" <- ?R2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R2 ==Int maxInt(N, I)
    [all-path]

  // ---- Entry claim: the loop terminates with r = max(n, r0), for arbitrary ints n, r0 ----
  // KleverBench problems/imp/countup: `while (!(n <= r)) { r = r + 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("r"), R:Int)
      While(Compare(Name("r"), CmpOp("<", Name("n"))),
        Assign(Name("r"), BinOp("+", Name("r"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "r" <- ?R2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R2 ==Int maxInt(N, R)
    [all-path]
endmodule
