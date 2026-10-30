requires "verification.k"

module KB-NORMALIZE-COUNT-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): from n = N, count = C, the countdown loop runs
  //      max(N,0) times, draining n to min(N,0) and adding max(N,0) to count; a no-op
  //      when N <= 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1)))
        Assign(Name("count"), BinOp("+", Name("count"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "n" <- N:Int ] [ "count" <- C:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- ?F:Int ] [ "count" <- ?C2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(N, 0) andBool ?C2 ==Int C +Int maxInt(N, 0)
    [all-path]

  // ---- Entry claim: n is normalized to |n| by the branch, drained to 0 by the loop while
  //      count climbs to |n|, and res = |n| * a + b — for arbitrary ints a, b, n ----
  // KleverBench problems/imp/normalize-count:
  //   `if (n < 0) { n = 0 - n ; } else { }
  //    count = 0 ;
  //    while (0 < n) { n = n - 1 ; count = count + 1 ; }
  //    res = count * a + b ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      If(Compare(Name("n"), CmpOp("<", Int(0))),
        Assign(Name("n"), BinOp("-", Int(0), Name("n"))),
        .Stmts)
      Assign(Name("count"), Int(0))
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1)))
        Assign(Name("count"), BinOp("+", Name("count"), Int(1))))
      Assign(Name("res"), BinOp("+", BinOp("*", Name("count"), Name("a")), Name("b")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- ?F:Int ] [ "count" <- ?C2:Int ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int 0
    andBool ?C2 ==Int absInt(N)
    andBool ?RES ==Int absInt(N) *Int A +Int B
    [all-path]
endmodule
