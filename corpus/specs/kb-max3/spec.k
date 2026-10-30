requires "verification.k"

module KB-MAX3-SPEC
  imports KB-MAX3-VERIFICATION

  // ---- Entry claim: after the two branches, max holds the maximum of a, b, n, for all ints ----
  // KleverBench problems/imp/max3:
  //   `max = a ; if (max <= b) { max = b ; } else { } if (max <= n) { max = n ; } else { }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      Assign(Name("max"), Name("a"))
      If(Compare(Name("max"), CmpOp("<=", Name("b"))),
        Assign(Name("max"), Name("b")),
        .Stmts)
      If(Compare(Name("max"), CmpOp("<=", Name("n"))),
        Assign(Name("max"), Name("n")),
        .Stmts)
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "max" <- ?M:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?M ==Int maxInt(maxInt(A, B), N)
    [all-path]
endmodule
