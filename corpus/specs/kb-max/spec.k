requires "verification.k"

module KB-MAX-SPEC
  imports KB-MAX-VERIFICATION

  // ---- Entry claim: after the branch, max holds the maximum of a and b, for all ints a, b ----
  // KleverBench problems/imp/max: `if (a <= b) { max = b ; } else { max = a ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      If(Compare(Name("a"), CmpOp("<=", Name("b"))),
        Assign(Name("max"), Name("b")),
        Assign(Name("max"), Name("a")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "max" <- ?M:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?M ==Int maxInt(A, B)
    [all-path]
endmodule
