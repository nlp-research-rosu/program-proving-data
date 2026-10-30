requires "verification.k"

module KB-ASSIGN-SPEC
  imports MPY-VERIFICATION

  // ---- Entry claim: after b = a + 4, b holds a + 4 and a is unchanged, for every int a ----
  // KleverBench problems/imp/assign: `b = a + 4 ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), BinOp("+", Name("a"), Int(4)))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- ?B:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?B ==Int A +Int 4
    [all-path]
endmodule
