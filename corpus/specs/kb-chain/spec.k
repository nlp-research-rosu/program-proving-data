requires "verification.k"

module KB-CHAIN-SPEC
  imports KB-CHAIN-VERIFICATION

  // ---- Entry claim: three-step dataflow chain x = a+1, y = 2x, z = y-a, for every int a ----
  // KleverBench problems/imp/chain: `x = a + 1 ; y = x * 2 ; z = y - a ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("x"), BinOp("+", Name("a"), Int(1)))
      Assign(Name("y"), BinOp("*", Name("x"), Int(2)))
      Assign(Name("z"), BinOp("-", Name("y"), Name("a")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "x" <- A +Int 1 ] [ "y" <- (A +Int 1) *Int 2 ] [ "z" <- (A +Int 1) *Int 2 -Int A ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    [all-path]
endmodule
