requires "verification.k"

module KB-DOUBLE-HALF-SPEC
  imports MPY-VERIFICATION

  // ---- Entry claim: doubling a then halving lands r exactly back on a, for every int a ----
  // KleverBench problems/imp/double-half: `r = a + a ; r = r / 2 ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("r"), BinOp("+", Name("a"), Name("a")))
      Assign(Name("r"), BinOp("//", Name("r"), Int(2)))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "r" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R ==Int A
    [all-path]
endmodule
