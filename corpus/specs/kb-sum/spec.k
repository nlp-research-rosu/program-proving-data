requires "verification.k"

module KB-SUM-SPEC
  imports KB-SUM-VERIFICATION

  // ---- Loop invariant (circularity): from n = I >= 0, sum = J, the loop drains n to 0
  //      and adds the remaining triangular sum I + (I-1) + ... + 1 = I*(I+1)/2 into sum ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("n")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ] [ "sum" <- J:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ] [ "sum" <- ?S2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 0
    ensures ?F ==Int 0
    andBool ?S2 ==Int J +Int (I *Int (I +Int 1)) /Int 2
    [all-path]

  // ---- Entry claim: for every n = N >= 0 and arbitrary initial sum = S, the loop
  //      terminates with n == 0 and sum == S + N*(N+1)/2 ----
  // KleverBench problems/imp/sum: `while (!(n <= 0)) { sum = sum + n ; n = n + -1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("sum"), S:Int)
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("n")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- ?F:Int ] [ "sum" <- ?S2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?F ==Int 0
    andBool ?S2 ==Int S +Int (N *Int (N +Int 1)) /Int 2
    [all-path]
endmodule
