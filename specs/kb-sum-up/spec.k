requires "verification.k"

module KB-SUM-UP-SPEC
  imports KB-SUM-UP-VERIFICATION

  // ---- Loop invariant (circularity): from i = I with 1 <= I <= N+1 and sum = S, the loop
  //      climbs i to N+1 and adds the remaining sum I + (I+1) + ... + N
  //      = (N*(N+1) - I*(I-1))/2 into sum ----
  claim
    <k>
      #while(Compare(Name("i"), CmpOp("<=", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("i")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "sum" <- S:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "sum" <- ?S2:Int ] [ "i" <- ?I2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1 andBool I <=Int N +Int 1
    ensures ?I2 ==Int N +Int 1
    andBool ?S2 ==Int S +Int ((N *Int (N +Int 1)) -Int (I *Int (I -Int 1))) /Int 2
    [all-path]

  // ---- Entry claim: for every n = N >= 0, the loop terminates with
  //      sum == N*(N+1)/2 and i == N+1 ----
  // KleverBench problems/imp/sum-up: `sum = 0 ; i = 1 ; while (i <= n) { sum = sum + i ; i = i + 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("sum"), Int(0))
      Assign(Name("i"), Int(1))
      While(Compare(Name("i"), CmpOp("<=", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("i")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "sum" <- ?S2:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?S2 ==Int (N *Int (N +Int 1)) /Int 2
    andBool ?I2 ==Int N +Int 1
    [all-path]
endmodule
