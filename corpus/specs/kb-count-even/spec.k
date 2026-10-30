requires "verification.k"

module KB-COUNT-EVEN-SPEC
  imports KB-COUNT-EVEN-VERIFICATION

  // ---- Loop invariant (circularity): from i = I with 0 <= I <= N, the loop counts the
  // ---- evens in I..N-1 on top of C — count gains (N+1)/2 - (I+1)/2 — and i climbs to N ----
  claim
    <k>
      #while(Compare(Name("i"), CmpOp("<", Name("n"))),
        If(Compare(BinOp("%", Name("i"), Int(2)), CmpOp("==", Int(0))),
          Assign(Name("count"), BinOp("+", Name("count"), Int(1))),
          .Stmts)
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "count" <- C:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "count" <- ?C2:Int ] [ "i" <- ?I2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 0 andBool I <=Int N
    ensures ?C2 ==Int C +Int ((N +Int 1) /Int 2) -Int ((I +Int 1) /Int 2)
    andBool ?I2 ==Int N
    [all-path]

  // ---- Entry claim: for every n >= 0, count = (n+1)/2 (the evens in 0..n-1) and i = n ----
  // KleverBench problems/imp/count-even:
  //   `count = 0 ; i = 0 ;
  //    while (i < n) { if (i % 2 == 0) { count = count + 1 ; } else { } i = i + 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("count"), Int(0))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        If(Compare(BinOp("%", Name("i"), Int(2)), CmpOp("==", Int(0))),
          Assign(Name("count"), BinOp("+", Name("count"), Int(1))),
          .Stmts)
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "count" <- ?C2:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?C2 ==Int (N +Int 1) /Int 2
    andBool ?I2 ==Int N
    [all-path]
endmodule
