requires "verification.k"

module KB-TRIANGLE-NESTED-SPEC
  imports KB-TRIANGLE-NESTED-VERIFICATION

  // ---- Inner-loop invariant (circularity, total): from j = J, count = C, the inner loop
  //      adds max(J,0) to count and drains j to min(J,0) (no-op when J <= 0);
  //      i and n are untouched ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("count"), BinOp("+", Name("count"), Int(1)))
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "count" <- C:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "count" <- ?C2:Int ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?J2 ==Int minInt(J, 0)
    andBool ?C2 ==Int C +Int maxInt(J, 0)
    [all-path]

  // ---- Outer-loop invariant (circularity): from i = I with I >= 1, count = C, each outer
  //      iteration lets the inner loop add i to count, so count gains I + (I-1) + ... + 1
  //      = I*(I+1)/2 while i drains to 0 and j is left drained at 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("i"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("count"), BinOp("+", Name("count"), Int(1)))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "count" <- C:Int ] [ "i" <- I:Int ] [ "j" <- _:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "count" <- ?C2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool ?C2 ==Int C +Int (I *Int (I +Int 1)) /Int 2
    [all-path]

  // ---- Entry claim: for every n = N >= 1, the nested loops terminate with the triangular
  //      count == N*(N+1)/2 and both counters drained: i == 0 and j == 0 ----
  // KleverBench problems/imp/triangle-nested:
  //   `count = 0 ; i = n ;
  //    while (0 < i) { j = i ; while (0 < j) { count = count + 1 ; j = j - 1 ; } i = i - 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("count"), Int(0))
      Assign(Name("i"), Name("n"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("i"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("count"), BinOp("+", Name("count"), Int(1)))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "count" <- ?C2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 1
    ensures ?C2 ==Int (N *Int (N +Int 1)) /Int 2
    andBool ?I2 ==Int 0
    andBool ?J2 ==Int 0
    [all-path]
endmodule
