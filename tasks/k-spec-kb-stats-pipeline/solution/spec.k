requires "verification.k"

module KB-STATS-PIPELINE-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): from i = I with I <= N, res = R, t = T, the loop
  //      climbs i to N and adds t once per remaining iteration: res = R + T*(N - I) ----
  claim
    <k>
      #while(Compare(Name("i"), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("t")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "n" <- N:Int ] [ "m" <- M:Int ]
                   [ "x" <- X:Int ] [ "t" <- T:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "m" <- M ]
                   [ "x" <- X ] [ "t" <- T ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I <=Int N
    ensures ?I2 ==Int N
    andBool ?R2 ==Int R +Int T *Int (N -Int I)
    [all-path]

  // ---- Entry claim: min/max of a, b; range t = max - min; the loop accumulates t exactly
  //      n times, then min is added back: res = (max - min)*n + min, for every n = N >= 0 ----
  // KleverBench problems/imp/stats-pipeline:
  //   `if (a <= b) { m = a ; x = b ; } else { m = b ; x = a ; } t = x - m ; res = 0 ; i = 0 ;
  //    while (i < n) { res = res + t ; i = i + 1 ; } res = res + m ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      If(Compare(Name("a"), CmpOp("<=", Name("b"))),
        Assign(Name("m"), Name("a"))
        Assign(Name("x"), Name("b")),
        Assign(Name("m"), Name("b"))
        Assign(Name("x"), Name("a")))
      Assign(Name("t"), BinOp("-", Name("x"), Name("m")))
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("t")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
      Assign(Name("res"), BinOp("+", Name("res"), Name("m")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "m" <- ?M:Int ]
                       [ "x" <- ?X:Int ] [ "t" <- ?T:Int ] [ "res" <- ?RES:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?M ==Int minInt(A, B)
    andBool ?X ==Int maxInt(A, B)
    andBool ?T ==Int maxInt(A, B) -Int minInt(A, B)
    andBool ?I2 ==Int N
    andBool ?RES ==Int (maxInt(A, B) -Int minInt(A, B)) *Int N +Int minInt(A, B)
    [all-path]
endmodule
