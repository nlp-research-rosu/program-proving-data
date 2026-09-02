requires "verification.k"

module KB-MULT-NESTED-SPEC
  imports KB-MULT-NESTED-VERIFICATION

  // ---- Inner-loop invariant (circularity): from j = J, res = R, the loop adds 1 exactly
  //      max(J,0) times and drains j to min(J,0); a no-op when J <= 0. Total over every
  //      state the outer body creates (i, res arbitrary) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?J2 ==Int minInt(J, 0) andBool ?R2 ==Int R +Int maxInt(J, 0)
    [all-path]

  // ---- Outer-loop invariant (circularity): from i = I >= 1, each iteration re-seeds j = B,
  //      lets the inner loop add max(B,0) into res, and decrements i — so i drains to 0,
  //      j ends at min(B,0), and res gains I*max(B,0) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- _J0:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1
    ensures ?I2 ==Int 0 andBool ?J2 ==Int minInt(B, 0) andBool ?R2 ==Int R +Int I *Int maxInt(B, 0)
    [all-path]

  // ---- Entry claim: multiplication by nested repeated addition — for a >= 1 the program
  //      terminates with res = a*max(b,0), i = 0, j = min(b,0) ----
  // KleverBench problems/imp/mult-nested:
  //   `res = 0 ; i = a ;
  //    while (0 < i) { j = b ; while (0 < j) { res = res + 1 ; j = j - 1 ; } i = i - 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?RES:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1
    ensures ?I2 ==Int 0 andBool ?J2 ==Int minInt(B, 0) andBool ?RES ==Int A *Int maxInt(B, 0)
    [all-path]
endmodule
