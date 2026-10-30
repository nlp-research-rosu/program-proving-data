requires "verification.k"

module KB-SUMDIFF-SPEC
  imports KB-SUMDIFF-VERIFICATION

  // ---- Loop invariant (circularity): from t = T, res = R, the loop adds 2 exactly max(T,0)
  //      times and drains t to min(T,0); a no-op when T <= 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("t"))),
        Assign(Name("res"), BinOp("+", Name("res"), Int(2)))
        Assign(Name("t"), BinOp("-", Name("t"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "t" <- T:Int ] [ "res" <- R:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "t" <- ?F:Int ] [ "res" <- ?R2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(T, 0) andBool ?R2 ==Int R +Int 2 *Int maxInt(T, 0)
    [all-path]

  // ---- Entry claim: t ends as |a-b| drained to 0 and res as 2*|a-b|, for arbitrary ints a, b ----
  // KleverBench problems/imp/sumdiff:
  //   `if (a < b) { t = b - a ; } else { t = a - b ; } res = 0 ;
  //    while (0 < t) { res = res + 2 ; t = t - 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      If(Compare(Name("a"), CmpOp("<", Name("b"))),
        Assign(Name("t"), BinOp("-", Name("b"), Name("a"))),
        Assign(Name("t"), BinOp("-", Name("a"), Name("b"))))
      Assign(Name("res"), Int(0))
      While(Compare(Int(0), CmpOp("<", Name("t"))),
        Assign(Name("res"), BinOp("+", Name("res"), Int(2)))
        Assign(Name("t"), BinOp("-", Name("t"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "t" <- ?F:Int ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int 0 andBool ?RES ==Int 2 *Int absInt(A -Int B)
    [all-path]
endmodule
