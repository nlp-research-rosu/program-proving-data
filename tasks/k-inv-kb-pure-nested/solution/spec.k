requires "verification.k"

module KB-PURE-NESTED-SPEC
  imports MPY-VERIFICATION

  // ---- Inner-loop invariant (circularity): from j = J the countdown drains j to min(J, 0)
  //      and touches nothing else — total (no requires): every outer iteration re-enters it
  //      with fresh i and j = b, so it must hold for arbitrary I and J ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?J2 ==Int minInt(J, 0)
    [all-path]

  // ---- Outer-loop invariant (circularity): from i = I with I >= 1 the outer countdown runs
  //      at least once — each iteration resets j to b and drains it (inner claim summarizes
  //      the inner While) — so i falls to 0 and j ends min(B, 0) regardless of its old value;
  //      the back-edge boundary i = 0 is discharged by one extra unfold ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "i" <- I:Int ] [ "j" <- _J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int minInt(B, 0)
    [all-path]

  // ---- Entry claim: for every a >= 1 the nested countdowns terminate with i = 0 and
  //      j = min(b, 0) — no accumulation, the loops only drain ----
  // KleverBench problems/imp/pure-nested:
  //   `i = a ; while (0 < i) { j = b ; while (0 < j) { j = j - 1 ; } i = i - 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int minInt(B, 0)
    [all-path]
endmodule
