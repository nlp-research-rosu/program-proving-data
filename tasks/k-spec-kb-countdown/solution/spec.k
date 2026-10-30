requires "verification.k"

module KB-COUNTDOWN-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): from any n = I >= 0, the countdown loop drains n to 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 0
    ensures ?F ==Int 0
    [all-path]

  // ---- Entry claim: for every n >= 0, the loop terminates with n == 0 ----
  // KleverBench problems/imp/countdown: `while (!(n <= 0)) { n = n + -1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- ?F:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?F ==Int 0
    [all-path]
endmodule
