requires "verification.k"

module KB-CLAMP-SPEC
  imports MPY-VERIFICATION

  // ---- Entry claim: res ends clamped into [0, 10], i.e. min(max(a, 0), 10), for every int a ----
  // KleverBench problems/imp/clamp:
  //   `if (a < 0) { res = 0 ; } else { if (10 < a) { res = 10 ; } else { res = a ; } }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      If(Compare(Name("a"), CmpOp("<", Int(0))),
        Assign(Name("res"), Int(0)),
        If(Compare(Int(10), CmpOp("<", Name("a"))),
          Assign(Name("res"), Int(10)),
          Assign(Name("res"), Name("a"))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?RES ==Int minInt(maxInt(A, 0), 10)
    [all-path]
endmodule
