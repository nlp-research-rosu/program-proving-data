requires "verification.k"

module KB-ABS-SPEC
  imports KB-ABS-VERIFICATION

  // ---- Entry claim: res ends as |a|, for every int a ----
  // KleverBench problems/imp/abs: `if (a < 0) { res = 0 - a ; } else { res = a ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      If(Compare(Name("a"), CmpOp("<", Int(0))),
        Assign(Name("res"), BinOp("-", Int(0), Name("a"))),
        Assign(Name("res"), Name("a")))
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
    ensures ?RES ==Int absInt(A)
    [all-path]
endmodule
