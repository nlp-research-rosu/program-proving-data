requires "verification.k"

module KB-MIN-SPEC
  imports MPY-VERIFICATION

  // ---- Entry claim: res ends as min(a, b), for all ints a, b ----
  // KleverBench problems/imp/min: `if (a <= b) { res = a ; } else { res = b ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      If(Compare(Name("a"), CmpOp("<=", Name("b"))),
        Assign(Name("res"), Name("a")),
        Assign(Name("res"), Name("b")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R ==Int minInt(A, B)
    [all-path]
endmodule
