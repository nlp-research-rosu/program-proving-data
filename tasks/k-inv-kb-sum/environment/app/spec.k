// Harbor task k-inv-kb-sum — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-SUM-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("sum"), S:Int)
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("n")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- ?F:Int ] [ "sum" <- ?S2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?F ==Int 0
    andBool ?S2 ==Int S +Int (N *Int (N +Int 1)) /Int 2
    [all-path]
endmodule
