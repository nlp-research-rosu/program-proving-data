// Harbor task k-inv-kb-triangle-nested — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-TRIANGLE-NESTED-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
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
