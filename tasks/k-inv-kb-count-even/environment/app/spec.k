// Harbor task k-inv-kb-count-even — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-COUNT-EVEN-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("count"), Int(0))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        If(Compare(BinOp("%", Name("i"), Int(2)), CmpOp("==", Int(0))),
          Assign(Name("count"), BinOp("+", Name("count"), Int(1))),
          .Stmts)
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "count" <- ?C2:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?C2 ==Int (N +Int 1) /Int 2
    andBool ?I2 ==Int N
    [all-path]
endmodule
