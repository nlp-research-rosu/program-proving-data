// Harbor task k-inv-kb-loop-max — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-LOOP-MAX-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("n"), N:Int)
      Assign(Name("max"), Name("a"))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        If(Compare(Name("max"), CmpOp("<", Name("i"))),
          Assign(Name("max"), Name("i")),
          .Stmts)
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "n" <- N ] [ "max" <- ?M2:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 1
    ensures ?M2 ==Int maxInt(A, N -Int 1)
    andBool ?I2 ==Int N
    [all-path]
endmodule
