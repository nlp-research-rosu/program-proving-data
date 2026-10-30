// Harbor task k-spec-kb-pipeline — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-PIPELINE-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level, if the
  //      program has loops ----

  // ---- Entry claim: frozen except the FINAL-SCOPE and ENSURES placeholders ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      Assign(Name("t"), BinOp("*", Name("a"), Name("b")))
      If(Compare(Name("t"), CmpOp("<", Int(0))),
        Assign(Name("t"), BinOp("-", Int(0), Name("t"))),
        .Stmts)
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("t")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
      Assign(Name("res"), BinOp("+", Name("res"), Name("a")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(/* FINAL-SCOPE: .Map [ "x" <- TERM ] [ "y" <- TERM ] ... */, parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    /* ENSURES: `ensures COND` pinning every ?-variable, or delete this comment */
    [all-path]
endmodule
