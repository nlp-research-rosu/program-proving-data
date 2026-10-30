// Harbor task k-spec-kb-nested-with-branch — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-NESTED-WITH-BRANCH-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level, if the
  //      program has loops ----

  // ---- Entry claim: frozen except the FINAL-SCOPE and ENSURES placeholders ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        If(Compare(Name("i"), CmpOp("<=", Name("b"))),
          Assign(Name("j"), Name("i"))
          While(Compare(Int(0), CmpOp("<", Name("j"))),
            Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
            Assign(Name("j"), BinOp("-", Name("j"), Int(1)))),
          .Stmts)
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
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
    requires A >=Int 1 andBool B >=Int 1
    /* ENSURES: `ensures COND` pinning every ?-variable, or delete this comment */
    [all-path]
endmodule
