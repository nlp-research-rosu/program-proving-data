// Harbor task k-spec-kb-min — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-MIN-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level, if the
  //      program has loops ----

  // ---- Entry claim: frozen except the FINAL-SCOPE and ENSURES placeholders ----
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
      0 |-> scope(/* FINAL-SCOPE: .Map [ "x" <- TERM ] [ "y" <- TERM ] ... */, parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    /* ENSURES: `ensures COND` pinning every ?-variable, or delete this comment */
    [all-path]
endmodule
