requires "verification.k"

module BUGGY-ABS-SPEC
  imports BUGGY-ABS-VERIFICATION

  // ---- Same absolute-value spec, over the buggy implementation (no x == 0
  // case: control falls off the body and returns None). EXPECTED: REFUTED —
  // the prover gets stuck at the fall-through state, whose path condition
  // yields the counterexample x == 0. ----
  claim
    <k>
      FuncDef("buggy_abs", Params("x"),
        If(Compare(Name("x"), CmpOp("<", Int(0))),
          Return(UnaryOp("-", Name("x"))),
          If(Compare(Name("x"), CmpOp(">", Int(0))),
            Return(Name("x")),
            .Stmts)))
      Assign(Name("result"), Call(Name("buggy_abs"), X:Int))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "buggy_abs" <- ?_:Val ] [ "result" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures (?R >=Int 0)
      andBool ((?R ==Int X) orBool (?R ==Int (0 -Int X)))
    [all-path]
endmodule
