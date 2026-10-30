// Harbor task k-inv-range-loop — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module RANGE-LOOP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      FuncDef("f", Params("n"),
        Assign(Name("total"), Int(0))
        Assign(Name("i"), Int(0))
        For(Name("i"), Call(Name("range"), Name("n")),
          AugAssign(Name("total"), "+", Name("i")))
        Return(Name("total")))
      Assign(Name("result"), Call(Name("f"), N:Int))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "f" <- ?_:Val ] [ "result" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?R ==Int (N *Int (N -Int 1)) /Int 2
    [all-path]
endmodule
