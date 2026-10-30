// Harbor task k-inv-kb-countup — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-COUNTUP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("r"), R:Int)
      While(Compare(Name("r"), CmpOp("<", Name("n"))),
        Assign(Name("r"), BinOp("+", Name("r"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "r" <- ?R2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R2 ==Int maxInt(N, R)
    [all-path]
endmodule
