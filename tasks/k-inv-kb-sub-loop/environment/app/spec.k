// Harbor task k-inv-kb-sub-loop — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-SUB-LOOP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      While(Compare(Int(0), CmpOp("<", Name("b"))),
        Assign(Name("a"), BinOp("-", Name("a"), Int(1)))
        Assign(Name("b"), BinOp("-", Name("b"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- ?F:Int ] [ "b" <- ?G:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int A -Int maxInt(B, 0) andBool ?G ==Int minInt(B, 0)
    [all-path]
endmodule
