// Harbor task k-inv-kb-add-loop — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-ADD-LOOP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("res"), R:Int)
      Assign(Name("a"), A:Int)
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("a")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- ?F:Int ] [ "res" <- ?S2:Int ] [ "a" <- A ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(N, 0) andBool ?S2 ==Int R +Int A *Int maxInt(N, 0)
    [all-path]
endmodule
