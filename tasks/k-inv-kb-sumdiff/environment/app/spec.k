// Harbor task k-inv-kb-sumdiff — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-SUMDIFF-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      If(Compare(Name("a"), CmpOp("<", Name("b"))),
        Assign(Name("t"), BinOp("-", Name("b"), Name("a"))),
        Assign(Name("t"), BinOp("-", Name("a"), Name("b"))))
      Assign(Name("res"), Int(0))
      While(Compare(Int(0), CmpOp("<", Name("t"))),
        Assign(Name("res"), BinOp("+", Name("res"), Int(2)))
        Assign(Name("t"), BinOp("-", Name("t"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "t" <- ?F:Int ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int 0 andBool ?RES ==Int 2 *Int absInt(A -Int B)
    [all-path]
endmodule
