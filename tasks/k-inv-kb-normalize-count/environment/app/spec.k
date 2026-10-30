// Harbor task k-inv-kb-normalize-count — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-NORMALIZE-COUNT-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      If(Compare(Name("n"), CmpOp("<", Int(0))),
        Assign(Name("n"), BinOp("-", Int(0), Name("n"))),
        .Stmts)
      Assign(Name("count"), Int(0))
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1)))
        Assign(Name("count"), BinOp("+", Name("count"), Int(1))))
      Assign(Name("res"), BinOp("+", BinOp("*", Name("count"), Name("a")), Name("b")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- ?F:Int ] [ "count" <- ?C2:Int ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int 0
    andBool ?C2 ==Int absInt(N)
    andBool ?RES ==Int absInt(N) *Int A +Int B
    [all-path]
endmodule
