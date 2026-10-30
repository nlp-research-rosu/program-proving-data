// Harbor task k-inv-kb-nested-with-branch — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-NESTED-WITH-BRANCH-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
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
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1 andBool B >=Int 1
    ensures ?R2 ==Int (minInt(A, B) *Int (minInt(A, B) +Int 1)) /Int 2
    andBool ?I2 ==Int 0
    andBool ?J2 ==Int 0
    [all-path]
endmodule
