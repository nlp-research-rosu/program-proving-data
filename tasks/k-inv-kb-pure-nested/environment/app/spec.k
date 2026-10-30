// Harbor task k-inv-kb-pure-nested — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-PURE-NESTED-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int minInt(B, 0)
    [all-path]
endmodule
