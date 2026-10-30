// Harbor task k-inv-kb-stats-pipeline — see instruction.md.
// Claim module for program.py over the klever MPY semantics (MPY-VERIFICATION).
requires "verification.k"

module KB-STATS-PIPELINE-SPEC
  imports MPY-VERIFICATION

  // ---- Loop-invariant (circularity) claims go here, one per loop level ----

  // ---- Entry claim (frozen) ----
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      If(Compare(Name("a"), CmpOp("<=", Name("b"))),
        Assign(Name("m"), Name("a"))
        Assign(Name("x"), Name("b")),
        Assign(Name("m"), Name("b"))
        Assign(Name("x"), Name("a")))
      Assign(Name("t"), BinOp("-", Name("x"), Name("m")))
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("t")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
      Assign(Name("res"), BinOp("+", Name("res"), Name("m")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "m" <- ?M:Int ]
                       [ "x" <- ?X:Int ] [ "t" <- ?T:Int ] [ "res" <- ?RES:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?M ==Int minInt(A, B)
    andBool ?X ==Int maxInt(A, B)
    andBool ?T ==Int maxInt(A, B) -Int minInt(A, B)
    andBool ?I2 ==Int N
    andBool ?RES ==Int (maxInt(A, B) -Int minInt(A, B)) *Int N +Int minInt(A, B)
    [all-path]
endmodule
