requires "verification.k"

module KB-SUB-LOOP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): from a = A2, b = I, the loop decrements a exactly
  //      max(I,0) times and drains b to min(I,0); a no-op when I <= 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("b"))),
        Assign(Name("a"), BinOp("-", Name("a"), Int(1)))
        Assign(Name("b"), BinOp("-", Name("b"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A2:Int ] [ "b" <- I:Int ], P:Parent) =>
        scope(.Map [ "a" <- ?F:Int ] [ "b" <- ?G:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int A2 -Int maxInt(I, 0) andBool ?G ==Int minInt(I, 0)
    [all-path]

  // ---- Entry claim: for arbitrary ints a, b the loop terminates with
  //      a = a0 - max(b0,0) and b = min(b0,0) ----
  // KleverBench problems/imp/sub-loop: `while (0 < b) { a = a - 1 ; b = b - 1 ; }`
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
