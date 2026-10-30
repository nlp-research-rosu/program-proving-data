requires "verification.k"

module KB-MULT-LOOP-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): from n = I, res = S, the loop adds a exactly max(I,0)
  //      times and drains n to min(I,0); a no-op when I <= 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("a")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ] [ "a" <- A:Int ] [ "res" <- S:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ] [ "a" <- A ] [ "res" <- ?S2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(I, 0) andBool ?S2 ==Int S +Int A *Int maxInt(I, 0)
    [all-path]

  // ---- Entry claim: multiplication by repeated addition — for arbitrary ints n, a the
  //      program terminates with res = a*max(n0,0) and n = min(n0,0) ----
  // KleverBench problems/imp/mult-loop: `res = 0 ; while (0 < n) { res = res + a ; n = n - 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("a"), A:Int)
      Assign(Name("res"), Int(0))
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
      0 |-> scope(.Map [ "n" <- ?F:Int ] [ "a" <- A ] [ "res" <- ?S2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(N, 0) andBool ?S2 ==Int A *Int maxInt(N, 0)
    [all-path]
endmodule
