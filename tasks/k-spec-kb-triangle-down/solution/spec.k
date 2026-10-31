requires "verification.k"

module KB-TRIANGLE-DOWN-SPEC
  imports MPY-VERIFICATION

  // ---- Loop invariant (circularity): from n = I, sum = S, the loop adds the triangle
  //      number of max(I,0) to sum and drains n to min(I,0) (no-op when I <= 0) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("n")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ] [ "sum" <- S:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ] [ "sum" <- ?T:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int (I -Int maxInt(I, 0))
    andBool ?T ==Int S +Int (maxInt(I, 0) *Int (maxInt(I, 0) +Int 1)) /Int 2
    [all-path]

  // ---- Entry claim: sum n..1 (no-op for n <= 0):
  //      sum = max(n,0)*(max(n,0)+1)/2, n ends at min(n,0), for arbitrary int n ----
  // KleverBench problems/imp/triangle-down:
  //   `sum = 0 ; while (0 < n) { sum = sum + n ; n = n - 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("sum"), Int(0))
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("n")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- (N -Int maxInt(N, 0)) ] [ "sum" <- ?T:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?T ==Int (maxInt(N, 0) *Int (maxInt(N, 0) +Int 1)) /Int 2
    [all-path]
endmodule
