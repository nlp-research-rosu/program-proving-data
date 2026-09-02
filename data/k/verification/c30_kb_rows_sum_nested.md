# verification/kb-rows-sum-nested — **PROVED**

```python
sum = 0
i = a
while 0 < i:
    j = b
    while 0 < j:
        sum = sum + j
        j = j - 1
    i = i - 1
```

- requires: `a >= 1`
- ensures: `2*sum == a * maxInt(b,0)*(maxInt(b,0)+1) (a rows, each summing b..1), i == 0, j == minInt(b, 0)`
- invariant @ inner #while circularity: `j = J >= 1 => 0, 2*sum += J*(J+1); a, b, i unchanged` (inner row-sum summary, guard-true side)
- invariant @ outer #while circularity (b >= 1 side): `i = I >= 1 => 0, j => 0, 2*sum += I*b*(b+1)` (outer circularity where rows are nonempty)
- invariant @ outer #while circularity (b <= 0 side): `i = I >= 1 => 0, j => b, sum unchanged` (outer circularity where every row is empty)

Prover: kprove (K haskell backend + z3) — **#Top** in 19.9s (mem cap 8G (systemd-run scope))

Row sums: the ensures is stated in the division-free form 2*sum == a*max(b,0)*(max(b,0)+1) (which pins sum exactly), and the outer loop needs TWO circularities — one for the b >= 1 side and one for the empty-row b <= 0 side — since a single piecewise form left z3 in a nonlinear div context.

Ported from KleverBench [`problems/imp/rows-sum-nested`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `sum = 0 ; i = a ; while (0 < i) { j = b ; while (0 < j) { sum = sum + j ; j = j - 1 ; } i = i - 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-ROWS-SUM-NESTED-SPEC
  imports KB-ROWS-SUM-NESTED-VERIFICATION

  // ---- Inner-loop invariant (circularity): from j = J >= 1, sum = S, the inner loop adds
  //      J + (J-1) + ... + 1 = J*(J+1)/2 into sum and drains j to 0; a, b, i are untouched.
  //      Total over every state the outer body creates on the b >= 1 side (i, sum arbitrary);
  //      on the b <= 0 side the inner guard is refuted outright and no summary is needed.
  //      The sum ensures is stated doubled (2*?S2 = 2*S + J*(J+1), same exact value) so no
  //      /Int cluster ever enters the symbolic state — z3's default budget cannot decide
  //      side conditions once truncated-div terms pile up in the path condition ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("j")))
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "sum" <- S:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "sum" <- ?S2:Int ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires J >=Int 1
    ensures ?J2 ==Int 0
    andBool 2 *Int ?S2 ==Int 2 *Int S +Int J *Int (J +Int 1)
    [all-path]

  // ---- Outer-loop invariant (circularity, b >= 1 side): from i = I >= 1, each iteration
  //      re-seeds j = b and the inner loop adds the row sum b*(b+1)/2, so i drains to 0,
  //      j is left drained at 0, and sum gains I rows of b*(b+1)/2. Stated doubled
  //      (division-free) like the inner claim; the back edge is then a pure polynomial
  //      identity 2S + B(B+1) + (I-1)*B(B+1) = 2S + I*B(B+1) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("sum"), BinOp("+", Name("sum"), Name("j")))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "sum" <- S:Int ] [ "i" <- I:Int ] [ "j" <- _J0:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "sum" <- ?S2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1 andBool B >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool 2 *Int ?S2 ==Int 2 *Int S +Int I *Int (B *Int (B +Int 1))
    [all-path]

  // ---- Outer-loop invariant (circularity, b <= 0 side): every row is empty — the inner
  //      guard 0 < j is false at j = b, so each iteration only re-seeds j = b and decrements
  //      i; sum is untouched, i drains to 0, j ends at b ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("sum"), BinOp("+", Name("sum"), Name("j")))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "sum" <- S:Int ] [ "i" <- I:Int ] [ "j" <- _J0:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "sum" <- ?S2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1 andBool B <=Int 0
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int B
    andBool ?S2 ==Int S
    [all-path]

  // ---- Entry claim: a rows, each summing b..1 — for a >= 1 the program terminates with
  //      sum = a * tri(max(b,0)) = a * (max(b,0)*(max(b,0)+1)/2), i = 0, j = min(b,0).
  //      The sum ensures is stated doubled (2*sum = a*max(b,0)*(max(b,0)+1) — the same
  //      unique integer value: max(b,0)*(max(b,0)+1) is even): with a /Int 2 cluster in the
  //      target, z3 answers unknown on the trivially-sat side conditions kore poses while
  //      evaluating minInt/maxInt (mod+div+nonlinear = "incomplete (theory arithmetic)"),
  //      and kore treats that unknown as a hard error. Division-free, every query decides ----
  // KleverBench problems/imp/rows-sum-nested:
  //   `sum = 0 ; i = a ;
  //    while (0 < i) { j = b ; while (0 < j) { sum = sum + j ; j = j - 1 ; } i = i - 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("sum"), Int(0))
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("sum"), BinOp("+", Name("sum"), Name("j")))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "sum" <- ?SUM:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1
    ensures 2 *Int ?SUM ==Int A *Int (maxInt(B, 0) *Int (maxInt(B, 0) +Int 1))
    andBool ?I2 ==Int 0
    andBool ?J2 ==Int minInt(B, 0)
    [all-path]
endmodule
```
