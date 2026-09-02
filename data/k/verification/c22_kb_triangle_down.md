# verification/kb-triangle-down — **PROVED**

```python
sum = 0
while 0 < n:
    sum = sum + n
    n = n - 1
```

- requires: `True (any int n)`
- ensures: `sum == maxInt(n, 0)*(maxInt(n, 0)+1)/2 (the triangle number of max(n,0); no-op for n <= 0), n == minInt(n, 0)`
- invariant @ while-loop head (#while circularity claim): `from n = I, sum = S: the loop ends with n == minInt(I, 0), sum == S + maxInt(I, 0)*(maxInt(I, 0)+1)/2` (circularity claim, total over all I)

Prover: kprove (K haskell backend + z3) — **#Top** in 8.9s (mem cap 8G (systemd-run scope))

c14's Gauss form with NO precondition: the piecewise maxInt/minInt closed form absorbs the no-op branch, and z3 still discharges the nonlinear /Int 2 triangle algebra unaided. The dead initial sum binding of the IMP source is dropped (the program seeds sum = 0 itself).

Ported from KleverBench [`problems/imp/triangle-down`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `sum = 0 ; while (0 < n) { sum = sum + n ; n = n - 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-TRIANGLE-DOWN-SPEC
  imports KB-TRIANGLE-DOWN-VERIFICATION

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
    ensures ?F ==Int minInt(I, 0)
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
      0 |-> scope(.Map [ "n" <- minInt(N, 0) ] [ "sum" <- ?T:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?T ==Int (maxInt(N, 0) *Int (maxInt(N, 0) +Int 1)) /Int 2
    [all-path]
endmodule
```
