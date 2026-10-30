# verification/kb-sum — **PROVED**

```python
while 0 < n:
    sum = sum + n
    n = n - 1
```

- requires: `n >= 0`
- ensures: `n == 0 and sum == sum0 + n*(n+1)/2 (the triangular sum added into an arbitrary initial sum0)`
- invariant @ while-loop head (#while circularity claim): `n = I >= 0, sum = J; the remaining iterations end with n == 0 and sum == J + I*(I+1)/2` (circularity claim — closed form of the remaining triangular sum; the back edge re-establishes it at I - 1 with J + I accumulated)

Prover: kprove (K haskell backend + z3) — **#Top** in 8.9s (mem cap 8G (systemd-run scope))

The Gauss benchmark: the circularity's closed form carries the division by 2 (z3 discharges the floored /Int algebra, as in the vendored range-loop proof); requires is exactly the intent's n >= 0, sum fully arbitrary.

Ported from KleverBench [`problems/imp/sum`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `while (!(n <= 0)) { sum = sum + n ; n = n + -1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-SUM-SPEC
  imports KB-SUM-VERIFICATION

  // ---- Loop invariant (circularity): from n = I >= 0, sum = J, the loop drains n to 0
  //      and adds the remaining triangular sum I + (I-1) + ... + 1 = I*(I+1)/2 into sum ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("sum"), BinOp("+", Name("sum"), Name("n")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ] [ "sum" <- J:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ] [ "sum" <- ?S2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 0
    ensures ?F ==Int 0
    andBool ?S2 ==Int J +Int (I *Int (I +Int 1)) /Int 2
    [all-path]

  // ---- Entry claim: for every n = N >= 0 and arbitrary initial sum = S, the loop
  //      terminates with n == 0 and sum == S + N*(N+1)/2 ----
  // KleverBench problems/imp/sum: `while (!(n <= 0)) { sum = sum + n ; n = n + -1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("sum"), S:Int)
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
      0 |-> scope(.Map [ "n" <- ?F:Int ] [ "sum" <- ?S2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?F ==Int 0
    andBool ?S2 ==Int S +Int (N *Int (N +Int 1)) /Int 2
    [all-path]
endmodule
```
