# verification/kb-loop-max — **PROVED**

```python
max = a
i = 0
while i < n:
    if max < i:
        max = i
    i = i + 1
```

- requires: `n >= 1`
- ensures: `max == maxInt(a, n-1) (fold of max over 0..n-1 seeded with a) and i == n; a, n unchanged`
- invariant @ while-loop head (#while circularity claim): `i == I <= n-1, max = M; the loop ends with i == n and max == maxInt(M, n-1)` (circularity claim — folding max over the nonempty range I..n-1 yields maxInt(M, n-1))

Prover: kprove (K haskell backend + z3) — **#Top** in 10.5s (mem cap 8G (systemd-run scope))

Running maximum with a branch in the body: the circularity holds for i <= n-1 (guard true); the back edge landing on i == n is discharged by one extra unfold that exits, so a single circularity suffices. requires is the intent's n >= 1.

Ported from KleverBench [`problems/imp/loop-max`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `max = a ; i = 0 ; while (i < n) { if (max < i) { max = i ; } else { } i = i + 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-LOOP-MAX-SPEC
  imports KB-LOOP-MAX-VERIFICATION

  // ---- Loop invariant (circularity): from i = I with I <= N-1, the loop folds max over
  // ---- I..N-1 on top of M — since I..N-1 is nonempty its max is N-1 — and i climbs to N ----
  claim
    <k>
      #while(Compare(Name("i"), CmpOp("<", Name("n"))),
        If(Compare(Name("max"), CmpOp("<", Name("i"))),
          Assign(Name("max"), Name("i")),
          .Stmts)
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "n" <- N:Int ] [ "max" <- M:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "n" <- N ] [ "max" <- ?M2:Int ] [ "i" <- ?I2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I <=Int N -Int 1
    ensures ?M2 ==Int maxInt(M, N -Int 1)
    andBool ?I2 ==Int N
    [all-path]

  // ---- Entry claim: for every n >= 1, max = max(a, n-1) (a folded with 0..n-1) and i = n ----
  // KleverBench problems/imp/loop-max:
  //   `max = a ; i = 0 ;
  //    while (i < n) { if (max < i) { max = i ; } else { } i = i + 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("n"), N:Int)
      Assign(Name("max"), Name("a"))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        If(Compare(Name("max"), CmpOp("<", Name("i"))),
          Assign(Name("max"), Name("i")),
          .Stmts)
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "n" <- N ] [ "max" <- ?M2:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 1
    ensures ?M2 ==Int maxInt(A, N -Int 1)
    andBool ?I2 ==Int N
    [all-path]
endmodule
```
