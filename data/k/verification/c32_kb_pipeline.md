# verification/kb-pipeline — **PROVED**

```python
t = a * b
if t < 0:
    t = 0 - t
res = 0
i = 0
while i < n:
    res = res + t
    i = i + 1
res = res + a
```

- requires: `n >= 0`
- ensures: `t == absInt(a*b), i == n, and res == absInt(a*b) * n + a`
- invariant @ while-loop head (#while circularity claim): `i = I <= n, res = R; the loop ends with i == n and res == R + t*(n - I) (t frozen)` (circularity claim; z3 discharges the nonlinear t*(n-I) distributivity on the back edge)

Prover: kprove (K haskell backend + z3) — **#Top** in 12.3s (mem cap 8G (systemd-run scope))

Tier-5 pipeline: branch computes t = |a*b|, a loop accumulates it n times, a final adjustment adds a — the branch and epilogue stages are consumed by the entry claim's symbolic execution around one loop circularity, with the intermediate t carried symbolically end to end.

Ported from KleverBench [`problems/imp/pipeline`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `t = a * b ; if (t < 0) { t = 0 - t ; } else { } res = 0 ; i = 0 ; while (i < n) { res = res + t ; i = i + 1 ; } res = res + a ;`

## K claims (verbatim)

```k
requires "verification.k"

module KB-PIPELINE-SPEC
  imports KB-PIPELINE-VERIFICATION

  // ---- Loop invariant (circularity): from i = I with I <= N, res = R and t = T, the loop
  //      adds t exactly N - I times and climbs i to N; t is loop-invariant ----
  claim
    <k>
      #while(Compare(Name("i"), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("t")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "n" <- N:Int ] [ "t" <- T:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "t" <- T ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I <=Int N
    ensures ?R2 ==Int R +Int T *Int (N -Int I)
    andBool ?I2 ==Int N
    [all-path]

  // ---- Entry claim: for every n = N >= 0 and arbitrary ints a, b, the pipeline ends with
  //      t = |a*b|, i = n and res = |a*b| * n + a ----
  // KleverBench problems/imp/pipeline:
  //   `t = a * b ; if (t < 0) { t = 0 - t ; } else { } res = 0 ; i = 0 ;
  //    while (i < n) { res = res + t ; i = i + 1 ; } res = res + a ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      Assign(Name("t"), BinOp("*", Name("a"), Name("b")))
      If(Compare(Name("t"), CmpOp("<", Int(0))),
        Assign(Name("t"), BinOp("-", Int(0), Name("t"))),
        .Stmts)
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Int(0))
      While(Compare(Name("i"), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("t")))
        Assign(Name("i"), BinOp("+", Name("i"), Int(1))))
      Assign(Name("res"), BinOp("+", Name("res"), Name("a")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "t" <- ?T:Int ] [ "res" <- ?RES:Int ] [ "i" <- ?I2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?T ==Int absInt(A *Int B)
    andBool ?I2 ==Int N
    andBool ?RES ==Int absInt(A *Int B) *Int N +Int A
    [all-path]
endmodule
```
