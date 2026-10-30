# verification/kb-assign — **PROVED**

```python
b = a + 4
```

- requires: `True (any int a)`
- ensures: `b == a + 4 and a unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 6.8s (mem cap 8G (systemd-run scope))

Straight-line full characterization: the final scope pins both bindings exactly (a unchanged, b = a + 4).

Ported from KleverBench [`problems/imp/assign`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `b = a + 4 ;`

## K claims (verbatim)

```k
requires "verification.k"

module KB-ASSIGN-SPEC
  imports KB-ASSIGN-VERIFICATION

  // ---- Entry claim: after b = a + 4, b holds a + 4 and a is unchanged, for every int a ----
  // KleverBench problems/imp/assign: `b = a + 4 ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), BinOp("+", Name("a"), Int(4)))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- ?B:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?B ==Int A +Int 4
    [all-path]
endmodule
```
