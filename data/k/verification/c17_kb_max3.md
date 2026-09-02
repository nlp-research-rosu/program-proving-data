# verification/kb-max3 — **PROVED**

```python
max = a
if max <= b:
    max = b
if max <= n:
    max = n
```

- requires: `True (any ints a, b, n)`
- ensures: `max == maxInt(maxInt(a, b), n); a, b, n unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 10.6s (mem cap 8G (systemd-run scope))

Two sequential branches; the prover's 4-way case split collapses into the nested maxInt closed form.

Ported from KleverBench [`problems/imp/max3`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `max = a ; if (max <= b) { max = b ; } else { } if (max <= n) { max = n ; } else { }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-MAX3-SPEC
  imports KB-MAX3-VERIFICATION

  // ---- Entry claim: after the two branches, max holds the maximum of a, b, n, for all ints ----
  // KleverBench problems/imp/max3:
  //   `max = a ; if (max <= b) { max = b ; } else { } if (max <= n) { max = n ; } else { }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("n"), N:Int)
      Assign(Name("max"), Name("a"))
      If(Compare(Name("max"), CmpOp("<=", Name("b"))),
        Assign(Name("max"), Name("b")),
        .Stmts)
      If(Compare(Name("max"), CmpOp("<=", Name("n"))),
        Assign(Name("max"), Name("n")),
        .Stmts)
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "n" <- N ] [ "max" <- ?M:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?M ==Int maxInt(maxInt(A, B), N)
    [all-path]
endmodule
```
