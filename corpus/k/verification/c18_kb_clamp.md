# verification/kb-clamp — **PROVED**

```python
if a < 0:
    res = 0
else:
    if 10 < a:
        res = 10
    else:
        res = a
```

- requires: `True (any int a)`
- ensures: `res == minInt(maxInt(a, 0), 10) (a clamped to [0, 10]); a unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 8.8s (mem cap 8G (systemd-run scope))

Nested branches; the three-way split collapses into the composed minInt/maxInt clamp form.

Ported from KleverBench [`problems/imp/clamp`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `if (a < 0) { res = 0 ; } else { if (10 < a) { res = 10 ; } else { res = a ; } }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-CLAMP-SPEC
  imports KB-CLAMP-VERIFICATION

  // ---- Entry claim: res ends clamped into [0, 10], i.e. min(max(a, 0), 10), for every int a ----
  // KleverBench problems/imp/clamp:
  //   `if (a < 0) { res = 0 ; } else { if (10 < a) { res = 10 ; } else { res = a ; } }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      If(Compare(Name("a"), CmpOp("<", Int(0))),
        Assign(Name("res"), Int(0)),
        If(Compare(Int(10), CmpOp("<", Name("a"))),
          Assign(Name("res"), Int(10)),
          Assign(Name("res"), Name("a"))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?RES ==Int minInt(maxInt(A, 0), 10)
    [all-path]
endmodule
```
