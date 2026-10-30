# verification/kb-min — **PROVED**

```python
if a <= b:
    res = a
else:
    res = b
```

- requires: `True (any ints a, b)`
- ensures: `res == minInt(a, b); a and b unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 7.4s (mem cap 8G (systemd-run scope))

Branching spec via the minInt hook, dual of c10.

Ported from KleverBench [`problems/imp/min`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `if (a <= b) { res = a ; } else { res = b ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-MIN-SPEC
  imports KB-MIN-VERIFICATION

  // ---- Entry claim: res ends as min(a, b), for all ints a, b ----
  // KleverBench problems/imp/min: `if (a <= b) { res = a ; } else { res = b ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      If(Compare(Name("a"), CmpOp("<=", Name("b"))),
        Assign(Name("res"), Name("a")),
        Assign(Name("res"), Name("b")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R ==Int minInt(A, B)
    [all-path]
endmodule
```
