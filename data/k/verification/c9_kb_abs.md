# verification/kb-abs — **PROVED**

```python
if a < 0:
    res = 0 - a
else:
    res = a
```

- requires: `True (any int a)`
- ensures: `res == absInt(a); a unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 7.9s (mem cap 8G (systemd-run scope))

Branching functional spec via the absInt hook, both paths; the IMP shape (if/else assignment, `0 - a`) is kept verbatim, unlike the early-return abs_val of c2.

Ported from KleverBench [`problems/imp/abs`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `if (a < 0) { res = 0 - a ; } else { res = a ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-ABS-SPEC
  imports KB-ABS-VERIFICATION

  // ---- Entry claim: res ends as |a|, for every int a ----
  // KleverBench problems/imp/abs: `if (a < 0) { res = 0 - a ; } else { res = a ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      If(Compare(Name("a"), CmpOp("<", Int(0))),
        Assign(Name("res"), BinOp("-", Int(0), Name("a"))),
        Assign(Name("res"), Name("a")))
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
    ensures ?RES ==Int absInt(A)
    [all-path]
endmodule
```
