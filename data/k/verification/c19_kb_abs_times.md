# verification/kb-abs-times — **PROVED**

```python
if a < 0:
    t = 0 - a
else:
    t = a
res = t * b
```

- requires: `True (any ints a, b)`
- ensures: `t == absInt(a) and res == absInt(a) * b; a, b unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 10.1s (mem cap 8G (systemd-run scope))

Branch feeding a nonlinear multiply: both the intermediate t and the product res are pinned exactly (absInt hook).

Ported from KleverBench [`problems/imp/abs-times`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `if (a < 0) { t = 0 - a ; } else { t = a ; } res = t * b ;`

## K claims (verbatim)

```k
requires "verification.k"

module KB-ABS-TIMES-SPEC
  imports KB-ABS-TIMES-VERIFICATION

  // ---- Entry claim: t ends as |a| and res as |a| * b, for every ints a, b ----
  // KleverBench problems/imp/abs-times:
  //   `if (a < 0) { t = 0 - a ; } else { t = a ; } res = t * b ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      If(Compare(Name("a"), CmpOp("<", Int(0))),
        Assign(Name("t"), BinOp("-", Int(0), Name("a"))),
        Assign(Name("t"), Name("a")))
      Assign(Name("res"), BinOp("*", Name("t"), Name("b")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "t" <- ?T:Int ] [ "res" <- ?RES:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?T ==Int absInt(A) andBool ?RES ==Int absInt(A) *Int B
    [all-path]
endmodule
```
