# verification/kb-arith-mix — **PROVED**

```python
res = a * b + a - b
```

- requires: `True (any ints a, b)`
- ensures: `res == a*b + a - b; a and b unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 8.2s (mem cap 8G (systemd-run scope))

Nonlinear closed form (a*b over two symbolic ints) pinned exactly; no arithmetic lemmas needed.

Ported from KleverBench [`problems/imp/arith-mix`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `res = a * b + a - b ;`

## K claims (verbatim)

```k
requires "verification.k"

module KB-ARITH-MIX-SPEC
  imports KB-ARITH-MIX-VERIFICATION

  // ---- Entry claim: res ends as a*b + a - b, a and b unchanged, for all ints a, b ----
  // KleverBench problems/imp/arith-mix: `res = a * b + a - b ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(
        Name("res"),
        BinOp(
          "-",
          BinOp("+", BinOp("*", Name("a"), Name("b")), Name("a")),
          Name("b")))
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
    ensures ?R ==Int (A *Int B) +Int A -Int B
    [all-path]
endmodule
```
