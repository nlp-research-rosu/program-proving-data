# verification/kb-swap — **PROVED**

```python
r = a
a = b
b = r
```

- requires: `True (any ints a, b)`
- ensures: `a == B, b == A, r == A (swap via temporary r)`

Prover: kprove (K haskell backend + z3) — **#Top** in 7.3s (mem cap 8G (systemd-run scope))

Three-assignment dataflow; finals are closed forms written directly in the scope RHS (no existentials). Initial r is dead in the IMP source and dropped.

Ported from KleverBench [`problems/imp/swap`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `r = a ; a = b ; b = r ;`

## K claims (verbatim)

```k
requires "verification.k"

module KB-SWAP-SPEC
  imports KB-SWAP-VERIFICATION

  // ---- Entry claim: swap a and b via temporary r; afterwards a = B, b = A, r = A ----
  // KleverBench problems/imp/swap: `r = a ; a = b ; b = r ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("r"), Name("a"))
      Assign(Name("a"), Name("b"))
      Assign(Name("b"), Name("r"))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- B ] [ "b" <- A ] [ "r" <- A ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    [all-path]
endmodule
```
