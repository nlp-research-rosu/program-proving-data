# verification/kb-chain — **PROVED**

```python
x = a + 1
y = x * 2
z = y - a
```

- requires: `True (any int a)`
- ensures: `x == a + 1, y == (a + 1) * 2, z == (a + 1) * 2 - a; a unchanged`

Prover: kprove (K haskell backend + z3) — **#Top** in 8.2s (mem cap 8G (systemd-run scope))

Three-step dataflow chain; all three computed finals pinned as direct closed forms of the symbolic input.

Ported from KleverBench [`problems/imp/chain`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `x = a + 1 ; y = x * 2 ; z = y - a ;`

## K claims (verbatim)

```k
requires "verification.k"

module KB-CHAIN-SPEC
  imports KB-CHAIN-VERIFICATION

  // ---- Entry claim: three-step dataflow chain x = a+1, y = 2x, z = y-a, for every int a ----
  // KleverBench problems/imp/chain: `x = a + 1 ; y = x * 2 ; z = y - a ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("x"), BinOp("+", Name("a"), Int(1)))
      Assign(Name("y"), BinOp("*", Name("x"), Int(2)))
      Assign(Name("z"), BinOp("-", Name("y"), Name("a")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "x" <- A +Int 1 ] [ "y" <- (A +Int 1) *Int 2 ] [ "z" <- (A +Int 1) *Int 2 -Int A ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    [all-path]
endmodule
```
