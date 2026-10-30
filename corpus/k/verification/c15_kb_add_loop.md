# verification/kb-add-loop — **PROVED**

```python
while 0 < n:
    res = res + a
    n = n - 1
```

- requires: `True (any ints n, res, a)`
- ensures: `n == minInt(n, 0), res == res0 + a * maxInt(n, 0) (adds a exactly max(n,0) times); a unchanged`
- invariant @ while-loop head (#while circularity claim): `from n = I, res = S (a = A unchanged): the loop ends with n == minInt(I, 0), res == S + A*maxInt(I, 0)` (circularity claim, no requires — the closed form is total over all I)

Prover: kprove (K haskell backend + z3) — **#Top** in 11.2s (mem cap 8G (systemd-run scope))

Repeated addition with NO precondition: the piecewise minInt/maxInt closed form covers the no-op branch; z3 discharges the nonlinear a*maxInt back-edge algebra unaided.

Ported from KleverBench [`problems/imp/add-loop`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `while (0 < n) { res = res + a ; n = n - 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-ADD-LOOP-SPEC
  imports KB-ADD-LOOP-VERIFICATION

  // ---- Loop invariant (circularity): from n = I, res = S, the loop adds a exactly max(I,0)
  //      times and drains n to min(I,0); a no-op when I <= 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("a")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ] [ "res" <- S:Int ] [ "a" <- A:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ] [ "res" <- ?S2:Int ] [ "a" <- A ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(I, 0) andBool ?S2 ==Int S +Int A *Int maxInt(I, 0)
    [all-path]

  // ---- Entry claim: for arbitrary ints n, res, a the loop terminates with
  //      res = res0 + a*max(n0,0) and n = min(n0,0) ----
  // KleverBench problems/imp/add-loop: `while (0 < n) { res = res + a ; n = n - 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("res"), R:Int)
      Assign(Name("a"), A:Int)
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("a")))
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- ?F:Int ] [ "res" <- ?S2:Int ] [ "a" <- A ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?F ==Int minInt(N, 0) andBool ?S2 ==Int R +Int A *Int maxInt(N, 0)
    [all-path]
endmodule
```
