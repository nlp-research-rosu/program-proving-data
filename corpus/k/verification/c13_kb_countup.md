# verification/kb-countup — **PROVED**

```python
while r < n:
    r = r + 1
```

- requires: `True (any ints n, r)`
- ensures: `r == maxInt(n, r0) for initial r0 (climb to n, no-op when r0 >= n); n unchanged`
- invariant @ while-loop head (#while circularity claim): `n = N unchanged, r = I arbitrary; the remaining iterations end with r == maxInt(N, I)` (circularity claim — back edge re-establishes the closed form at I + 1; exit branch has N <= I, where maxInt(N, I) == I)

Prover: kprove (K haskell backend + z3) — **#Top** in 7.6s (mem cap 8G (systemd-run scope))

While-loop proof with NO precondition: the invariant's closed form maxInt(n, r) covers both the climbing and the no-op case; z3 discharges maxInt(N, I+1) == maxInt(N, I) under I < N on the back edge. Guard `!(n <= r)` written as `r < n`.

Ported from KleverBench [`problems/imp/countup`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `while (!(n <= r)) { r = r + 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-COUNTUP-SPEC
  imports KB-COUNTUP-VERIFICATION

  // ---- Loop invariant (circularity): r climbs to n; if it starts at or above n it stays put ----
  claim
    <k>
      #while(Compare(Name("r"), CmpOp("<", Name("n"))),
        Assign(Name("r"), BinOp("+", Name("r"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "r" <- I:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "r" <- ?R2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R2 ==Int maxInt(N, I)
    [all-path]

  // ---- Entry claim: the loop terminates with r = max(n, r0), for arbitrary ints n, r0 ----
  // KleverBench problems/imp/countup: `while (!(n <= r)) { r = r + 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("r"), R:Int)
      While(Compare(Name("r"), CmpOp("<", Name("n"))),
        Assign(Name("r"), BinOp("+", Name("r"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "r" <- ?R2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R2 ==Int maxInt(N, R)
    [all-path]
endmodule
```
