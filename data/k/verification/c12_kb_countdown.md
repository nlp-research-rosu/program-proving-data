# verification/kb-countdown — **PROVED**

```python
while 0 < n:
    n = n - 1
```

- requires: `n >= 0`
- ensures: `n == 0 (the loop drains n exactly to zero)`
- invariant @ while-loop head (#while circularity claim): `n = I with I >= 0; the remaining iterations end with n == 0` (circularity claim — the back edge re-enters it at I - 1 (guard 0 < I keeps I - 1 >= 0); on exit I <= 0 and I >= 0 force I == 0)

Prover: kprove (K haskell backend + z3) — **#Top** in 7.6s (mem cap 8G (systemd-run scope))

First ported while-loop proof: a circularity claim anchored on the mid-execution #while redex (n = I >= 0 at the loop head ends at exactly 0) plus the entry claim, the same two-claim shape as the vendored range-loop proof. Guard `!(n <= 0)` is written idiomatically as `0 < n`, `n + -1` as `n - 1`.

Ported from KleverBench [`problems/imp/countdown`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `while (!(n <= 0)) { n = n + -1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-COUNTDOWN-SPEC
  imports KB-COUNTDOWN-VERIFICATION

  // ---- Loop invariant (circularity): from any n = I >= 0, the countdown loop drains n to 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- I:Int ], P:Parent) =>
        scope(.Map [ "n" <- ?F:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 0
    ensures ?F ==Int 0
    [all-path]

  // ---- Entry claim: for every n >= 0, the loop terminates with n == 0 ----
  // KleverBench problems/imp/countdown: `while (!(n <= 0)) { n = n + -1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      While(Compare(Int(0), CmpOp("<", Name("n"))),
        Assign(Name("n"), BinOp("-", Name("n"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- ?F:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?F ==Int 0
    [all-path]
endmodule
```
