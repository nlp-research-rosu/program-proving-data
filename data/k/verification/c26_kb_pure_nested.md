# verification/kb-pure-nested — **PROVED**

```python
i = a
while 0 < i:
    j = b
    while 0 < j:
        j = j - 1
    i = i - 1
```

- requires: `a >= 1`
- ensures: `i == 0 and j == minInt(b, 0); a, b unchanged`
- invariant @ inner #while circularity: `j = J drains to minInt(J, 0); a, b, i unchanged` (total inner-loop summary the prover applies each time it walks the outer body)
- invariant @ outer #while circularity: `i = I >= 1 drains to 0, j ends at minInt(b, 0)` (outer circularity; back edge at I - 1 >= 1, the I - 1 == 0 boundary discharged by one extra unfold)

Prover: kprove (K haskell backend + z3) — **#Top** in 12.1s (mem cap 8G (systemd-run scope))

First nested-loop port: one circularity per loop level, the inner claim first and total (no requires — it must cover every state each outer iteration creates), the outer under i >= 1. The first outer iteration (j still unbound) unfolds in the entry claim before the outer circularity anchors. Magic literals downsized to 137/138 so the concrete run stays instant.

Ported from KleverBench [`problems/imp/pure-nested`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `i = a ; while (0 < i) { j = b ; while (0 < j) { j = j - 1 ; } i = i - 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-PURE-NESTED-SPEC
  imports KB-PURE-NESTED-VERIFICATION

  // ---- Inner-loop invariant (circularity): from j = J the countdown drains j to min(J, 0)
  //      and touches nothing else — total (no requires): every outer iteration re-enters it
  //      with fresh i and j = b, so it must hold for arbitrary I and J ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?J2 ==Int minInt(J, 0)
    [all-path]

  // ---- Outer-loop invariant (circularity): from i = I with I >= 1 the outer countdown runs
  //      at least once — each iteration resets j to b and drains it (inner claim summarizes
  //      the inner While) — so i falls to 0 and j ends min(B, 0) regardless of its old value;
  //      the back-edge boundary i = 0 is discharged by one extra unfold ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "i" <- I:Int ] [ "j" <- _J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int minInt(B, 0)
    [all-path]

  // ---- Entry claim: for every a >= 1 the nested countdowns terminate with i = 0 and
  //      j = min(b, 0) — no accumulation, the loops only drain ----
  // KleverBench problems/imp/pure-nested:
  //   `i = a ; while (0 < i) { j = b ; while (0 < j) { j = j - 1 ; } i = i - 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("b"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int minInt(B, 0)
    [all-path]
endmodule
```
