# verification/kb-squares-cubic — **PROVED**

```python
res = 0
i = n
while 0 < i:
    j = i
    while 0 < j:
        res = res + i
        j = j - 1
    i = i - 1
```

- requires: `n >= 1`
- ensures: `res == n*(n+1)*(2n+1)/6 (the sum of squares 1² + ... + n²), i == 0, j == 0`
- invariant @ inner #while circularity: `j => minInt(j, 0), res += i * maxInt(j, 0); n, i unchanged` (total inner-loop summary (adds i per iteration))
- invariant @ outer #while circularity: `i = I >= 1 => 0, j => 0, res += (I*(I+1)*(2I+1))/6` (outer circularity, sum-of-squares closed form)

Prover: kprove (K haskell backend + z3) — **#Top** in 13.6s (mem cap 8G (systemd-run scope))

Sum of squares via i added i times: the outer circularity carries the cubic closed form as one whole-numerator division by 6, and z3 discharges the per-step delta i*(i+1)*(2i+1)/6 - (i-1)*i*(2i-1)/6 == i² unaided. Magic literal 137.

Ported from KleverBench [`problems/imp/squares-cubic`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `res = 0 ; i = n ; while (0 < i) { j = i ; while (0 < j) { res = res + i ; j = j - 1 ; } i = i - 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-SQUARES-CUBIC-SPEC
  imports KB-SQUARES-CUBIC-VERIFICATION

  // ---- Inner-loop invariant (circularity, total): from j = J, res = R, the inner loop
  //      adds i exactly max(J,0) times — res gains I *Int maxInt(J,0) — and drains j to
  //      min(J,0) (no-op when J <= 0); i and n are untouched ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("res"), BinOp("+", Name("res"), Name("i")))
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "res" <- ?R2:Int ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?J2 ==Int minInt(J, 0)
    andBool ?R2 ==Int R +Int I *Int maxInt(J, 0)
    [all-path]

  // ---- Outer-loop invariant (circularity): from i = I with I >= 1, res = R, each outer
  //      iteration lets the inner loop add i*i (i copies of i) into res, so res gains
  //      I^2 + (I-1)^2 + ... + 1 = I*(I+1)*(2I+1)/6 while i drains to 0 and j is left
  //      drained at 0 (the last inner run starts from j = 1) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("i"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("res"), BinOp("+", Name("res"), Name("i")))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "n" <- N:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- _:Int ], P:Parent) =>
        scope(.Map [ "n" <- N ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool ?R2 ==Int R +Int (I *Int (I +Int 1) *Int (2 *Int I +Int 1)) /Int 6
    [all-path]

  // ---- Entry claim: for every n = N >= 1, the nested loops terminate with the
  //      sum of squares res == N*(N+1)*(2N+1)/6 and both counters drained:
  //      i == 0 and j == 0 ----
  // KleverBench problems/imp/squares-cubic:
  //   `res = 0 ; i = n ;
  //    while (0 < i) { j = i ; while (0 < j) { res = res + i ; j = j - 1 ; } i = i - 1 ; }`
  claim
    <k>
      Assign(Name("n"), N:Int)
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Name("n"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        Assign(Name("j"), Name("i"))
        While(Compare(Int(0), CmpOp("<", Name("j"))),
          Assign(Name("res"), BinOp("+", Name("res"), Name("i")))
          Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "n" <- N ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 1
    ensures ?R2 ==Int (N *Int (N +Int 1) *Int (2 *Int N +Int 1)) /Int 6
    andBool ?I2 ==Int 0
    andBool ?J2 ==Int 0
    [all-path]
endmodule
```
