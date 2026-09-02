# verification/kb-nested-with-branch — **PROVED**

```python
res = 0
i = a
while 0 < i:
    if i <= b:
        j = i
        while 0 < j:
            res = res + 1
            j = j - 1
    i = i - 1
```

- requires: `a >= 1 and b >= 1`
- ensures: `res == m*(m+1)/2 for m = minInt(a, b) (only rows i <= b are admitted), i == 0, j == 0`
- invariant @ inner #while circularity: `j = J >= 1 => 0, res += J` (guard-true inner summary (c25 style))
- invariant @ outer #while circularities (admitted region, j-unbound and j-bound): `i = I >= 1, I <= b: i => 0, j => 0, res += (I*(I+1))/2` (the region where every remaining row fires)
- invariant @ outer #while circularities (skipped region, j-unbound and j-bound): `i = I, b < I, b >= 1: i => 0, j => 0, res += (b*(b+1))/2` (rows above b are skipped until i reaches b)

Prover: kprove (K haskell backend + z3) — **#Top** in 22.2s (mem cap 8G (systemd-run scope))

The hardest port: a branch guards the inner loop, so the outer circularity splits into admitted (i <= b) and skipped (b < i) regions, each in j-unbound and j-bound variants (four outer claims + the inner one). Its verification module adds two documented proof-only minInt simplification rules firing on the non-strict <= atoms the path actually carries (the stock equations require strict comparisons, and deciding those pushed z3 into an unknown).

Ported from KleverBench [`problems/imp/nested-with-branch`](https://github.com/nlp-research-rosu/KleverBench) @ `b5eced3` — original IMP: `res = 0 ; i = a ; while (0 < i) { if (i <= b) { j = i ; while (0 < j) { res = res + 1 ; j = j - 1 ; } } else { } i = i - 1 ; }`

## K claims (verbatim)

```k
requires "verification.k"

module KB-NESTED-WITH-BRANCH-SPEC
  imports KB-NESTED-WITH-BRANCH-VERIFICATION

  // ---- Inner-loop invariant (circularity): from j = J >= 1, res = R, the inner loop adds
  //      J to res and drains j to 0; a, b and i are untouched. Guard-true precondition is
  //      total over the states the outer body creates: every inner entry follows j = i
  //      under the outer guard 0 < i (kb-loop-max style) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("j"))),
        Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
        Assign(Name("j"), BinOp("-", Name("j"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- J:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- I ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires J >=Int 1
    ensures ?J2 ==Int 0
    andBool ?R2 ==Int R +Int J
    [all-path]

  // ---- Outer-loop invariants: one circularity per (region of i vs b) x (is j bound yet).
  //      The branch `i <= b` admits exactly the iterations i = min(I,B)..1, so res gains the
  //      triangular number of min(I,B); stating the two regions as separate claims keeps
  //      minInt (an ite-with-division for z3) out of every circularity target — with the
  //      claim-level split each target carries a plain product over one literal divisor.
  //      j is created by the first admitted iteration, so the two j-unbound claims (4-key
  //      scope) cover the entry path and the two j-bound ones (5-key scope) the back edges. ----

  // ---- j unbound, 1 <= I <= B: every remaining iteration is admitted, res gains
  //      I + (I-1) + ... + 1 = I*(I+1)/2, i drains to 0, j is created and ends drained at 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        If(Compare(Name("i"), CmpOp("<=", Name("b"))),
          Assign(Name("j"), Name("i"))
          While(Compare(Int(0), CmpOp("<", Name("j"))),
            Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
            Assign(Name("j"), BinOp("-", Name("j"), Int(1)))),
          .Stmts)
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1 andBool I <=Int B
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool ?R2 ==Int R +Int (I *Int (I +Int 1)) /Int 2
    [all-path]

  // ---- j unbound, I > B >= 1: iterations I..B+1 are skipped, then the loop enters the
  //      admitted region at i = B, so res gains B*(B+1)/2, i drains to 0, j ends 0 ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        If(Compare(Name("i"), CmpOp("<=", Name("b"))),
          Assign(Name("j"), Name("i"))
          While(Compare(Int(0), CmpOp("<", Name("j"))),
            Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
            Assign(Name("j"), BinOp("-", Name("j"), Int(1)))),
          .Stmts)
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires B <Int I andBool B >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool ?R2 ==Int R +Int (B *Int (B +Int 1)) /Int 2
    [all-path]

  // ---- j bound, 1 <= I <= B: as above with j already in scope (back edge of the
  //      admitted region) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        If(Compare(Name("i"), CmpOp("<=", Name("b"))),
          Assign(Name("j"), Name("i"))
          While(Compare(Int(0), CmpOp("<", Name("j"))),
            Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
            Assign(Name("j"), BinOp("-", Name("j"), Int(1)))),
          .Stmts)
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- _:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires I >=Int 1 andBool I <=Int B
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool ?R2 ==Int R +Int (I *Int (I +Int 1)) /Int 2
    [all-path]

  // ---- j bound, I > B >= 1: as above with j already in scope (back edge of the
  //      skipped region) ----
  claim
    <k>
      #while(Compare(Int(0), CmpOp("<", Name("i"))),
        If(Compare(Name("i"), CmpOp("<=", Name("b"))),
          Assign(Name("j"), Name("i"))
          While(Compare(Int(0), CmpOp("<", Name("j"))),
            Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
            Assign(Name("j"), BinOp("-", Name("j"), Int(1)))),
          .Stmts)
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <scopes>
      ... 0 |-> (
        scope(.Map [ "a" <- A:Int ] [ "b" <- B:Int ] [ "res" <- R:Int ] [ "i" <- I:Int ] [ "j" <- _:Int ], P:Parent) =>
        scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], P)
      ) ...
    </scopes>
    <env> 0 </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires B <Int I andBool B >=Int 1
    ensures ?I2 ==Int 0
    andBool ?J2 ==Int 0
    andBool ?R2 ==Int R +Int (B *Int (B +Int 1)) /Int 2
    [all-path]

  // ---- Entry claim: for a = A >= 1, b = B >= 1 the outer loop walks i = A..1, the branch
  //      admits only i <= B, and each admitted i lets the inner loop add i to res, so the
  //      nested loops terminate with res == min(A,B)*(min(A,B)+1)/2 (the triangular number
  //      of min(A,B)) and both counters drained: i == 0 and j == 0 ----
  // KleverBench problems/imp/nested-with-branch:
  //   `res = 0 ; i = a ;
  //    while (0 < i) {
  //      if (i <= b) { j = i ; while (0 < j) { res = res + 1 ; j = j - 1 ; } } else { }
  //      i = i - 1 ; }`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("res"), Int(0))
      Assign(Name("i"), Name("a"))
      While(Compare(Int(0), CmpOp("<", Name("i"))),
        If(Compare(Name("i"), CmpOp("<=", Name("b"))),
          Assign(Name("j"), Name("i"))
          While(Compare(Int(0), CmpOp("<", Name("j"))),
            Assign(Name("res"), BinOp("+", Name("res"), Int(1)))
            Assign(Name("j"), BinOp("-", Name("j"), Int(1)))),
          .Stmts)
        Assign(Name("i"), BinOp("-", Name("i"), Int(1))))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R2:Int ] [ "i" <- ?I2:Int ] [ "j" <- ?J2:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires A >=Int 1 andBool B >=Int 1
    ensures ?R2 ==Int (minInt(A, B) *Int (minInt(A, B) +Int 1)) /Int 2
    andBool ?I2 ==Int 0
    andBool ?J2 ==Int 0
    [all-path]
endmodule
```
