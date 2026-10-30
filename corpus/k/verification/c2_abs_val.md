# verification/abs-val — **PROVED**

```python
def abs_val(x):
    if x < 0:
        return -x
    return x

result = abs_val(x)
```

- requires: `True (any int x)`
- ensures: `result >= 0 and (result == x or result == -x)`

Prover: kprove (K haskell backend + z3) — **#Top** in 17.3s (mem cap 8G (systemd-run scope))

Branching functional-correctness proof, all paths.

## K claims (verbatim)

```k
requires "verification.k"

module ABS-VAL-SPEC
  imports ABS-VAL-VERIFICATION

  // ---- Entry claim: for every int x, result >= 0 and result is x or -x ----
  claim
    <k>
      FuncDef("abs_val", Params("x"),
        If(Compare(Name("x"), CmpOp("<", Int(0))),
          Return(UnaryOp("-", Name("x"))),
          .Stmts)
        Return(Name("x")))
      Assign(Name("result"), Call(Name("abs_val"), X:Int))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "abs_val" <- ?_:Val ] [ "result" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures (?R >=Int 0)
      andBool ((?R ==Int X) orBool (?R ==Int (0 -Int X)))
    [all-path]
endmodule
```
