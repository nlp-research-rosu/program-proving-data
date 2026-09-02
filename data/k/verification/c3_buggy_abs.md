# verification/buggy-abs — **REFUTED**

```python
def buggy_abs(x):
    if x < 0:
        return -x
    elif x > 0:
        return x

result = buggy_abs(x)
```

- requires: `True (any int x)`
- ensures: `result >= 0 and (result == x or result == -x)`

Prover: kprove (K haskell backend + z3) — **stuck claim state** in 69.3s (mem cap 8G (systemd-run scope))

Same spec as c2 over the buggy implementation (missing x == 0 case falls through to None). The prover must NOT prove it.

## Counterexample

- stuck-state path condition: `(not (< x 0)) and (not (> x 0))`
- z3 model: `x = 0`
- concrete replay: `result = None` — result is None, which fails `result >= 0 and (result == x or result == -x)`

| # | event | line | locals / value |
|---|---|---|---|
| 0 | line | 1 | {} |
| 1 | line | 7 | {"buggy_abs": "<function buggy_abs>"} |
| 2 | call | 1 | {"x": 0} |
| 3 | line | 2 | {"x": 0} |
| 4 | line | 4 | {"x": 0} |
| 5 | return | 4 | returns `None` |

## K claims (verbatim)

```k
requires "verification.k"

module BUGGY-ABS-SPEC
  imports BUGGY-ABS-VERIFICATION

  // ---- Same absolute-value spec, over the buggy implementation (no x == 0
  // case: control falls off the body and returns None). EXPECTED: REFUTED —
  // the prover gets stuck at the fall-through state, whose path condition
  // yields the counterexample x == 0. ----
  claim
    <k>
      FuncDef("buggy_abs", Params("x"),
        If(Compare(Name("x"), CmpOp("<", Int(0))),
          Return(UnaryOp("-", Name("x"))),
          If(Compare(Name("x"), CmpOp(">", Int(0))),
            Return(Name("x")),
            .Stmts)))
      Assign(Name("result"), Call(Name("buggy_abs"), X:Int))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "buggy_abs" <- ?_:Val ] [ "result" <- ?R:Int ], parent(-1))
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
