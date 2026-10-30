# concrete/half_of_even/x=7

```python
def half_of_even(x):
    assert x % 2 == 0
    return x // 2

result = half_of_even(7)
```

Entry: `half_of_even({'x': 7})` — validation: **exact_match**

| # | event | line | source | locals / value | K rules applied |
|---|---|---|---|---|---|
| 0 | line | 1 | `def half_of_even(x):` | {} | seq.step → def.bind → seq.step |
| 1 | line | 5 | `result = half_of_even(7)` | {"half_of_even": "<function half_of_even>"} | seq.step → strict.assign-rhs → call.eval-callee → name.lookup-begin → name.lookup-hit → call.eval-args → args.eval-next → lit.int → args.eval-collect → args.apply |
| 2 | call | 1 | `def half_of_even(x):` | args: {"x": 7} | frame.push → params.bind-next → params.done → seq.step |
| 3 | line | 2 | `assert x % 2 == 0` | {"x": 7} | seq.step → strict.assert-test → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.assert-test → assert.fail |
| 4 | exception | 2 | `assert x % 2 == 0` | **AssertionError** — locals {"x": 7} | assert.fail |

Rule names are defined in `semantics/mpy-traced/rules.yaml` (file:line -> name/kind/description).
