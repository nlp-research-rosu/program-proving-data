# concrete/sum_to_n/n=5

```python
def sum_to_n(n):
    acc = 0
    i = 1
    while i <= n:
        acc = acc + i
        i = i + 1
    return acc

result = sum_to_n(5)
```

Entry: `sum_to_n({'n': 5})` — validation: **exact_match**

| # | event | line | source | locals / value | K rules applied |
|---|---|---|---|---|---|
| 0 | line | 1 | `def sum_to_n(n):` | {} | seq.step → def.bind → seq.step |
| 1 | line | 9 | `result = sum_to_n(5)` | {"sum_to_n": "<function sum_to_n>"} | seq.step → strict.assign-rhs → call.eval-callee → name.lookup-begin → name.lookup-hit → call.eval-args → args.eval-next → lit.int → args.eval-collect → args.apply |
| 2 | call | 1 | `def sum_to_n(n):` | args: {"n": 5} | frame.push → params.bind-next → params.done → seq.step |
| 3 | line | 2 | `acc = 0` | {"n": 5} | seq.step → strict.assign-rhs → lit.int → strict.assign-rhs → assign.store → seq.step |
| 4 | line | 3 | `i = 1` | {"acc": 0, "n": 5} | seq.step → strict.assign-rhs → lit.int → strict.assign-rhs → assign.store → seq.step |
| 5 | line | 4 | `while i <= n:` | {"acc": 0, "i": 1, "n": 5} | seq.step → while.begin → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → name.lookup-begin → name.lookup-hit → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 6 | line | 5 | `acc = acc + i` | {"acc": 0, "i": 1, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 7 | line | 6 | `i = i + 1` | {"acc": 1, "i": 1, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 8 | line | 4 | `while i <= n:` | {"acc": 1, "i": 2, "n": 5} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → name.lookup-begin → name.lookup-hit → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 9 | line | 5 | `acc = acc + i` | {"acc": 1, "i": 2, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 10 | line | 6 | `i = i + 1` | {"acc": 3, "i": 2, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 11 | line | 4 | `while i <= n:` | {"acc": 3, "i": 3, "n": 5} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → name.lookup-begin → name.lookup-hit → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 12 | line | 5 | `acc = acc + i` | {"acc": 3, "i": 3, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 13 | line | 6 | `i = i + 1` | {"acc": 6, "i": 3, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 14 | line | 4 | `while i <= n:` | {"acc": 6, "i": 4, "n": 5} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → name.lookup-begin → name.lookup-hit → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 15 | line | 5 | `acc = acc + i` | {"acc": 6, "i": 4, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 16 | line | 6 | `i = i + 1` | {"acc": 10, "i": 4, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 17 | line | 4 | `while i <= n:` | {"acc": 10, "i": 5, "n": 5} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → name.lookup-begin → name.lookup-hit → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 18 | line | 5 | `acc = acc + i` | {"acc": 10, "i": 5, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 19 | line | 6 | `i = i + 1` | {"acc": 15, "i": 5, "n": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 20 | line | 4 | `while i <= n:` | {"acc": 15, "i": 6, "n": 5} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → name.lookup-begin → name.lookup-hit → strict.compare-rhs → op.compare-dispatch → while.exit → seq.step |
| 21 | line | 7 | `return acc` | {"acc": 15, "i": 6, "n": 5} | seq.step → strict.return-value → name.lookup-begin → name.lookup-hit → strict.return-value → return.set |
| 22 | return | 7 | `return acc` | returns `15` — locals {"acc": 15, "i": 6, "n": 5} | frame.pop → strict.assign-rhs → assign.store → seq.done |

Rule names are defined in `semantics/mpy-traced/rules.yaml` (file:line -> name/kind/description).
