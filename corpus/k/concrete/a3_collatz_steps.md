# concrete/collatz_steps/n=6

```python
def collatz_steps(n):
    steps = 0
    while n != 1:
        if n % 2 == 0:
            n = n // 2
        else:
            n = 3 * n + 1
        steps = steps + 1
    return steps

result = collatz_steps(6)
```

Entry: `collatz_steps({'n': 6})` — validation: **exact_match**

| # | event | line | source | locals / value | K rules applied |
|---|---|---|---|---|---|
| 0 | line | 1 | `def collatz_steps(n):` | {} | seq.step → def.bind → seq.step |
| 1 | line | 11 | `result = collatz_steps(6)` | {"collatz_steps": "<function collatz_steps>"} | seq.step → strict.assign-rhs → call.eval-callee → name.lookup-begin → name.lookup-hit → call.eval-args → args.eval-next → lit.int → args.eval-collect → args.apply |
| 2 | call | 1 | `def collatz_steps(n):` | args: {"n": 6} | frame.push → params.bind-next → params.done → seq.step |
| 3 | line | 2 | `steps = 0` | {"n": 6} | seq.step → strict.assign-rhs → lit.int → strict.assign-rhs → assign.store → seq.step |
| 4 | line | 3 | `while n != 1:` | {"n": 6, "steps": 0} | seq.step → while.begin → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 5 | line | 4 | `if n % 2 == 0:` | {"n": 6, "steps": 0} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 6 | line | 5 | `n = n // 2` | {"n": 6, "steps": 0} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 7 | line | 8 | `steps = steps + 1` | {"n": 3, "steps": 0} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 8 | line | 3 | `while n != 1:` | {"n": 3, "steps": 1} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 9 | line | 4 | `if n % 2 == 0:` | {"n": 3, "steps": 1} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.false → seq.step |
| 10 | line | 7 | `n = 3 * n + 1` | {"n": 3, "steps": 1} | seq.step → strict.assign-rhs → strict.binop×2 → lit.int → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 11 | line | 8 | `steps = steps + 1` | {"n": 10, "steps": 1} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 12 | line | 3 | `while n != 1:` | {"n": 10, "steps": 2} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 13 | line | 4 | `if n % 2 == 0:` | {"n": 10, "steps": 2} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 14 | line | 5 | `n = n // 2` | {"n": 10, "steps": 2} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 15 | line | 8 | `steps = steps + 1` | {"n": 5, "steps": 2} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 16 | line | 3 | `while n != 1:` | {"n": 5, "steps": 3} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 17 | line | 4 | `if n % 2 == 0:` | {"n": 5, "steps": 3} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.false → seq.step |
| 18 | line | 7 | `n = 3 * n + 1` | {"n": 5, "steps": 3} | seq.step → strict.assign-rhs → strict.binop×2 → lit.int → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 19 | line | 8 | `steps = steps + 1` | {"n": 16, "steps": 3} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 20 | line | 3 | `while n != 1:` | {"n": 16, "steps": 4} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 21 | line | 4 | `if n % 2 == 0:` | {"n": 16, "steps": 4} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 22 | line | 5 | `n = n // 2` | {"n": 16, "steps": 4} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 23 | line | 8 | `steps = steps + 1` | {"n": 8, "steps": 4} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 24 | line | 3 | `while n != 1:` | {"n": 8, "steps": 5} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 25 | line | 4 | `if n % 2 == 0:` | {"n": 8, "steps": 5} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 26 | line | 5 | `n = n // 2` | {"n": 8, "steps": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 27 | line | 8 | `steps = steps + 1` | {"n": 4, "steps": 5} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 28 | line | 3 | `while n != 1:` | {"n": 4, "steps": 6} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 29 | line | 4 | `if n % 2 == 0:` | {"n": 4, "steps": 6} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 30 | line | 5 | `n = n // 2` | {"n": 4, "steps": 6} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 31 | line | 8 | `steps = steps + 1` | {"n": 2, "steps": 6} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 32 | line | 3 | `while n != 1:` | {"n": 2, "steps": 7} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.iterate → seq.step |
| 33 | line | 4 | `if n % 2 == 0:` | {"n": 2, "steps": 7} | seq.step → strict.if-cond → strict.compare-lhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 34 | line | 5 | `n = n // 2` | {"n": 2, "steps": 7} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.done → seq.step |
| 35 | line | 8 | `steps = steps + 1` | {"n": 1, "steps": 7} | seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → lit.int → strict.binop → op.binop-dispatch → strict.assign-rhs → assign.store → seq.step |
| 36 | line | 3 | `while n != 1:` | {"n": 1, "steps": 8} | seq.done → loop.label-unfold → while.cond-eval → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → while.exit → seq.step |
| 37 | line | 9 | `return steps` | {"n": 1, "steps": 8} | seq.step → strict.return-value → name.lookup-begin → name.lookup-hit → strict.return-value → return.set |
| 38 | return | 9 | `return steps` | returns `8` — locals {"n": 1, "steps": 8} | frame.pop → strict.assign-rhs → assign.store → seq.done |

Rule names are defined in `semantics/mpy-traced/rules.yaml` (file:line -> name/kind/description).
