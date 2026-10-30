# concrete/gcd/a=48,b=18

```python
def gcd(a, b):
    if b == 0:
        return a
    return gcd(b, a % b)

result = gcd(48, 18)
```

Entry: `gcd({'a': 48, 'b': 18})` — validation: **exact_match**

| # | event | line | source | locals / value | K rules applied |
|---|---|---|---|---|---|
| 0 | line | 1 | `def gcd(a, b):` | {} | seq.step → def.bind → seq.step |
| 1 | line | 6 | `result = gcd(48, 18)` | {"gcd": "<function gcd>"} | seq.step → strict.assign-rhs → call.eval-callee → name.lookup-begin → name.lookup-hit → call.eval-args → args.eval-next → lit.int → args.eval-collect → args.eval-next → lit.int → args.eval-collect → args.apply |
| 2 | call | 1 | `def gcd(a, b):` | args: {"a": 48, "b": 18} | frame.push → params.bind-next×2 → params.done → seq.step |
| 3 | line | 2 | `if b == 0:` | {"a": 48, "b": 18} | seq.step → strict.if-cond → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.false → seq.done → seq.step |
| 4 | line | 4 | `return gcd(b, a % b)` | {"a": 48, "b": 18} | seq.step → strict.return-value → call.eval-callee → name.lookup-begin → name.lookup-parent → name.lookup-hit → call.eval-args → args.eval-next → name.lookup-begin → name.lookup-hit → args.eval-collect → args.eval-next → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → args.eval-collect → args.apply |
| 5 | call | 1 | `def gcd(a, b):` | args: {"a": 18, "b": 12} | frame.push → params.bind-next×2 → params.done → seq.step |
| 6 | line | 2 | `if b == 0:` | {"a": 18, "b": 12} | seq.step → strict.if-cond → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.false → seq.done → seq.step |
| 7 | line | 4 | `return gcd(b, a % b)` | {"a": 18, "b": 12} | seq.step → strict.return-value → call.eval-callee → name.lookup-begin → name.lookup-parent → name.lookup-hit → call.eval-args → args.eval-next → name.lookup-begin → name.lookup-hit → args.eval-collect → args.eval-next → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → args.eval-collect → args.apply |
| 8 | call | 1 | `def gcd(a, b):` | args: {"a": 12, "b": 6} | frame.push → params.bind-next×2 → params.done → seq.step |
| 9 | line | 2 | `if b == 0:` | {"a": 12, "b": 6} | seq.step → strict.if-cond → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.false → seq.done → seq.step |
| 10 | line | 4 | `return gcd(b, a % b)` | {"a": 12, "b": 6} | seq.step → strict.return-value → call.eval-callee → name.lookup-begin → name.lookup-parent → name.lookup-hit → call.eval-args → args.eval-next → name.lookup-begin → name.lookup-hit → args.eval-collect → args.eval-next → strict.binop → name.lookup-begin → name.lookup-hit → strict.binop×2 → name.lookup-begin → name.lookup-hit → strict.binop → op.binop-dispatch → args.eval-collect → args.apply |
| 11 | call | 1 | `def gcd(a, b):` | args: {"a": 6, "b": 0} | frame.push → params.bind-next×2 → params.done → seq.step |
| 12 | line | 2 | `if b == 0:` | {"a": 6, "b": 0} | seq.step → strict.if-cond → strict.compare-lhs → name.lookup-begin → name.lookup-hit → strict.compare-lhs → strict.compare-rhs → lit.int → strict.compare-rhs → op.compare-dispatch → strict.if-cond → if.dispatch → if.true → seq.step |
| 13 | line | 3 | `return a` | {"a": 6, "b": 0} | seq.step → strict.return-value → name.lookup-begin → name.lookup-hit → strict.return-value → return.set |
| 14 | return | 3 | `return a` | returns `6` — locals {"a": 6, "b": 0} | frame.pop → strict.return-value → return.set |
| 15 | return | 4 | `return gcd(b, a % b)` | returns `6` — locals {"a": 12, "b": 6} | frame.pop → strict.return-value → return.set |
| 16 | return | 4 | `return gcd(b, a % b)` | returns `6` — locals {"a": 18, "b": 12} | frame.pop → strict.return-value → return.set |
| 17 | return | 4 | `return gcd(b, a % b)` | returns `6` — locals {"a": 48, "b": 18} | frame.pop → strict.assign-rhs → assign.store → seq.done |

Rule names are defined in `semantics/mpy-traced/rules.yaml` (file:line -> name/kind/description).
