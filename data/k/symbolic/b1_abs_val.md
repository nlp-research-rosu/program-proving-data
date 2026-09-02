# symbolic/abs_val/x=?x:int

```python
def abs_val(x):
    if x < 0:
        return -x
    return x

result = abs_val(x)
```

Symbolic args: `{'x': '?x:int'}` — 2 feasible paths, 0 infeasible (SMT-pruned)

## Path -> return `0 - x`  (node 1)

- path condition: `x < 0`
- witness: `{'x': -1}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def abs_val(x):` | {} |
| 6 | `result = abs_val(x)` | {"abs_val": "<function abs_val>"} |
| 2 | `if x < 0:` | {"x": "x"} |
| 3 | `return -x` | {"x": "x"} |

## Path -> return `x`  (node 2)

- path condition: `not (x < 0)`
- witness: `{'x': 0}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def abs_val(x):` | {} |
| 6 | `result = abs_val(x)` | {"abs_val": "<function abs_val>"} |
| 2 | `if x < 0:` | {"x": "x"} |
| 4 | `return x` | {"x": "x"} |
