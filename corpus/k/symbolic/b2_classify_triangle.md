# symbolic/classify_triangle/a=?a:int,b=?b:int,c=?c:int

```python
def classify_triangle(a, b, c):
    equal_pairs = 0
    if a == b:
        equal_pairs = equal_pairs + 1
    if b == c:
        equal_pairs = equal_pairs + 1
    if a == c:
        equal_pairs = equal_pairs + 1
    if equal_pairs == 3:
        return "equilateral"
    if equal_pairs >= 1:
        return "isosceles"
    return "scalene"

result = classify_triangle(a, b, c)
```

Symbolic args: `{'a': '?a:int', 'b': '?b:int', 'c': '?c:int'}` — 5 feasible paths, 3 infeasible (SMT-pruned)

## Path -> return `equilateral`  (node 3)

- path condition: `a == c and b == c`
- witness: `{'a': 2, 'b': 2, 'c': 2}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def classify_triangle(a, b, c):` | {} |
| 15 | `result = classify_triangle(a, b, c)` | {"classify_triangle": "<function classify_triangle>"} |
| 2 | `equal_pairs = 0` | {"a": "c", "b": "c", "c": "c"} |
| 3 | `if a == b:` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 0} |
| 4 | `equal_pairs = equal_pairs + 1` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 0} |
| 5 | `if b == c:` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 1} |
| 6 | `equal_pairs = equal_pairs + 1` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 1} |
| 7 | `if a == c:` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 2} |
| 8 | `equal_pairs = equal_pairs + 1` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 2} |
| 9 | `if equal_pairs == 3:` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 3} |
| 10 | `return "equilateral"` | {"a": "c", "b": "c", "c": "c", "equal_pairs": 3} |

## Path -> return `isosceles`  (node 4)

- path condition: `not (b == c) and a == b`
- witness: `{'a': 2, 'b': 2, 'c': 3}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def classify_triangle(a, b, c):` | {} |
| 15 | `result = classify_triangle(a, b, c)` | {"classify_triangle": "<function classify_triangle>"} |
| 2 | `equal_pairs = 0` | {"a": "b", "b": "b", "c": "c"} |
| 3 | `if a == b:` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 0} |
| 4 | `equal_pairs = equal_pairs + 1` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 0} |
| 5 | `if b == c:` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 1} |
| 7 | `if a == c:` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 1} |
| 9 | `if equal_pairs == 3:` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 1} |
| 11 | `if equal_pairs >= 1:` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 1} |
| 12 | `return "isosceles"` | {"a": "b", "b": "b", "c": "c", "equal_pairs": 1} |

## Path -> return `isosceles`  (node 5)

- path condition: `not (a == c) and b == c`
- witness: `{'a': 3, 'b': 2, 'c': 2}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def classify_triangle(a, b, c):` | {} |
| 15 | `result = classify_triangle(a, b, c)` | {"classify_triangle": "<function classify_triangle>"} |
| 2 | `equal_pairs = 0` | {"a": "a", "b": "c", "c": "c"} |
| 3 | `if a == b:` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 0} |
| 5 | `if b == c:` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 0} |
| 6 | `equal_pairs = equal_pairs + 1` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 0} |
| 7 | `if a == c:` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 1} |
| 9 | `if equal_pairs == 3:` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 1} |
| 11 | `if equal_pairs >= 1:` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 1} |
| 12 | `return "isosceles"` | {"a": "a", "b": "c", "c": "c", "equal_pairs": 1} |

## Path -> return `isosceles`  (node 7)

- path condition: `not (b == c) and a == c`
- witness: `{'a': 2, 'b': 3, 'c': 2}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def classify_triangle(a, b, c):` | {} |
| 15 | `result = classify_triangle(a, b, c)` | {"classify_triangle": "<function classify_triangle>"} |
| 2 | `equal_pairs = 0` | {"a": "c", "b": "b", "c": "c"} |
| 3 | `if a == b:` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 0} |
| 5 | `if b == c:` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 0} |
| 7 | `if a == c:` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 0} |
| 8 | `equal_pairs = equal_pairs + 1` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 0} |
| 9 | `if equal_pairs == 3:` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 1} |
| 11 | `if equal_pairs >= 1:` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 1} |
| 12 | `return "isosceles"` | {"a": "c", "b": "b", "c": "c", "equal_pairs": 1} |

## Path -> return `scalene`  (node 8)

- path condition: `not (a == b) and not (a == c) and not (b == c)`
- witness: `{'a': 2, 'b': 3, 'c': 4}` — replay validated: **True**

| line | source | symbolic locals |
|---|---|---|
| 1 | `def classify_triangle(a, b, c):` | {} |
| 15 | `result = classify_triangle(a, b, c)` | {"classify_triangle": "<function classify_triangle>"} |
| 2 | `equal_pairs = 0` | {"a": "a", "b": "b", "c": "c"} |
| 3 | `if a == b:` | {"a": "a", "b": "b", "c": "c", "equal_pairs": 0} |
| 5 | `if b == c:` | {"a": "a", "b": "b", "c": "c", "equal_pairs": 0} |
| 7 | `if a == c:` | {"a": "a", "b": "b", "c": "c", "equal_pairs": 0} |
| 9 | `if equal_pairs == 3:` | {"a": "a", "b": "b", "c": "c", "equal_pairs": 0} |
| 11 | `if equal_pairs >= 1:` | {"a": "a", "b": "b", "c": "c", "equal_pairs": 0} |
| 13 | `return "scalene"` | {"a": "a", "b": "b", "c": "c", "equal_pairs": 0} |

## Infeasible paths (pruned by SMT)

- `a == b and b == c and not (a == c)` — z3 unsat on the path constraints (equality is transitive)
- `a == b and not (b == c) and a == c` — z3 unsat on the path constraints (equality is transitive)
- `not (a == b) and b == c and a == c` — z3 unsat on the path constraints (equality is transitive)
