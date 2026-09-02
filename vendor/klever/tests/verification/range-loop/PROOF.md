# Proof — `range` counter loop (over the whole semantics)

Proves that `for i in range(N)` over a **symbolic** bound `N` computes the Gauss closed
form, **over the whole reference semantics** (`verification.k` imports `MPY` directly — no
copied cut, so the proof can't drift from what `krun` runs). `solution.py`:

```python
def f(n):
    total = 0
    i = 0
    for i in range(n):
        total += i
    return total
```

`kprove` proves `result == N*(N-1)/2` for symbolic `N >= 0`. **`#Top`** (both claims),
non-vacuous.

## The loop structure: in-cell continuation (no `<lstack>`)

A range is a lazy `rangeObj` (the counter stays an int in the term, never a list), and the
unified `#loop` keeps the **loop-back continuation in the `<k>` cell** as `loopLbl(#loop(tail))`
— *not* in a side `<lstack>`. `#loop(rangeObj(I+ST,…))` sits directly in `<k>`, so the
circularity inducts on the integer bound. This mirrors `wasm-semantics/tests/proofs/loops-spec.k`,
where the loop-back `label { #loop(…) }` lives in `<instrs>` and `#br(0)` (continue) jumps to it
in-cell.

The in-cell shape is a **config choice** (one fewer cell than RV's `<lstack>` resume model),
*not* the reason this proof closes: a `<lstack>` resume proves a symbolic counter just as well —
see [`reference/notes/lstack-probe/`](../../../notes/lstack-probe/INVESTIGATION.md), which
disproves the earlier "side-cell jams on a counter" guess. What makes a counter-loop proof close
is the **summary** (next section).

```
#loop(rangeObj(I, HI, ST), T, B) => bind T:=I ~> B ~> loopLbl(#loop(rangeObj(I+ST, HI, ST), T, B))  [inRange]
#loop(rangeObj(I, HI, ST), _, _) => .K                                                              [done]
loopLbl(NEXT) => NEXT          // body finished -> next iteration (in-cell)
```

Induction is on the **integer bound** (`I` climbs to `HI`), like `kprove-haskell/sum-spec.k`'s
`addCounter(N)`.

## The proof — closed form, not a fold that restates the loop

The invariant carries the **Gauss closed form** (no recursive summary): the work remaining at
counter `I` is `sum[I, N) = (N*(N-1) - I*(I-1)) / 2`. Closing the circularity forces Z3 to
discharge the algebra (including the floor `/2`), exactly as `sum-spec` proves `(N-1)*N/2`.

Two `[all-path]` claims (`spec.k`), over `MPY`'s `#loop`:

1. **Loop invariant (circularity).** `#loop(rangeObj(I, N, 1), "i", total += i) => .K`, leaving
   `total = B + (N*(N-1) - I*(I-1))/2`, for `0 <= I <= N`. The step (`I < N`) binds `i := I`,
   runs `total += I`, and the in-cell `loopLbl` runs the next iteration at `I+1`; Z3 discharges
   `I + (N(N-1) - (I+1)I)/2 == (N(N-1) - I(I-1))/2`. Base (`I == N`): `.K`, `total` unchanged.
2. **Entry claim.** `result = f(N)` (for `N >= 0`) runs to completion (`<k> => .K`) leaving the
   root scope's `result = N*(N-1)/2`.

The loop variable `i` is pre-bound (`i = 0`) for a stable scope shape (NOTES loop-var discipline).

## Reliability

- **Whole semantics.** `verification.k` imports `MPY`; the proof drives the *actual* `#loop` /
  `rangeObj` / `range` rules `krun` uses — no drift.
- **Non-vacuous.** Corrupting the entry postcondition to `N*(N-1)/2 +Int 1` fails the implication
  (no `#Top`, 0 parse errors).
- **Smoke.** `krun smoke.mpy --definition ../../../src/semantics-kompiled` runs the same rules
  concretely (`f(4)==6`, `f(5)==10`, `f(10)==45`); the proof drives them on a symbolic `N`.

## Scope

Step is assumed `> 0` (f only builds `range(n)`); a general `range(a, b, c)` proof would split
on the sign of `c`.
