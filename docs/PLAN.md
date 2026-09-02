> Historical planning document (July 2026): kept as the record of what was proposed and
> approved. Paths refer to the pre-reorganization layout; see the repo-root README.md for the
> current one.

# K-Framework CWM-Style Python Trace Data — Implementation Plan (v2)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce a tiny (9-sample), high-quality dataset of Python execution/verification traces in the spirit of Meta CWM's mid-training data (arXiv:2510.02387), generated from K-framework semantics — demonstrating what CPython-based tracing cannot provide: rule-level semantic annotation, symbolic traces with path conditions, and verification traces (specs, a loop invariant, proofs, a counterexample).

**Architecture:** Reuse the **klever reference Python semantics** (`~/projects/klever/verification/humaneval/reference/src/` — "MPY": ~2,100 lines of modern K, 23 modules, verified today on this machine: 39/39 concrete tests pass, 62 HumanEval problems machine-proved) together with its `py2mpy.py` frontend and its verification harness. We add only a thin tracing layer: a vendored copy with a `<trace>` cell, a `LineMark` statement, two instrumented frame rules, and Python extractors that turn final configurations / prover output into JSONL. **Nothing is built from scratch; no CWM token-format replication** — JSON is the canonical output, with Markdown renderings for human review.

**Tech Stack:** K v7.1.337 (installed, verified), klever MPY semantics + `py2mpy.py` (vendored at a pinned git sha), pyk (`pip install kframework==7.1.337` via `uv`), kore-rpc-booster + z3 (installed), CPython 3.12 `sys.settrace` for differential validation.

## Global constraints & runtime discipline (final review round)

- **Repo/commits:** private GitHub repo **`nlp-research-rosu/sample-data`**, branch **`master`** (created in T0 via `gh repo create`). Commit after every meaningful step, push after every task — commit often.
- **K-tool watchdogs — never wait blindly:** these programs are tiny, so every K invocation should finish in minutes. All calls are wrapped in `timeout` with budgets ≈2× the expected time: `kompile` llvm ≤ 600 s (observed ~2–4 min), `kompile` haskell ≤ 600 s (observed ~3–5 min), `krun`/`kast` ≤ 120 s (expected seconds), `kprove` ≤ 900 s (range-loop class proves in seconds–minutes), kore-rpc ≤ 120 s per request / ≤ 10 min per program. A fired timeout or anything running well past its expected time is treated as **stuck or looping** — kill it, inspect partial output/configuration, shrink the program or claim, and fix the cause; do not simply re-run with a bigger timeout. `kprove` additionally runs under a memory cap (klever's own `systemd-run … MemoryMax=8G` recipe, or `ulimit -v` fallback) so a runaway prover can't take down the box.

## Changes from v1 (feedback merge)

| # | Feedback | Change |
|---|---|---|
| 1 | Use the klever semantics at `~/projects/klever/.../reference/src/semantics` | Adopted wholesale. The fresh "MiniPy" semantics (v1 Tasks 1–3, ~1.5 days) is **deleted**; replaced by vendoring MPY + a ~60-line trace overlay. `py2mpy.py` replaces the planned `py2k.py`. The existing proven `range-loop` spec **is** sample C1. |
| 2 | Subset OK | Unchanged (samples stay int-only; the semantics itself covers much more — str/list/tuple/dict — noted in REPORT as headroom). |
| 3 | JSON fine; no verbatim CWM format | `render_cwm.py` and all `.cwm.txt` outputs **dropped**. JSONL keeps CWM's observation–action *structure* (locals-before-line, line, call/return/exception events). |
| 4 | Hours, not days; control complexity | Plan is now 6 tasks ≈ **4–6 h** with per-task timeboxes and explicit cut-lines (graceful degradation instead of overruns). |
| 5 | Keep refutation sample | Kept (C3). |

Two sample-inventory adjustments (flagging since the 9 were approved):
- **A4** was `safe_div(7,0)` / ZeroDivisionError → now `half_of_even(7)` / **AssertionError**. The MPY exception domain is exactly `AssertionError` (`<exc>` cell); adding ZeroDivisionError means semantics surgery, contrary to "control the complexity". Assertion-failure traces are equally CWM-relevant.
- **C1** was `sum_to_n` (while) → now the klever **`range-loop`** program (`total += i for i in range(n)`, Gauss closed form `n*(n-1)/2`). Identical mathematical content, and its invariant-circularity + entry claims are **already proved** over the full MPY semantics — we re-run and serialize instead of authoring. (`sum_to_n` remains sample A1 on the concrete side.)

---

## 1. Verified findings about the reuse target (all checked today on this machine)

- **Location:** `~/projects/klever/verification/humaneval/reference/` (`src/semantics/*.k` = 23 modules / ~2,100 lines; `src/lemmas/*.k` = 13 proof-side files; `tests/`, `notes/` probes, `README.md`, `METHODOLOGY.md`, `CANONICAL-GAPS.md`). Actively developed — latest commits **2026-07-14**.
- **Coverage:** ints/bools/None/str/float, lists/tuples/sets/dicts, full operator family incl. floored `//`/`%` (`pyMod` — v1's Python-fidelity concern already solved), `if`/ternary/`for`/`while`/`break`/`continue`, functions/recursion/closures (with cell-based capture), builtins (`len sum abs min max ord chr range all any zip sorted list map enumerate int str float ...`), `assert` (sets `<exc> AssertionError`, `<exit-code> 1`), comprehensions.
- **Program format:** `.mpy` = AST-constructor terms (`Module(Assign(Name("x"), Int(5)) ...)`) generated by `~/projects/klever/scripts/py2mpy.py`, a pure CPython-`ast`→K transliterator (v1's planned frontend, already written). It does **not** emit line numbers — the trace overlay adds them.
- **Build/run (executed, green):** `kompile src/semantics.k --backend llvm --main-module MPY-CONCRETE --syntax-module MPY-SYNTAX`; `tests/run.sh` = CPython-oracle + krun over 39 cases → **ALL PASS** (run today, fresh kompile, exit 0).
- **Verification harness:** per-case `verification.k` (imports full `MPY` — e.g. `tests/verification/range-loop`, "no copied cut") or per-question minimal copy-select semantics (`questions/*/`); `kprove spec.k --spec-module <CASE>-SPEC` → `#Top`; memory-capped via `systemd-run`, patterns documented in `PROOF.md` files. `range-loop` proves the symbolic Gauss sum with a loop-invariant circularity claim, `[all-path]`.
- **Key config cells** (what extractors read): `<k>`, `<env>` (current scope loc), `<scopes>` (loc → `scope(Map, parent)`), `<heap>`/`<heapLoc>` (list objects, closure cells), `<stack>` (`frame(continuation, callerEnv, savedLoc)`), `<ret>`, `<exc>`, `<exit-code>`.
- **Instrumentation points:** statement sequencing `core.k:126`; frame push `call.k:69` (`closureVal` apply); frame pop `functions.k:85` (`#pop`); assert-failure `assert.k:8` (no patch needed — final `<exc>`+`<exit-code>` suffice).
- Haskell-backend kompile of full `MPY` (`--main-module MPY`) — **verified today on this machine** (exit 0, one benign warning), independently of their `tests/verification` flow which exercises it routinely.

## 2. Product definition — 9 samples, JSONL canonical

| ID | Program (self-contained `.py`: defs + entry call) | Kind | Shows |
|----|---|---|---|
| A1 | `sum_to_n(5)` — while loop | concrete | locals evolution per line; k_rules annotations |
| A2 | `gcd(48, 18)` — recursion | concrete | call/return events, frame nesting |
| A3 | `collatz_steps(6)` — while + if/else + augassign | concrete | branching inside loop |
| A4 | `half_of_even(7)` — `assert x % 2 == 0` fails | concrete | AssertionError event, halt semantics |
| B1 | `abs_val(x)`, symbolic `x` | symbolic | 2-path tree, path conditions, witnesses |
| B2 | `classify_triangle(a,b,c)`, symbolic | symbolic | nested branching, ≥1 SMT-pruned infeasible path |
| C1 | klever `range-loop` (`f(n)`: sum of `range(n)`), symbolic `n ≥ 0` | verification | loop-invariant circularity + entry claim → `#Top` (re-run of existing proof) |
| C2 | `abs_val(x)` spec: `ret >= 0 and (ret == x or ret == -x)` | verification | branching proof → `#Top` (new, follows range-loop pattern) |
| C3 | `buggy_abs(x)` (no `x == 0` branch → returns `None`), same spec | verification | **refuted**: stuck claim state → counterexample `x = 0` → embedded concrete failing trace |

### JSONL schemas (unchanged from v1 except: no CWM-token rendering; `k_rules` ids may be rule source locations)

Concrete record:

```json
{"id": "concrete/sum_to_n/n=5", "kind": "concrete_trace",
 "source": {"file": "programs/sum_to_n.py", "code": "...", "entry": "sum_to_n", "args": {"n": 5}},
 "trace": [
   {"event": "call", "line": 1, "func": "sum_to_n", "locals": {"n": 5}},
   {"event": "line", "line": 2, "locals": {"n": 5},
    "k_rules": [{"rule": "controls.k:9 (Assign)", "desc": "write RHS value into the current scope"}]},
   {"event": "return", "line": 7, "value": 15, "locals": {"n": 5, "acc": 15, "i": 6}}],
 "provenance": {"generator": "krun(MPY-TRACED)+llvm", "k": "v7.1.337", "klever_sha": "<sha>",
                "validation": {"cpython_settrace": "exact_match", "cpython": "3.12.3"}}}
```

Symbolic record: `nodes[] {node, line, locals(symbolic, Python-rendered), path_condition}`, `edges[] {from, to, branch, k_rule}`, `leaves[] {node, event, value, path_condition, witness, witness_validated}`, `pruned_infeasible[]`. Verification record: `spec {requires, ensures, invariants[], claim_k}`, `result proved|refuted`, `proof_trace` (claims + prover summary; KCFG nodes/edges when available), `counterexample {model, failing_trace}` for C3. Every record carries provenance incl. the klever git sha.

## 3. Architecture — what we build (the thin layer)

```
cwm-alike-data/
├── PLAN.md  README.md  REPORT.md  Makefile
├── vendor/klever/            # pinned copy: src/semantics/, src/lemmas/, scripts/py2mpy.py, VENDOR.md (sha)
├── semantics/
│   ├── traced/               # the ONLY K we write:
│   │   ├── traced.k          #   top module MPY-TRACED: requires vendor modules + trace.k + 3 patched files
│   │   ├── trace.k           #   <trace>-cell events: LineMark stmt + lineEvt/callEvt/retEvt (~40 lines)
│   │   └── patched/          #   core.k (+ <trace> cell in config), call.k (+ callEvt on frame push),
│   │                         #   functions.k (+ retEvt on #pop) — each a ≤6-line diff, `make vendor-diff` shows it
├── frontend/py2mpy_traced.py # vendored py2mpy + `--linemarks` flag: interleaves LineMark(lineno) per stmt
├── programs/                 # 7 self-contained .py files (defs + entry call; args live in the file)
├── specs/                    # abs-val/ and buggy-abs/ dirs: {verification.k, spec.k} following tests/verification/range-loop
├── scripts/
│   ├── k2trace.py            # krun --output json → walk <trace>/<exc>/<scopes> → concrete JSONL
│   ├── validate.py           # sys.settrace differential (exact match) + symbolic-witness replay
│   ├── annotate.py           # proof-hints → k_rules per step (T2; has fallbacks)
│   ├── run_symbolic.py       # pyk kore-rpc branching explorer → symbolic JSONL
│   └── run_proofs.py         # kompile+kprove per spec dir → verification JSONL (+ stuck-state → counterexample)
└── data/{concrete,symbolic,verification}/*.jsonl + *.md
```

Trace overlay mechanics (settled during research):
- `trace.k`: `syntax Stmt ::= "LineMark" "(" Int ")"` and `syntax TraceEvt ::= lineEvt(Int, Map, Map) | callEvt(Vals) | retEvt(Val, Map)`. The LineMark rule appends `lineEvt(N, scopeMap, heap)` — locals **before** the statement executes, CWM-style; the heap snapshot lets the extractor deref `ref(_)` values per-step.
- `call.k` patch: the `closureVal` frame-push rule also appends `callEvt(ACC)`; `functions.k` patch: `#pop` also appends `retEvt(V, calleeScopeMap)`. Function names are resolved by the extractor from def-line tables (the frontend knows them).
- A4 needs **no** patch: extractor synthesizes the exception event from final `<exc> AssertionError </exc>` + the last lineEvt.
- Verification (C) and symbolic (B) families run against the **untouched vendored semantics** — the overlay exists only in the concrete traced build, so the proofs we re-run/author are exactly klever's discipline.

## 4. Tasks (timeboxed; each ends with a commit)

### Task 0: Scaffold + env (20 min)
- [ ] `git init -b master`; create the private repo `gh repo create nlp-research-rosu/sample-data --private`, add it as `origin`, and push `master` (every task below ends with commit + push).
- [ ] Vendor `reference/src/{semantics,lemmas}` + `tests/verification/range-loop` + `scripts/py2mpy.py` from klever at HEAD, record sha in `vendor/klever/VENDOR.md`.
- [ ] `uv venv .venv && uv pip install 'kframework==7.1.337' pyyaml` (uv installed via astral.sh script; nix/`kup shell` is the fallback).
- [ ] `Makefile`: `check-env` (K version grep, `import pyk`, z3 present), `kompile-traced`, `kompile-haskell`, `data`, `validate`, `vendor-diff`. Run `make check-env` → `env OK`. Commit.

### Task 1: Traced build + concrete samples A1–A4 (90 min)
- [ ] Write `trace.k` + the 3 patched files; `kompile semantics/traced/traced.k --backend llvm --main-module MPY-TRACED --syntax-module MPY-TRACED-SYNTAX` (syntax module extends MPY-SYNTAX with LineMark).
- [ ] `py2mpy_traced.py --linemarks`: interleave `LineMark(node.lineno)` before each `Stmt` in every statement sequence (module body, function bodies, branch/loop bodies). Golden check: without `--linemarks` output is byte-identical to vendored py2mpy on all 7 programs.
- [ ] Write the 4 A-programs; `krun --definition build/traced <prog>.mpy --output json`; `k2trace.py` walks the JSON: `<trace>` ListItems → events (render `Val`s Python-style; filter `$cells`; deref refs against the per-event heap snapshot; synthesize A4's exception event from `<exc>`).
- [ ] `validate.py`: `sys.settrace` reference runner; normalize (def-line call events, `noneV`↔`None`); require **exact** event/line/locals match for A1–A4. Emit `data/concrete/*.jsonl` + `.md`. Commit.
- Cut-line: if `callEvt`/`retEvt` patches misbehave, A1/A3/A4 ship line-events-only and A2 is deferred — but the patches are ≤6 lines each, low risk.

### Task 2: `k_rules` annotations (60 min timebox)
- [ ] Re-kompile traced build with `--llvm-proof-hint-instrumentation` (flag verified); run A1; parse with `pyk.kllvm.hints.prooftrace`; map rule ordinals → source `file.k:line` (+ label when present); segment the rule stream between LineMark applications; attach as `k_rules` to each step.
- [ ] `rules.yaml`: one-line `desc` for every rule the A-samples exercise (the semantics files are richly commented — descriptions largely transcribe).
- [ ] Fallback chain if hints parsing fights the timebox: (1) kore-rpc `execute` with `log-successful-rewrites` on the Haskell build for A1 only; (2) static per-construct rule maps (statement kind → known rule sequence from the semantics). Either still populates `k_rules`; provenance records which generator produced it. Regenerate A-family, re-validate, commit.

### Task 3: Symbolic samples B1–B2 (75 min)
- [ ] Kompile untouched vendor semantics with `--backend haskell --main-module MPY` (independent re-check of what `tests/verification` flow already exercises).
- [ ] Write B-programs; `run_symbolic.py`: py2mpy the program with a magic-constant placeholder for the symbolic arg; parse to KAst via pyk and substitute a sorted K variable (`X:Int`); wrap in the initial configuration; drive kore-rpc `execute` — on `BRANCHING`, record the branch condition + rule, fork, continue to terminal states (loop-free programs; depth cap 2,000).
- [ ] Per leaf: `get-model` → witness; replay through CPython **and** the traced LLVM build; assert the concrete line path matches the tree branch (`witness_validated`). B2 must show ≥1 infeasible branch under `pruned_infeasible` (adjust condition order if needed — that's B2's point). Emit JSONL + `.md`. Commit.
- Cut-line: if pyk config-building drags, B-family init states reuse the exact `<k>`-cell shape of klever's entry claims (FuncDef … Assign(result, Call(f, X:Int))) pasted as a claim-less exploration start — same term, less plumbing.

### Task 4: Verification samples C1–C3 (60 min)
- [ ] C1: re-run klever's `range-loop` (kompile per-dir verification.k + `kprove spec.k` → `#Top`, their verify.sh recipe incl. memory cap); serialize claim sources (entry + invariant circularity, both quoted verbatim), Pythonic spec rendering, verdict, prover stats into JSONL.
- [ ] C2: `specs/abs-val/{verification.k,spec.k}` following the range-loop pattern verbatim (imports full MPY; entry-style claim with `X:Int`, `ensures (?R >=Int 0) andBool ((?R ==Int X) orBool (?R ==Int 0 -Int X))`, `[all-path]`); kprove → `#Top`.
- [ ] C3: same spec over `buggy_abs` → kprove fails; capture the stuck-claim-state output (kore-exec prints term + path condition, as seen in smoke tests); extract the counterexample (`x = 0` from the PC), replay `buggy_abs(0)` through the T1 pipeline, embed as `counterexample.failing_trace`. Emit JSONL + `.md`. Commit.
- Cut-line: `proof_trace` detail is best-effort — claims + verdict + prover summary always; pyk `APRProof`/KCFG node-edge serialization only if it fits the timebox (provenance marks the detail level).

### Task 5: Validation sweep + REPORT + README (40 min)
- [ ] `make data && make validate` from clean checkout regenerates and re-validates everything (differential checks, witness replays, `#Top` greps).
- [ ] `README.md`: schemas, regeneration, normalization rules, klever attribution + sha.
- [ ] `REPORT.md` (the pitch): (1) framing — CWM showed execution traces teach world-modeling; K makes them *semantics-grounded*; (2) table: sys.settrace vs K (faithful ✓/✓ · rule-annotated ✗/✓ · symbolic ✗/✓ · specs/invariants/proofs ✗/✓ · counterexamples ✗/✓); (3) one worked excerpt per family; (4) trust story: traces validated event-exact against CPython, proofs machine-checked, the underlying semantics CPython-oracle-tested (39/39) and already carrying 62 proved HumanEval problems; (5) scaling note: the harness maps over any py2mpy-covered corpus and any K-defined language. Final commit.

## 5. Risks

| Risk | Level | Handling |
|---|---|---|
| Proof-hints parsing (T2) | medium | 60-min timebox + two fallbacks; JSONL field identical either way |
| Full-MPY haskell kompile hiccup (T3) | retired — kompile verified green on this machine today | (fallback would have been copy-select minimal modules per klever README discipline) |
| pyk pip install | low | `kup shell` via nix; T1/T4 need no pyk at all (krun `--output json`, kprove CLI) |
| C2 proof slow/stuck | low (trivial branching; their suite proves harder things in seconds) | bound `X` (`-100 ≤ X ≤ 100`) — still a symbolic proof |
| py2mpy `--linemarks` patch awkwardness | low | it's our vendored fork; golden byte-identity check keeps drift at zero |
| Traced-build divergence from vendor | low | `make vendor-diff` (3 files, ≤6 lines each) + A-family differential validation catches behavior drift |

## 6. Effort

T0 20m · T1 90m · T2 60m (timebox) · T3 75m · T4 60m · T5 40m ≈ **5¾ h worst case, ~4 h expected** — cut-lines convert overruns into documented detail-level reductions, not schedule slips.

## 7. Standing decisions (from review)

1. klever MPY semantics reused wholesale; fresh semantics abandoned (feedback #1).
2. Int-only sample programs; semantics headroom (str/list/…) noted in REPORT (feedback #2).
3. JSON canonical; no CWM token replication (feedback #3).
4. Complexity controlled: 6 tasks, timeboxed, ~4–6 h (feedback #4).
5. C3 refutation sample retained (feedback #5).
6. **Needs reviewer eyes:** A4 exception swapped to AssertionError; C1 swapped to klever's proven `range-loop` Gauss sum (§ "Changes from v1").
