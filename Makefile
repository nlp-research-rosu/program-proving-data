# K-generated CWM-style (Code World Model) trace data — build & validation entry points.
# Runtime discipline: every K tool call runs under `timeout` sized ~2x its
# expected time (programs are tiny). A fired timeout means STUCK/LOOPING —
# diagnose, do not blindly re-run bigger (see docs/PLAN.md).
SHELL := /bin/bash
K_VER := v7.1.337
# .venv/bin/python when present (pip install kframework==7.1.337 there, needed only for
# regeneration); plain python3 suffices for k-validate.
PY    := $(if $(wildcard .venv/bin/python),.venv/bin/python,python3)

T_KOMPILE := timeout 600
T_KRUN    := timeout 120
T_KPROVE  := timeout 900

VENDOR_SEM := vendor/klever/src/semantics.k

.PHONY: check-env vendor-diff k-data k-data-concrete k-data-symbolic k-data-verification k-validate \
        lean-gen lean-build clean

check-env:
	@command -v kompile >/dev/null || { echo "kompile not found (need K $(K_VER))"; exit 1; }
	@kompile --version | grep -q $(K_VER) || { echo "K version mismatch (want $(K_VER))"; exit 1; }
	@$(PY) -c "import pyk, pyk.kore.rpc, pyk.kllvm.hints.prooftrace" || exit 1
	@command -v z3 >/dev/null || { echo "z3 missing"; exit 1; }
	@echo "env OK"

# ---- kompiled definitions --------------------------------------------------
build/k/traced: semantics/mpy-traced/traced.k semantics/mpy-traced/trace.k $(wildcard semantics/mpy-traced/patched/*.k)
	$(T_KOMPILE) kompile semantics/mpy-traced/traced.k --backend llvm \
	  --main-module MPY-TRACED --syntax-module MPY-TRACED-SYNTAX \
	  --output-definition build/k/traced

build/k/traced-hints: semantics/mpy-traced/traced.k semantics/mpy-traced/trace.k $(wildcard semantics/mpy-traced/patched/*.k)
	$(T_KOMPILE) kompile semantics/mpy-traced/traced.k --backend llvm \
	  --llvm-proof-hint-instrumentation \
	  --main-module MPY-TRACED --syntax-module MPY-TRACED-SYNTAX \
	  --output-definition build/k/traced-hints

build/k/mpy-haskell: $(VENDOR_SEM)
	$(T_KOMPILE) kompile $(VENDOR_SEM) --backend haskell \
	  --main-module MPY --syntax-module MPY-SYNTAX \
	  --output-definition build/k/mpy-haskell

build/k/traced-sym: semantics/mpy-traced/traced.k semantics/mpy-traced/trace.k $(wildcard semantics/mpy-traced/patched/*.k)
	$(T_KOMPILE) kompile semantics/mpy-traced/traced.k --backend haskell \
	  --main-module MPY-TRACED-SYM --syntax-module MPY-TRACED-SYNTAX \
	  --output-definition build/k/traced-sym

# ---- data generation -------------------------------------------------------
k-data-concrete: build/k/traced build/k/traced-hints
	$(PY) scripts/k/run_concrete.py && $(PY) scripts/k/annotate.py

k-data-symbolic: build/k/traced-sym build/k/traced
	$(PY) scripts/k/run_symbolic.py

k-data-verification: build/k/traced
	$(PY) scripts/k/run_proofs.py

k-data: k-data-concrete k-data-symbolic k-data-verification

k-validate:
	$(PY) scripts/k/validate.py

# ---- lean pipeline (data/lean) ----------------------------------------------
LEAN_PROGS := sum_to_n gcd buggy_abs collatz_steps abs_val half_of_even classify_triangle \
              kb_assign kb_swap kb_chain kb_double_half kb_arith_mix kb_abs kb_max kb_min \
              kb_countdown kb_max3 kb_clamp kb_abs_times kb_countup kb_sum kb_add_loop \
              kb_sub_loop kb_mult_loop kb_triangle_down kb_sum_up kb_sumdiff \
              kb_count_even kb_loop_max kb_pipeline kb_stats_pipeline kb_normalize_count \
              kb_pure_nested kb_mult_nested kb_triangle_nested kb_squares_cubic \
              kb_rows_sum_nested kb_nested_with_branch

build/lean/minipy-lean: semantics/minipy-lean.k
	$(T_KOMPILE) kompile semantics/minipy-lean.k --backend llvm \
	  --main-module MINIPY-LEAN --syntax-module MINIPY-LEAN-SYNTAX \
	  --output-definition build/lean/minipy-lean

build/lean/minipy-lean-hints: semantics/minipy-lean.k
	$(T_KOMPILE) kompile semantics/minipy-lean.k --backend llvm \
	  --llvm-proof-hint-instrumentation \
	  --main-module MINIPY-LEAN --syntax-module MINIPY-LEAN-SYNTAX \
	  --output-definition build/lean/minipy-lean-hints
	rm -f build/lean/hints-header.bin build/lean/*.hints build/lean/*.hints.txt  # stale header segfaults kore-proof-trace

# regenerate the theorem files (proofs included); idempotent vs the committed package.
# klean base modules (Prelude/Sorts/Inj/Func/Rewrite) are regenerated manually when the
# semantics changes — klean emits a fresh package skeleton, so run it in a scratch dir and
# copy the five modules (see REPORT.md).
lean-gen: build/lean/minipy-lean build/lean/minipy-lean-hints
	mkdir -p build/lean/mpy
	for p in $(LEAN_PROGS); do \
	  $(PY) scripts/py2mpy_traced.py programs/$$p.py --no-linemarks > build/lean/mpy/$$p.mpy; done
	$(PY) scripts/lean/gen_lean_traces.py --prove
	$(PY) scripts/lean/gen_lean_symbolic.py
	$(PY) scripts/lean/gen_lean_paths.py

lean-build:
	cd data/lean && PATH="$$HOME/.elan/bin:$$PATH" lake build

# ---- provenance ------------------------------------------------------------
vendor-diff:
	@for f in core.k call.k functions.k; do \
	  echo "=== $$f ==="; \
	  diff -u vendor/klever/src/semantics/$$f semantics/mpy-traced/patched/$$f || true; \
	done

clean:
	rm -rf build
