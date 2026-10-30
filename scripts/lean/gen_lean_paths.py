#!/usr/bin/env python3
"""gen_lean_paths — emit the PROVED ∀-quantified symbolic-path theorem files
`KMiniPy/Symbolic/B1AbsVal.lean` (paths of `abs_val`) and
`KMiniPy/Symbolic/B2ClassifyTriangle.lean` (paths of `classify_triangle`).

Method: witness generalization. Each path is generated CONCRETELY with the
machinery of gen_lean_traces (krun --depth config sweep, proof-hint rule
sequence, per-step constructor with explicit cool-HOLE named implicits) at a
witness input on that path, and then a pure TEXT substitution parameterizes
every emitted piece: the full printed literal terms `(SortExpr.«Int(_)…» w)`
/ `(SortVal.«intV(_)…» w)` of each witness literal become the path's bound
variable (B1's negated result becomes `(0 - x)`). Longest/most-specific
templates are replaced first and a hard assert checks no witness digits
survive. Every step theorem carries the path's variable and hypothesis
binders, and the fold threads them through.

B2 adds equivalence-class reduction: on four of the five paths some inputs
are EQUAL on-path, so a witness run holds equal concrete values and naive
per-variable substitution would be ambiguous. Instead an internal reduced
lemma quantifies ONE variable per on-path equivalence class (distinct
classes get distinct witness values, so substitution is unambiguous), and
the frozen public theorem recovers `(a b c)` by substituting its equality
hypotheses into the reduced lemma. The ≠ hypotheses are threaded through the
step theorems in BOTH orientations (`h` plus `Ne.symm h` at the fold call
sites): the program compares pairs in both orders, and `omega` (over the
`SortInt` abbrev) only picks up a hypothesis whose orientation matches the
goal.

Hypothesis discharge is the trace TACTIC extended with the applyCmp/applyBin
dispatchers + branch defs, the Int hooks, and the isKResult/andBool helpers,
closing by `first | rfl | omega` — `omega` picks the path conditions from
the context on the branch-deciding `cmp` steps; every other hypothesis is
ground modulo a symbolic payload and closes by `rfl` or the simp set.
Soundness is by Lean re-checking: the generalized steps elaborate for EVERY
input on the path or the build fails.

Endpoints are emitted as `(init …)` / `(final …)`; the script asserts every
path's substituted first/last sweep configs coincide with the shared
`init`/`final` bodies (up to the class-variable instance and the result
slot), so the public interface of the statement stage is preserved exactly.
B2 additionally asserts the `equal_pairs` counter stays ground (≤ 3) in
every parameterized term.

Watchdogs: every subprocess runs under timeout (krun 120 s each)."""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_lean_traces as glt  # noqa: E402  (also puts the venv pyk on sys.path)

from pyk.kore.parser import KoreParser  # noqa: E402

ROOT = glt.ROOT
PKG = glt.PKG

INT_LIT = "(SortExpr.«Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» {})"
VAL_INT = "(SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» {})"
VAL_STR = "(SortVal.«strV(_)_MINIPY-LEAN-SYNTAX_Val_String» {})"

WITNESS = 31337  # entry literal of programs/abs_val.py
W1, W2, W3 = 31337, 31338, 31339  # entry literals of programs/classify_triangle.py
TRI_GONE = (str(W1), str(W2), str(W3))

# The trace TACTIC's simp set (WF-mutual K functions + rule-branch defs +
# String hooks) extended with everything the path-condition hypotheses touch:
# applyCmp/applyBin dispatchers + branches, the Int hooks, and the
# isKResult/andBool helpers of the strictness hypotheses. Verified against
# the current Func.lean/Prelude.lean/Relations.lean by check_simp_names().
SIMP_NAMES = [
    # trace TACTIC set (gen_lean_traces.TACTIC)
    "«vsnoc(_,_)_MINIPY-LEAN_Vals_Vals_Val»", "_b922119", "_f20aa8c",
    "«snocW(_,_,_)_MINIPY-LEAN_Stmts_Stmts_Expr_Stmts»", "_0e7f4fe", "_50a6500",
    "«lookup(_,_)_MINIPY-LEAN_OptVal_Env_String»", "_639b4ef", "_95e90d4", "_9ce0d02",
    "«update(_,_,_)_MINIPY-LEAN_Env_Env_String_Val»", "_bd0f5e0", "_c952276", "_f3c9862",
    "«flookup(_,_)_MINIPY-LEAN_OptFun_Funs_String»", "_ae92d99", "_efd7dee", "_f5f3f2e",
    "«_=/=String__STRING-COMMON_Bool_String_String»", "_f390a9b",
    "notBool_", "_17ebc68", "_53fc758",
    # applyCmp dispatcher + branches
    "«applyCmp(_,_,_)_MINIPY-LEAN_Val_String_Val_Val»",
    "_0ddec05", "_0f91d65", "_148f5b4", "_1a7b0ca", "_53572c8", "_7ef5a32",
    # applyBin dispatcher + branches
    "«applyBin(_,_,_)_MINIPY-LEAN_Val_String_Val_Val»",
    "_2d811e1", "_3439d27", "_4b97627", "_6c7c2e8", "_969013d",
    # floored division/modulus (kb ports: symbolic `//` operands)
    "«floorDiv(_,_)_MINIPY-LEAN_Int_Int_Int»", "_08cef47",
    "«floorMod(_,_)_MINIPY-LEAN_Int_Int_Int»", "_bd04896",
    # Int hooks (+ the Relations.lean notation-restoring lemmas: klean applies
    # Int.emod/Int.ediv as raw constants, which omega cannot read)
    "«_<Int_»", "«_<=Int_»", "«_>Int_»", "«_>=Int_»", "«_==Int_»",
    "«_=/=Int_»", "_4de6e05", "«_+Int_»", "«_-Int_»", "«_*Int_»", "_modInt_", "«_/Int_»",
    "intEmodEq", "intEdivEq",
    # strictness-hypothesis helpers
    "isKResult", "_f4c2469", "_afefecb", "_andBool_", "_5b9db8d", "_61fbef3",
    # String-hook interpretation + Alternative guard
    "eqStringHook", "guard",
]

# closer: rfl for ground goals; omega for comparison side conditions; the
# last alternative handles klean's Int-typed value equalities — the goals are
# stated at the SortInt abbrev, whose `@Eq SortInt` head omega refuses, so
# retype with `show @Eq Int _ _` (defeq), bridge K's truncating `_/Int_`
# (Int.tdiv, unreadable by omega) to ediv under a divisibility fact omega CAN
# discharge, and finish with omega.
TACTIC = ("first | rfl | (simp [" + ", ".join(SIMP_NAMES)
          + "] <;> first | rfl | omega"
          + " | ((try show @Eq Int _ _)"
          + " <;> (try rw [Int.tdiv_eq_ediv_of_dvd (by omega)]) <;> omega))")


def check_simp_names() -> None:
    """klean regenerations keep uids stable but reorder declarations; make
    sure every simp lemma name still exists before emitting it."""
    src = "\n".join((PKG / "KMiniPy" / f).read_text()
                    for f in ("Func.lean", "Prelude.lean", "Relations.lean"))
    for name in SIMP_NAMES:
        if name == "guard":  # core Alternative, not a klean def
            continue
        if not re.search(rf"(def|axiom|theorem)\s+{re.escape(name)}[\s(:]", src):
            raise AssertionError(f"simp lemma {name!r} not found in klean base modules")


def subst(text: str, subs: list[tuple[str, str]], gone: tuple[str, ...]) -> str:
    """Apply the ordered witness->variable template replacements, then assert
    the witness digits are gone (any leftover means an unanticipated printed
    form and the generalized term would silently mention the witness)."""
    for old, new in subs:
        text = text.replace(old, new)
    for w in gone:
        assert w not in text, f"witness literal {w} survived substitution: {text[:400]}"
    return text


def assert_counters_ground(text: str, limit: int = 3) -> None:
    """Every Int literal left in a parameterized term must be one of the
    path-constant ground values (B2: the equal_pairs counter 0..3 and the
    program literals 0/1/3; C1: the initializers/increment 0/1) — anything
    larger means a witness leaked through."""
    for d in re.findall(r"» (\d+)\)", text):
        assert int(d) <= limit, f"unexpected ground int {d} in parameterized term"


def step_proof(label: str, arities, rule, subject, printer) -> str:
    """gen_lean_traces.step_proof with the extended path TACTIC (glt's own is
    kept byte-identical for the concrete pipeline)."""
    ndefs, has_req = arities[label]
    named = ""
    if rule is not None and subject is not None:
        binds: dict = {}
        needs: set = set()
        glt.match_lhs(rule.lhs, subject, binds, needs)
        for ident in sorted(needs):
            if ident in binds:
                val = printer._transform_pattern(binds[ident], concrete=True)
                named += f" ({ident} := {val})"
    args = [f"(by {TACTIC})"] * (ndefs + (1 if has_req else 0))
    return f"Rewrites.{label}" + named + ("".join(f" {a}" for a in args) if args else "")


def gen_path(stem: str, mpy_text: str, subs: list[tuple[str, str]], gone: tuple[str, ...],
             printer, arities, ord2label, rule_by_label):
    """Sweep + prove one path at its witness; return the parameterized
    (config terms, step proofs, n_steps)."""
    mpy = ROOT / "build/lean/mpy" / f"{stem}.mpy"
    mpy.write_text(mpy_text)
    ordinals = glt.rule_sequence(stem, mpy)
    labels = [ord2label[o] for o in ordinals]
    n = len(labels)
    configs = glt.sweep(mpy)
    assert len(configs) == n + 1, f"{stem}: {len(configs)} configs vs {n} rules"
    kpats = [KoreParser(c).pattern() for c in configs]
    cterms = [subst(str(printer._transform_pattern(p, concrete=True)), subs, gone)
              for p in kpats]
    steps = []
    for i, lbl in enumerate(labels):
        sp = subst(step_proof(lbl, arities, rule_by_label.get(lbl), kpats[i], printer),
                   subs, gone)
        steps.append((lbl, sp))
    return cterms, steps, n


def emit_path(prefix: str, var_params: str, var_args: str, binders: str, fold_args: str,
              init_ref: str, final_ref: str, cterms, steps, n: int) -> tuple[str, str]:
    """Config defs + step theorems (parameterized, single-line bodies), and
    the tran-fold proof threading the variables/hypotheses through every step."""
    parts = []
    for i in range(1, n):
        parts.append(f"def c{prefix}_{i} {var_params} : SortGeneratedTopCell :=\n  {cterms[i]}\n")
    for i, (_lbl, sp) in enumerate(steps):
        a = init_ref if i == 0 else f"(c{prefix}_{i} {var_args})"
        b = final_ref if i == n - 1 else f"(c{prefix}_{i+1} {var_args})"
        parts.append(f"theorem {prefix}_step_{i} {binders} : "
                     f"Rewrites {a} {b} := {sp}\n")
    fold = glt.tran_fold([f"{prefix}_step_{i} {fold_args}" for i in range(n)])
    return "\n".join(parts), fold


# ---------------------------------------------------------------------------
# B1: abs_val — two paths, one variable
# ---------------------------------------------------------------------------

def gen_b1(printer, arities, ord2label, rule_by_label) -> None:
    gone = (str(WITNESS),)
    src = (glt.REPO / "programs" / "abs_val.py").read_text()
    abs_mpy = (ROOT / "build/lean/mpy" / "abs_val.mpy").read_text()

    # nonneg path: witness 31337 as-is; both literal forms become x
    nonneg_subs = [(INT_LIT.format(WITNESS), INT_LIT.format("x")),
                   (VAL_INT.format(WITNESS), VAL_INT.format("x"))]
    # neg path: witness -31337 (printer renders it "(-31337)"); the witness
    # forms become x FIRST, then the computed result 0 - (-31337) = 31337
    # (value form only — it is never a program literal) becomes (0 - x)
    neg_subs = [(INT_LIT.format(f"(-{WITNESS})"), INT_LIT.format("x")),
                (VAL_INT.format(f"(-{WITNESS})"), VAL_INT.format("x")),
                (VAL_INT.format(WITNESS), VAL_INT.format("(0 - x)"))]

    non_cterms, non_steps, n_non = gen_path(
        "b1_nonneg", abs_mpy, nonneg_subs, gone,
        printer, arities, ord2label, rule_by_label)
    neg_cterms, neg_steps, n_neg = gen_path(
        "b1_neg", abs_mpy.replace(str(WITNESS), f"-{WITNESS}"), neg_subs, gone,
        printer, arities, ord2label, rule_by_label)

    # endpoints: both parameterized depth-0 configs must be the SAME init
    # body, and the last configs the SAME final body up to the result slot
    init_body = non_cterms[0]
    assert neg_cterms[0] == init_body, "neg/nonneg depth-0 configs disagree after substitution"
    assert non_cterms[-1].count(VAL_INT.format("x")) == 1, "result slot not unique in nonneg final"
    final_body = non_cterms[-1].replace(VAL_INT.format("x"), "v")
    assert neg_cterms[-1] == non_cterms[-1].replace(VAL_INT.format("x"), VAL_INT.format("(0 - x)")), \
        "neg final config does not match the final body's result slot"

    non_defs, non_fold = emit_path("nonneg", "(x : SortInt)", "x",
                                   "(x : SortInt) (h : 0 ≤ x)", "x h",
                                   "(init x)", "(final (iV x))",
                                   non_cterms, non_steps, n_non)
    neg_defs, neg_fold = emit_path("neg", "(x : SortInt)", "x",
                                   "(x : SortInt) (h : x < 0)", "x h",
                                   "(init x)", "(final (iV (0 - x)))",
                                   neg_cterms, neg_steps, n_neg)

    rec_neg = f"set_option maxRecDepth {max(2048, 16 * n_neg)} in\n"
    rec_non = f"set_option maxRecDepth {max(2048, 16 * n_non)} in\n"

    body = f"""import KMiniPy.Relations

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform (x h) binders; h used only on branch steps

/-! B1: symbolic execution of `abs_val` — one theorem per path, quantified
over every integer input on that path. PROVED by witness generalization:
each path is generated concretely at a witness input (neg: -{WITNESS},
nonneg: {WITNESS}) with the concrete-trace pipeline, then every witness
literal in the printed configurations and rule arguments is generalized to
the bound variable `x` (the negated result to `0 - x`); each step theorem
carries the path condition `h`, and the branch-deciding `cmp` hypothesis
closes by `omega` from `h`. Lean re-checks every step for ALL `x` on the path.
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: {n_neg}-step (neg) and {n_non}-step (nonneg) tran-folds of rule applications.
-/

namespace B1AbsVal

def init (x : SortInt) : SortGeneratedTopCell :=
  {init_body}

def final (v : SortVal) : SortGeneratedTopCell :=
  {final_body}

{neg_defs}
{rec_neg}/-- Negative path: for every x < 0 the program rewrites to result `-x`. -/
theorem path_neg (x : SortInt) (h : x < 0) :
    Rewrites (init x) (final (iV (0 - x))) :=
  {neg_fold}

{non_defs}
{rec_non}/-- Non-negative path: for every 0 ≤ x the program rewrites to result `x`. -/
theorem path_nonneg (x : SortInt) (h : 0 ≤ x) :
    Rewrites (init x) (final (iV x)) :=
  {non_fold}

end B1AbsVal
"""
    out = PKG / "KMiniPy" / "Symbolic" / "B1AbsVal.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body)
    print(f"[ok] B1AbsVal: proved, {n_neg} steps (neg) + {n_non} steps (nonneg)")


# ---------------------------------------------------------------------------
# B2: classify_triangle — five paths, equivalence-class reduction
# ---------------------------------------------------------------------------

# tag, witness triple, literal -> class variable, class variables (binder
# order), reduced-lemma hypothesis binders, step-theorem hypothesis binders
# (both ≠ orientations: omega only picks up the orientation matching the
# goal), fold hypothesis args, init instance args, result string
B2_PATHS = [
    ("equilateral", (W1, W1, W1), {W1: "c"}, ("c",),
     "", "", "", "c c c", "equilateral"),
    ("iso_ab", (W1, W1, W3), {W1: "b", W3: "c"}, ("b", "c"),
     " (h : b ≠ c)", " (h : b ≠ c) (h' : c ≠ b)", " h (Ne.symm h)",
     "b b c", "isosceles"),
    ("iso_bc", (W1, W3, W3), {W1: "a", W3: "c"}, ("a", "c"),
     " (h : a ≠ c)", " (h : a ≠ c) (h' : c ≠ a)", " h (Ne.symm h)",
     "a c c", "isosceles"),
    ("iso_ac", (W1, W3, W1), {W1: "c", W3: "b"}, ("b", "c"),
     " (h : b ≠ c)", " (h : b ≠ c) (h' : c ≠ b)", " h (Ne.symm h)",
     "c b c", "isosceles"),
    ("scalene", (W1, W2, W3), {W1: "a", W2: "b", W3: "c"}, ("a", "b", "c"),
     " (h1 : a ≠ b) (h2 : b ≠ c) (h3 : a ≠ c)",
     " (h1 : a ≠ b) (h2 : b ≠ c) (h3 : a ≠ c) (h1' : b ≠ a) (h2' : c ≠ b) (h3' : c ≠ a)",
     " h1 h2 h3 (Ne.symm h1) (Ne.symm h2) (Ne.symm h3)",
     "a b c", "scalene"),
]

# frozen public statements: doc, hypothesis binders, glue from the reduced lemma
B2_PUBLIC = {
    "equilateral": ("All three sides equal.",
                    " (h1 : a = b) (h2 : b = c) (h3 : a = c)",
                    "subst h1; subst h2; exact equilateral_reduced _"),
    "iso_ab": ("Exactly one equal pair: a = b.",
               " (h1 : a = b) (h2 : b ≠ c) (h3 : a ≠ c)",
               "subst h1; exact iso_ab_reduced _ _ h2"),
    "iso_bc": ("Exactly one equal pair: b = c.",
               " (h1 : a ≠ b) (h2 : b = c) (h3 : a ≠ c)",
               "subst h2; exact iso_bc_reduced _ _ h1"),
    "iso_ac": ("Exactly one equal pair: a = c.",
               " (h1 : a ≠ b) (h2 : b ≠ c) (h3 : a = c)",
               "subst h3; exact iso_ac_reduced _ _ h2"),
    "scalene": ("No equal pair.",
                " (h1 : a ≠ b) (h2 : b ≠ c) (h3 : a ≠ c)",
                None),
}

B2_CLASSES = {
    "equilateral": "{a, b, c} → c",
    "iso_ab": "{a, b} → b, {c} → c",
    "iso_bc": "{a} → a, {b, c} → c",
    "iso_ac": "{a, c} → c, {b} → b",
}


def tri_instance(mpy: str, triple: tuple[int, int, int]) -> str:
    """classify_triangle mpy text with its three entry literals replaced by
    the witness triple (two-stage placeholders: triples may repeat values)."""
    out = mpy.replace(str(W1), "@1@").replace(str(W2), "@2@").replace(str(W3), "@3@")
    return (out.replace("@1@", str(triple[0]))
               .replace("@2@", str(triple[1]))
               .replace("@3@", str(triple[2])))


def init_instance(init_body: str, inst: str) -> str:
    """`init` body text instantiated at the path's class variables (two-stage
    placeholders: instances repeat variables)."""
    v1, v2, v3 = inst.split()
    t = (init_body.replace(INT_LIT.format("a"), "@A@")
                  .replace(INT_LIT.format("b"), "@B@")
                  .replace(INT_LIT.format("c"), "@C@"))
    return (t.replace("@A@", INT_LIT.format(v1))
             .replace("@B@", INT_LIT.format(v2))
             .replace("@C@", INT_LIT.format(v3)))


def gen_b2(printer, arities, ord2label, rule_by_label) -> None:
    src = (glt.REPO / "programs" / "classify_triangle.py").read_text()
    tri_mpy = (ROOT / "build/lean/mpy" / "classify_triangle.mpy").read_text()

    results = {}
    for tag, triple, litmap, _vars, _rh, _sh, _fh, _inst, _res in B2_PATHS:
        subs = []
        for lit, var in litmap.items():
            subs += [(INT_LIT.format(lit), INT_LIT.format(var)),
                     (VAL_INT.format(lit), VAL_INT.format(var))]
        cterms, steps, n = gen_path(f"b2_{tag}", tri_instance(tri_mpy, triple), subs,
                                    TRI_GONE, printer, arities, ord2label, rule_by_label)
        for t in cterms:
            assert_counters_ground(t)
        results[tag] = (cterms, steps, n)

    # endpoints: scalene (witness = the program's own literals, all classes
    # singletons) is the reference for the shared init/final bodies; every
    # path must coincide up to its class-variable instance / result slot
    init_body = results["scalene"][0][0]
    for slot in ("a", "b", "c"):
        assert init_body.count(INT_LIT.format(slot)) == 1, f"init slot {slot} not unique"
    scal_last = results["scalene"][0][-1]
    assert scal_last.count(VAL_STR.format('"scalene"')) == 1, "result slot not unique in scalene final"
    final_body = scal_last.replace(VAL_STR.format('"scalene"'), "v")
    for tag, _triple, _litmap, _vars, _rh, _sh, _fh, inst, res in B2_PATHS:
        cterms = results[tag][0]
        assert cterms[0] == init_instance(init_body, inst), \
            f"{tag}: depth-0 config does not match init at ({inst})"
        assert cterms[-1] == scal_last.replace(VAL_STR.format('"scalene"'),
                                               VAL_STR.format(f'"{res}"')), \
            f"{tag}: final config does not match the final body's result slot"

    sections = []
    nsteps = {}
    for tag, _triple, _litmap, vars_, red_hyps, step_hyps, fold_hyps, inst, res in B2_PATHS:
        cterms, steps, n = results[tag]
        nsteps[tag] = n
        var_params = "(" + " ".join(vars_) + " : SortInt)"
        var_args = " ".join(vars_)
        defs, fold = emit_path(tag, var_params, var_args, var_params + step_hyps,
                               var_args + fold_hyps, f"(init {inst})",
                               f'(final (sV "{res}"))', cterms, steps, n)
        rec = f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
        pub_doc, pub_hyps, glue = B2_PUBLIC[tag]
        if glue is None:  # scalene: all classes singletons — the public theorem IS the fold
            sections.append(f"""{defs}
{rec}/-- {pub_doc} -/
theorem path_{tag} (a b c : SortInt){pub_hyps} :
    Rewrites (init a b c) (final (sV "{res}")) :=
  {fold}
""")
        else:
            sections.append(f"""{defs}
{rec}/-- {tag} path reduced to one variable per on-path equivalence class
({B2_CLASSES[tag]}). -/
theorem {tag}_reduced {var_params}{red_hyps} :
    Rewrites (init {inst}) (final (sV "{res}")) :=
  {fold}

/-- {pub_doc} -/
theorem path_{tag} (a b c : SortInt){pub_hyps} :
    Rewrites (init a b c) (final (sV "{res}")) :=
  by {glue}
""")

    body = f"""import KMiniPy.Relations

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform path binders; hyps used only on branch steps

/-! B2: symbolic execution of `classify_triangle` — one theorem per feasible
path, quantified over every integer triple on that path. PROVED by witness
generalization with equivalence-class reduction: each path is generated
concretely at a witness triple with the concrete-trace pipeline, then every
witness literal is generalized to ONE bound variable per on-path equivalence
class (`*_reduced` lemmas; distinct classes get distinct witness values, so
the text substitution is unambiguous), and the public theorems recover the
full `(a b c)` statements by substituting their equality hypotheses into the
reduced lemmas. The branch-deciding `cmp` hypotheses close by `omega` from
the path's ≠ hypotheses (threaded in both orientations through the steps);
the `equal_pairs` counter is concrete on every path. The three contradictory
outcome combinations (exactly two sides equal implies the third pair equal)
have no theorem, matching the solver-pruned paths of the K record.
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: {nsteps['equilateral']}/{nsteps['iso_ab']}/{nsteps['iso_bc']}/{nsteps['iso_ac']}/{nsteps['scalene']}-step tran-folds (equilateral / iso_ab / iso_bc / iso_ac / scalene).
-/

namespace B2ClassifyTriangle

def init (a b c : SortInt) : SortGeneratedTopCell :=
  {init_body}

def final (v : SortVal) : SortGeneratedTopCell :=
  {final_body}

{chr(10).join(sections)}
end B2ClassifyTriangle
"""
    out = PKG / "KMiniPy" / "Symbolic" / "B2ClassifyTriangle.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body)
    print("[ok] B2ClassifyTriangle: proved, steps " +
          "/".join(str(nsteps[t]) for t, *_ in B2_PATHS) +
          " (equilateral/iso_ab/iso_bc/iso_ac/scalene)")


# ---------------------------------------------------------------------------
# C1 legs: sum_to_n — parametric execution fragments for the RL derivation
# ---------------------------------------------------------------------------
# The loop-head state of this While semantics is NOT iteration-uniform: every
# `whileUnfold` unfolds the body as a block whose emptied statement list stays
# in the continuation until loop exit, so the k cell grows by one
# `inj_SortStmts .List` frame per iteration (witnessed: k-cell text 1531 →
# 1636 → 1741 → 1846 chars at the first four whileUnfold configs). A
# self-looping `body_leg` over `loopCfg (n i acc)` alone is therefore
# unprovable; `loopCfg` takes the continuation below the While as an explicit
# `rest : SortK` parameter, and loop exit factors through `loopExit` (guard
# false, block residue popped up to `rest`) + `nil_step` (one residue frame) +
# `epilogue_leg` (return/frame pop/assign at the ground entry continuation
# `loopRest`). Composition: init n ⇒ loopCfg n 1 0 loopRest ⇒(body_leg)^k
# with rest = nil-frame^k loopRest ⇒ exit_leg ⇒ (nil_step)^k ⇒ epilogue_leg
# ⇒ final (iV acc).

NILSTMTS = 'SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»'
NIL_FRAME = "(SortK.kseq (SortKItem.inj_SortStmts " + NILSTMTS + ") rest)"


def rule_sequence_depth(stem: str, mpy: Path, depth: int | None = None) -> list[int]:
    """glt.rule_sequence with an optional --depth on the hints krun: leg
    extraction only needs a bounded prefix of a possibly very long run."""
    hints = ROOT / "build/lean" / f"{stem}.hints"
    txt = ROOT / "build/lean" / f"{stem}.hints.txt"
    header = ROOT / "build/lean/hints-header.bin"
    if not header.exists():
        subprocess.run(["timeout", "120", "kore-rich-header",
                        str(glt.HINTS_DEFN / "definition.kore"), "-o", str(header)], check=True)
    cmd = ["timeout", "120", "krun", "--definition", str(glt.HINTS_DEFN), str(mpy),
           "--proof-hint"]
    if depth is not None:
        cmd += ["--depth", str(depth)]
    with open(hints, "wb") as fh:
        subprocess.run(cmd, stdout=fh, check=True)
    with open(txt, "w") as fh:
        subprocess.run(["timeout", "300", "kore-proof-trace", "--verbose", str(header),
                        str(hints), str(glt.HINTS_DEFN / "definition.kore")], stdout=fh,
                       stderr=subprocess.STDOUT, check=True)
    labels, d = [], 0
    rule_re = re.compile(r"rule: (\d+) ")
    for line in txt.read_text().splitlines():
        if line.startswith("function:"):
            d += 1
        elif line.startswith("function exit:"):
            d -= 1
        elif line.startswith("rule:") and d == 0:
            labels.append(int(rule_re.match(line).group(1)))
    return labels


def sweep_range(mpy: Path, lo: int, hi: int) -> list[str]:
    """Configurations at depths lo..hi inclusive (kore text)."""
    return [glt.krun_kore(mpy, k) for k in range(lo, hi + 1)]


def swap_funs(cfg: str, stock_funs: str) -> str:
    """Replace the funs cell of a printed config with the stock function
    table. The body/exit witnesses seed `i`/`acc` through modified initializer
    literals, which also show up (inert) in the recorded function body; every
    leg rule frames the funs cell, so the swapped configurations take exactly
    the same steps — Lean re-checks each one."""
    assert cfg.count(" funs := ") == 1
    pre, rest_ = cfg.split(" funs := ", 1)
    assert rest_.count(", stack := ") == 1
    _, post = rest_.split(", stack := ", 1)
    return pre + " funs := " + stock_funs + ", stack := " + post


def funs_of(cfg: str) -> str:
    return cfg.split(" funs := ", 1)[1].split(", stack := ", 1)[0]


def kval_of(cfg: str) -> str:
    return cfg.split("{ k := { val := ", 1)[1].split(" }, env := ", 1)[0]


def gen_c1(printer, arities, ord2label, rule_by_label) -> None:
    src = (glt.REPO / "programs" / "sum_to_n.py").read_text()
    stock = (ROOT / "build/lean/mpy" / "sum_to_n.mpy").read_text()
    for anchor in ('Assign(Name("acc"), Int(0))', 'Assign(Name("i"), Int(1))', "Int(5)"):
        assert stock.count(anchor) == 1, f"seed anchor not unique: {anchor}"

    def seeded(acc0: int, i0: int, n0: int) -> str:
        """Witness program: the acc/i initializer literals and the call
        argument carry the witness values (they land in env at the loop head;
        the initializer copies inside the funs cell are swapped back out)."""
        return (stock
                .replace('Assign(Name("acc"), Int(0))', f'Assign(Name("acc"), Int({acc0}))')
                .replace('Assign(Name("i"), Int(1))', f'Assign(Name("i"), Int({i0}))')
                .replace("Int(5)", f"Int({n0})"))

    def prints(kores: list[str]):
        kpats = [KoreParser(c).pattern() for c in kores]
        raws = [str(printer._transform_pattern(p, concrete=True)) for p in kpats]
        return kpats, raws

    def build(kpats, raws, rules_slice, subs, gone, post=None):
        texts = [post(t) for t in raws] if post else list(raws)
        cterms = [subst(t, subs, gone) for t in texts]
        for t in cterms:
            assert_counters_ground(t, limit=1)
        steps = []
        for j, lbl in enumerate(rules_slice):
            sp = subst(step_proof(lbl, arities, rule_by_label.get(lbl), kpats[j], printer),
                       subs, gone)
            steps.append((lbl, sp))
        return cterms, steps, len(rules_slice)

    # init/final: exactly the statement-stage construction (byte-identity)
    stock_path = ROOT / "build/lean/mpy" / "c1_stock.mpy"
    stock_path.write_text(stock)
    _, (init_raw,) = prints([glt.krun_kore(stock_path, 0)])
    _, (final_raw,) = prints([glt.krun_kore(stock_path, None)])
    assert init_raw.count(INT_LIT.format(5)) == 1
    init_body = init_raw.replace(INT_LIT.format(5), INT_LIT.format("n"))
    assert final_raw.count(VAL_INT.format(15)) == 1
    final_body = final_raw.replace(VAL_INT.format(15), "v")
    final_at_acc = final_raw.replace(VAL_INT.format(15), VAL_INT.format("acc"))

    # ---- prologue: stock program at n := 31337, program start .. first
    # whileUnfold-start (bounded hints run: the full witness run is huge)
    pro_path = ROOT / "build/lean/mpy" / "c1_prologue.mpy"
    pro_path.write_text(stock.replace("Int(5)", "Int(31337)"))
    pro_rules = [ord2label[o] for o in rule_sequence_depth("c1_prologue", pro_path, depth=60)]
    pro_wu = [k for k, l in enumerate(pro_rules) if l == "whileUnfold"]
    assert pro_wu, "no whileUnfold within 60 steps"
    pro_kp, pro_raw = prints(sweep_range(pro_path, 0, pro_wu[0]))
    pro_subs = [(INT_LIT.format(31337), INT_LIT.format("n")),
                (VAL_INT.format(31337), VAL_INT.format("n"))]
    pro_ct, pro_steps, n_pro = build(pro_kp, pro_raw, pro_rules[:pro_wu[0]],
                                     pro_subs, ("31337",))
    assert pro_ct[0] == init_body, "prologue depth-0 config does not match init"
    stock_funs = funs_of(pro_ct[-1])  # ground: the stock function table

    # ---- exit witness: guard false at first whileUnfold (i := 31341 > n :=
    # 31339); yields S0 (the ground entry continuation), the exit leg
    # (whileUnfold-start .. residue popped, k = rest) and the epilogue leg
    exit_path = ROOT / "build/lean/mpy" / "c1_exit.mpy"
    exit_path.write_text(seeded(31337, 31341, 31339))
    exit_rules = [ord2label[o] for o in rule_sequence_depth("c1_exit", exit_path)]
    ewu = [k for k, l in enumerate(exit_rules) if l == "whileUnfold"]
    assert len(ewu) == 1, f"exit witness ran {len(ewu)} iterations"
    lo = ewu[0]
    sd = next(k for k in range(lo, len(exit_rules)) if exit_rules[k] == "seqDone")
    boundary = sd + 1  # first config with the block residue popped: k = rest
    exit_kp, exit_raw = prints(sweep_range(exit_path, lo, len(exit_rules)))
    s0 = kval_of(exit_raw[boundary - lo])
    assert s0.startswith("SortK.kseq (SortKItem.inj_SortStmts (SortStmts.«___"), s0[:80]

    def post_swap(t: str) -> str:
        return swap_funs(t, stock_funs)

    def post_swap_rest(t: str) -> str:
        t = swap_funs(t, stock_funs)
        assert t.count(s0) == 1, "loop continuation not unique in config"
        return t.replace(s0, "rest")

    exit_subs = [(VAL_INT.format(31341), VAL_INT.format("i")),
                 (VAL_INT.format(31339), VAL_INT.format("n")),
                 (VAL_INT.format(31337), VAL_INT.format("acc"))]
    exit_gone = ("31341", "31339", "31337")
    exit_ct, exit_steps, n_exit = build(exit_kp[:boundary - lo + 1], exit_raw[:boundary - lo + 1],
                                        exit_rules[lo:boundary], exit_subs, exit_gone,
                                        post=post_swap_rest)
    epi_ct, epi_steps, n_epi = build(exit_kp[boundary - lo:], exit_raw[boundary - lo:],
                                     exit_rules[boundary:], exit_subs, exit_gone,
                                     post=post_swap)
    loopexit_body = exit_ct[-1]
    assert loopexit_body.count("{ val := rest }") == 1
    assert epi_ct[0] == loopexit_body.replace("{ val := rest }", "{ val := " + s0 + " }"), \
        "epilogue start does not match loopExit at loopRest"
    assert epi_ct[-1] == final_at_acc, "epilogue end does not match final at (iV acc)"

    # ---- body: one guard-true iteration (i := 31337 ≤ n := 31339, acc :=
    # 31341), first whileUnfold-start .. second whileUnfold-start
    body_path = ROOT / "build/lean/mpy" / "c1_body.mpy"
    body_path.write_text(seeded(31341, 31337, 31339))
    body_rules = [ord2label[o] for o in rule_sequence_depth("c1_body", body_path)]
    bwu = [k for k, l in enumerate(body_rules) if l == "whileUnfold"]
    assert len(bwu) >= 2, "body witness ran fewer than one full iteration"
    body_kp, body_raw = prints(sweep_range(body_path, bwu[0], bwu[1]))
    body_subs = [(VAL_INT.format(62678), VAL_INT.format("(acc + i)")),
                 (VAL_INT.format(31341), VAL_INT.format("acc")),
                 (VAL_INT.format(31339), VAL_INT.format("n")),
                 (VAL_INT.format(31338), VAL_INT.format("(i + 1)")),
                 (VAL_INT.format(31337), VAL_INT.format("i"))]
    body_gone = ("62678", "31341", "31339", "31338", "31337")
    body_ct, body_steps, n_body = build(body_kp, body_raw, body_rules[bwu[0]:bwu[1]],
                                        body_subs, body_gone, post=post_swap_rest)
    loopcfg_body = body_ct[0]
    assert loopcfg_body.count("(rest)") == 1

    # ---- endpoint cross-asserts (text-level: the folds rely on the
    # definitional equalities these certify)
    def inst_loopcfg(n: str, i: str, acc: str, rest: str) -> str:
        t = (loopcfg_body.replace(VAL_INT.format("n"), "@N@")
             .replace(VAL_INT.format("i"), "@I@")
             .replace(VAL_INT.format("acc"), "@A@")
             .replace("(rest)", "@R@"))
        return (t.replace("@N@", VAL_INT.format(n)).replace("@I@", VAL_INT.format(i))
                 .replace("@A@", VAL_INT.format(acc)).replace("@R@", rest))

    assert exit_ct[0] == loopcfg_body, "exit-witness loop head does not match loopCfg"
    assert pro_ct[-1] == inst_loopcfg("n", "1", "0", "(" + s0 + ")"), \
        "prologue end does not match loopCfg n 1 0 loopRest"
    assert body_ct[-1] == inst_loopcfg("n", "(i + 1)", "(acc + i)",
                                       "(SortK.kseq (SortKItem.inj_SortStmts "
                                       + NILSTMTS + ") (rest))"), \
        "body end does not match loopCfg n (i+1) (acc+i) (nil-frame rest)"

    # ---- emit
    pro_defs, pro_fold = emit_path("prologue", "(n : SortInt)", "n", "(n : SortInt)", "n",
                                   "(init n)", "(loopCfg n 1 0 loopRest)",
                                   pro_ct, pro_steps, n_pro)
    vp = "(n i acc : SortInt) (rest : SortK)"
    va = "n i acc rest"
    body_defs, body_fold = emit_path("body", vp, va, vp + " (h : i ≤ n)", va + " h",
                                     "(loopCfg n i acc rest)",
                                     "(loopCfg n (i + 1) (acc + i) " + NIL_FRAME + ")",
                                     body_ct, body_steps, n_body)
    exit_defs, exit_fold = emit_path("exit", vp, va, vp + " (h : n < i)", va + " h",
                                     "(loopCfg n i acc rest)", "(loopExit n i acc rest)",
                                     exit_ct, exit_steps, n_exit)
    epi_defs, epi_fold = emit_path("epilogue", "(n i acc : SortInt)", "n i acc",
                                   "(n i acc : SortInt)", "n i acc",
                                   "(loopExit n i acc loopRest)", "(final (iV acc))",
                                   epi_ct, epi_steps, n_epi)
    recs = {t: f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
            for t, n in (("pro", n_pro), ("body", n_body), ("exit", n_exit), ("epi", n_epi))}

    body_txt = f"""import KMiniPy.Relations

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform leg binders; hyps used only on guard steps

/-! C1 execution legs for `sum_to_n` — the PROVED parametric path fragments
the reachability-logic derivation of C1 composes. Generated by witness
generalization exactly like the B1/B2 paths, extended to mid-execution
endpoints.

The loop-head state of this While semantics is not iteration-uniform: each
`whileUnfold` unfolds the loop body as a block whose emptied statement list
stays in the continuation until loop exit, so the k cell gains one
`inj_SortStmts .List` residue frame per iteration. `loopCfg` therefore takes
the continuation below the While statement as an explicit `rest : SortK`
parameter, and loop exit factors through `loopExit n i acc rest` (guard
false, unfolded-block residue popped, k cell = rest), `nil_step` (pops one
residue frame by `seqDone`), and `epilogue_leg` (return, frame pop, module
result assignment from the ground entry continuation `loopRest`).

Composition recipe (the k-th loop state has rest = nil-frame^k `loopRest`):
  init n
    ⇒ loopCfg n 1 0 loopRest                              (prologue_leg)
    ⇒ loopCfg n (i+1) (acc+i) (nil-frame rest)            (body_leg, i ≤ n)
    ⇒ loopExit n i acc rest                               (exit_leg, n < i)
    ⇒ loopExit n i acc loopRest                           (nil_step, k times)
    ⇒ final (iV acc)                                      (epilogue_leg)

The body/exit witnesses seed `i`/`acc` through the acc/i initializer
literals; the copies of those literals recorded (inertly) in the funs cell
are swapped back to the stock function table before parameterization — every
leg rule frames the funs cell, and Lean re-checks each emitted step.
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: {n_pro}-step prologue, {n_body}-step body, {n_exit}-step exit,
1-step nil_step, {n_epi}-step epilogue tran-folds of rule applications.
-/

namespace C1SumToN

def init (n : SortInt) : SortGeneratedTopCell :=
  {init_body}

def final (v : SortVal) : SortGeneratedTopCell :=
  {final_body}

/-- The ground continuation below the While statement on loop entry:
`[Return acc]` then the implicit `Return None`. -/
def loopRest : SortK :=
  {s0}

/-- Loop-head configuration at the START of a `whileUnfold` step: the k cell
is topped by the While statement over the continuation `rest`; `n`, `acc`,
`i` are the environment values. -/
def loopCfg (n i acc : SortInt) (rest : SortK) : SortGeneratedTopCell :=
  {loopcfg_body}

/-- Post-loop configuration: guard evaluated false, the exiting iteration's
block residue popped — the k cell IS the continuation `rest`. -/
def loopExit (n i acc : SortInt) (rest : SortK) : SortGeneratedTopCell :=
  {loopexit_body}

{pro_defs}
{recs['pro']}/-- Program start to the first loop-head state. -/
theorem prologue_leg (n : SortInt) :
    Rewrites (init n) (loopCfg n 1 0 loopRest) :=
  {pro_fold}

{body_defs}
{recs['body']}/-- Exactly one loop iteration: guard true, `acc += i`, `i += 1`; the
unfolded block leaves one residue frame on the continuation. -/
theorem body_leg (n i acc : SortInt) (rest : SortK) (h : i ≤ n) :
    Rewrites (loopCfg n i acc rest)
      (loopCfg n (i + 1) (acc + i) {NIL_FRAME}) :=
  {body_fold}

{exit_defs}
{recs['exit']}/-- Loop exit: guard false, the exiting unfold's residue popped; the k cell
becomes the continuation `rest`. -/
theorem exit_leg (n i acc : SortInt) (rest : SortK) (h : n < i) :
    Rewrites (loopCfg n i acc rest) (loopExit n i acc rest) :=
  {exit_fold}

/-- Loop-exit cleanup: one accumulated block-residue frame pops by `seqDone`. -/
theorem nil_step (n i acc : SortInt) (rest : SortK) :
    Rewrites (loopExit n i acc (SortK.kseq (SortKItem.inj_SortStmts {NILSTMTS}) rest))
      (loopExit n i acc rest) :=
  Rewrites.seqDone

{epi_defs}
{recs['epi']}/-- From the popped loop exit at the entry continuation: return `acc`, pop
the call frame, assign the module-level `result`. -/
theorem epilogue_leg (n i acc : SortInt) :
    Rewrites (loopExit n i acc loopRest) (final (iV acc)) :=
  {epi_fold}

end C1SumToN
"""
    out = PKG / "KMiniPy" / "Verification" / "C1Legs.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body_txt)
    print(f"[ok] C1Legs: proved, {n_pro} (prologue) + {n_body} (body) + {n_exit} (exit) "
          f"+ 1 (nil_step) + {n_epi} (epilogue) steps")


# ---------------------------------------------------------------------------
# C12 legs: kb_countdown — parametric execution fragments for the FIRST
# loop-program KleverBench mirror (RL derivation in C12KbCountdown.lean)
# ---------------------------------------------------------------------------
# Same while-unfolding residue discipline as C1 (see the C1 comment block),
# but module-level: no function call, no funs-table seeding (no swap_funs),
# one variable, no accumulator. The ground continuation below the While is
# the emptied module statement list over the empty k cell. Composition:
# init n ⇒ loopCfg n loopRest ⇒(body_leg)^k with rest = nil-frame^k loopRest
# ⇒ exit_leg ⇒ (nil_step)^k ⇒ epilogue_leg ⇒ final n (at n = 0).

KB12_WITNESS = 31337    # the stock init literal of programs/kb_countdown.py
KB12_EXIT_WITNESS = -7  # guard 0 < n false; avoids the program constants 0/1
                        # (witness 0 WOULD collide with the guard literal)


def gen_kb_countdown(printer, arities, ord2label, rule_by_label) -> None:
    src = (glt.REPO / "programs" / "kb_countdown.py").read_text()
    stock = (ROOT / "build/lean/mpy" / "kb_countdown.mpy").read_text()
    assert stock.count(f"Int({KB12_WITNESS})") == 1, "seed anchor not unique"

    def prints(kores: list[str]):
        kpats = [KoreParser(c).pattern() for c in kores]
        raws = [str(printer._transform_pattern(p, concrete=True)) for p in kpats]
        return kpats, raws

    def build(kpats, raws, rules_slice, subs, gone, post=None):
        assert len(raws) == len(rules_slice) + 1
        texts = [post(t) for t in raws] if post else list(raws)
        cterms = [subst(t, subs, gone) for t in texts]
        for t in cterms:
            assert_counters_ground(t, limit=1)
        steps = []
        for j, lbl in enumerate(rules_slice):
            sp = subst(step_proof(lbl, arities, rule_by_label.get(lbl), kpats[j], printer),
                       subs, gone)
            steps.append((lbl, sp))
        return cterms, steps, len(rules_slice)

    # init/final: exactly the statement-stage construction (byte-identity)
    stock_path = ROOT / "build/lean/mpy" / "c12_stock.mpy"
    stock_path.write_text(stock)
    _, (init_raw,) = prints([glt.krun_kore(stock_path, 0)])
    _, (final_raw,) = prints([glt.krun_kore(stock_path, None)])
    assert init_raw.count(INT_LIT.format(KB12_WITNESS)) == 1
    init_body = init_raw.replace(INT_LIT.format(KB12_WITNESS), INT_LIT.format("n"))
    assert final_raw.count(VAL_INT.format(0)) == 1, "final n slot not unique"
    final_body = final_raw.replace(VAL_INT.format(0), VAL_INT.format("v"))
    final_at_n = final_raw.replace(VAL_INT.format(0), VAL_INT.format("n"))

    # ---- prologue + body: ONE stock hints run (depth-bounded: the full
    # countdown from 31337 is ~190k steps), sliced at the first two unfolds
    rules60 = [ord2label[o] for o in rule_sequence_depth("c12_stock", stock_path, depth=60)]
    wu = [k for k, l in enumerate(rules60) if l == "whileUnfold"]
    assert len(wu) >= 2, "fewer than two whileUnfolds within 60 steps"

    # ---- exit witness: n := -7 — guard false at the only whileUnfold; yields
    # loopRest (the ground continuation), the exit leg and the epilogue leg
    exit_path = ROOT / "build/lean/mpy" / "c12_exit.mpy"
    exit_path.write_text(stock.replace(f"Int({KB12_WITNESS})",
                                       f"Int({KB12_EXIT_WITNESS})"))
    exit_rules = [ord2label[o] for o in rule_sequence_depth("c12_exit", exit_path)]
    ewu = [k for k, l in enumerate(exit_rules) if l == "whileUnfold"]
    assert len(ewu) == 1, f"exit witness ran {len(ewu)} unfolds"
    lo = ewu[0]
    sd = next(k for k in range(lo, len(exit_rules)) if exit_rules[k] == "seqDone")
    boundary = sd + 1  # first config with the block residue popped: k = rest
    exit_kp, exit_raw = prints(sweep_range(exit_path, lo, len(exit_rules)))
    s0 = kval_of(exit_raw[boundary - lo])
    assert s0.startswith("SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List"), s0[:100]

    def post_rest(t: str) -> str:
        # the ground continuation is the k cell's TAIL — its RIGHTMOST
        # occurrence: while the guard's If is heated, the frozen `.Stmts`
        # else-branch inside the #freezerIf item prints the very same text
        # (s0 is the nil frame over the empty k cell, unlike C1's non-empty
        # `[Return acc]` continuation)
        k_end = t.index(" }, env := ")
        assert s0 in t[:k_end], "loop continuation not found in k cell"
        assert t.count(s0, k_end) == 0, "continuation text outside the k cell"
        i = t.rindex(s0, 0, k_end)
        return t[:i] + "rest" + t[i + len(s0):]

    ew = KB12_EXIT_WITNESS
    exit_subs = [(INT_LIT.format(f"({ew})"), INT_LIT.format("n")),
                 (VAL_INT.format(f"({ew})"), VAL_INT.format("n"))]
    exit_gone = (str(ew),)  # parenthesized printed form; "-7" is distinctive
    exit_ct, exit_steps, n_exit = build(exit_kp[:boundary - lo + 1],
                                        exit_raw[:boundary - lo + 1],
                                        exit_rules[lo:boundary], exit_subs, exit_gone,
                                        post=post_rest)
    epi_ct, epi_steps, n_epi = build(exit_kp[boundary - lo:], exit_raw[boundary - lo:],
                                     exit_rules[boundary:], exit_subs, exit_gone)
    assert n_epi >= 1, "loopExit at loopRest is already final: drop epilogue_leg"
    loopexit_body = exit_ct[-1]
    assert loopexit_body.count("{ val := rest }") == 1
    assert epi_ct[0] == loopexit_body.replace("{ val := rest }",
                                              "{ val := " + s0 + " }"), \
        "epilogue start does not match loopExit at loopRest"
    assert epi_ct[-1] == final_at_n, "epilogue end does not match final at n"

    # ---- prologue: program start .. first whileUnfold-start, stock witness
    pro_kp, pro_raw = prints(sweep_range(stock_path, 0, wu[0]))
    pro_subs = [(INT_LIT.format(KB12_WITNESS), INT_LIT.format("n")),
                (VAL_INT.format(KB12_WITNESS), VAL_INT.format("n"))]
    pro_ct, pro_steps, n_pro = build(pro_kp, pro_raw, rules60[:wu[0]],
                                     pro_subs, (str(KB12_WITNESS),))
    assert pro_ct[0] == init_body, "prologue depth-0 config does not match init"

    # ---- body: one guard-true iteration (0 < 31337), first whileUnfold-start
    # .. second whileUnfold-start; 31336 is the computed n - 1
    body_kp, body_raw = prints(sweep_range(stock_path, wu[0], wu[1]))
    body_subs = [(VAL_INT.format(KB12_WITNESS - 1), VAL_INT.format("(n - 1)")),
                 (VAL_INT.format(KB12_WITNESS), VAL_INT.format("n"))]
    body_ct, body_steps, n_body = build(body_kp, body_raw, rules60[wu[0]:wu[1]],
                                        body_subs,
                                        (str(KB12_WITNESS), str(KB12_WITNESS - 1)),
                                        post=post_rest)
    loopcfg_body = body_ct[0]
    assert loopcfg_body.count("(rest)") == 1
    assert loopcfg_body.count(VAL_INT.format("n")) == 1

    # ---- endpoint cross-asserts (text-level: the folds rely on the
    # definitional equalities these certify)
    def inst_loopcfg(nv: str, rest: str) -> str:
        t = (loopcfg_body.replace(VAL_INT.format("n"), "@N@")
             .replace("(rest)", "@R@"))
        return t.replace("@N@", VAL_INT.format(nv)).replace("@R@", rest)

    assert exit_ct[0] == loopcfg_body, "exit-witness loop head does not match loopCfg"
    assert pro_ct[-1] == inst_loopcfg("n", "(" + s0 + ")"), \
        "prologue end does not match loopCfg n loopRest"
    assert body_ct[-1] == inst_loopcfg("(n - 1)",
                                       "(SortK.kseq (SortKItem.inj_SortStmts "
                                       + NILSTMTS + ") (rest))"), \
        "body end does not match loopCfg (n - 1) (nil-frame rest)"

    # ---- emit
    pro_defs, pro_fold = emit_path("prologue", "(n : SortInt)", "n", "(n : SortInt)", "n",
                                   "(init n)", "(loopCfg n loopRest)",
                                   pro_ct, pro_steps, n_pro)
    vp = "(n : SortInt) (rest : SortK)"
    va = "n rest"
    body_defs, body_fold = emit_path("body", vp, va, vp + " (h : 0 < n)", va + " h",
                                     "(loopCfg n rest)",
                                     "(loopCfg (n - 1) " + NIL_FRAME + ")",
                                     body_ct, body_steps, n_body)
    exit_defs, exit_fold = emit_path("exit", vp, va, vp + " (h : n ≤ 0)", va + " h",
                                     "(loopCfg n rest)", "(loopExit n rest)",
                                     exit_ct, exit_steps, n_exit)
    epi_defs, epi_fold = emit_path("epilogue", "(n : SortInt)", "n",
                                   "(n : SortInt)", "n",
                                   "(loopExit n loopRest)", "(final n)",
                                   epi_ct, epi_steps, n_epi)
    recs = {t: f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
            for t, n in (("pro", n_pro), ("body", n_body),
                         ("exit", n_exit), ("epi", n_epi))}

    body_txt = f"""import KMiniPy.Relations

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform leg binders; hyps used only on guard steps

/-! C12 execution legs for `kb_countdown` — the PROVED parametric path
fragments the reachability-logic derivation of C12 composes
(`KMiniPy/Verification/C12KbCountdown.lean`). Generated by witness
generalization exactly like the C1 legs, simpler: the program is
module-level MiniPy (no call frame, no function table to swap), one
variable, no accumulator.

Each `whileUnfold` unfolds the loop body as a block whose emptied statement
list stays in the continuation until loop exit (one `inj_SortStmts .List`
residue frame per iteration), so `loopCfg` takes the continuation below the
While statement as an explicit `rest : SortK` parameter; loop exit factors
through `loopExit n rest` (guard false, unfolded-block residue popped, k
cell = rest), `nil_step` (pops one residue frame by `seqDone`) and
`epilogue_leg` (the module tail's final `seqDone` from the ground entry
continuation `loopRest`).

Composition recipe (the k-th loop state has rest = nil-frame^k `loopRest`):
  init n
    ⇒ loopCfg n loopRest                        (prologue_leg)
    ⇒ loopCfg (n - 1) (nil-frame rest)          (body_leg, 0 < n)
    ⇒ loopExit n rest                           (exit_leg, n ≤ 0)
    ⇒ loopExit n loopRest                       (nil_step, k times)
    ⇒ final n                                   (epilogue_leg)

Witnesses: prologue/body at the stock literal {KB12_WITNESS}; exit/epilogue
at {KB12_EXIT_WITNESS} (a negative avoids the program constants 0 and 1; its
printed parenthesized form `({KB12_EXIT_WITNESS})` substitutes unambiguously).
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: {n_pro}-step prologue, {n_body}-step body, {n_exit}-step exit,
1-step nil_step, {n_epi}-step epilogue tran-folds of rule applications.
-/

namespace C12KbCountdownLegs

def init (n : SortInt) : SortGeneratedTopCell :=
  {init_body}

def final (v : SortInt) : SortGeneratedTopCell :=
  {final_body}

/-- The ground continuation below the While statement on loop entry: the
emptied module statement list over the empty k cell. -/
def loopRest : SortK :=
  {s0}

/-- Loop-head configuration at the START of a `whileUnfold` step: the k cell
is topped by the While statement over the continuation `rest`; `n` is the
environment value. -/
def loopCfg (n : SortInt) (rest : SortK) : SortGeneratedTopCell :=
  {loopcfg_body}

/-- Post-loop configuration: guard evaluated false, the exiting iteration's
block residue popped — the k cell IS the continuation `rest`. -/
def loopExit (n : SortInt) (rest : SortK) : SortGeneratedTopCell :=
  {loopexit_body}

{pro_defs}
{recs['pro']}/-- Program start to the first loop-head state. -/
theorem prologue_leg (n : SortInt) :
    Rewrites (init n) (loopCfg n loopRest) :=
  {pro_fold}

{body_defs}
{recs['body']}/-- Exactly one loop iteration: guard true, `n -= 1`; the unfolded block
leaves one residue frame on the continuation. -/
theorem body_leg (n : SortInt) (rest : SortK) (h : 0 < n) :
    Rewrites (loopCfg n rest)
      (loopCfg (n - 1) {NIL_FRAME}) :=
  {body_fold}

{exit_defs}
{recs['exit']}/-- Loop exit: guard false, the exiting unfold's residue popped; the k cell
becomes the continuation `rest`. -/
theorem exit_leg (n : SortInt) (rest : SortK) (h : n ≤ 0) :
    Rewrites (loopCfg n rest) (loopExit n rest) :=
  {exit_fold}

/-- Loop-exit cleanup: one accumulated block-residue frame pops by `seqDone`. -/
theorem nil_step (n : SortInt) (rest : SortK) :
    Rewrites (loopExit n (SortK.kseq (SortKItem.inj_SortStmts {NILSTMTS}) rest))
      (loopExit n rest) :=
  Rewrites.seqDone

{epi_defs}
{recs['epi']}/-- From the popped loop exit at the entry continuation: the module tail's
final `seqDone` — terminal state, `n` unchanged since loop exit. -/
theorem epilogue_leg (n : SortInt) :
    Rewrites (loopExit n loopRest) (final n) :=
  {epi_fold}

end C12KbCountdownLegs
"""
    out = PKG / "KMiniPy" / "Verification" / "C12KbCountdownLegs.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body_txt)
    print(f"[ok] C12KbCountdownLegs: proved, {n_pro} (prologue) + {n_body} (body) "
          f"+ {n_exit} (exit) + 1 (nil_step) + {n_epi} (epilogue) steps")


# ---------------------------------------------------------------------------
# KB: ported KleverBench problems — table-driven ∀-path theorems + RL specs
# ---------------------------------------------------------------------------
# Each ported problem (see programs/PROVENANCE.md) is a MODULE-LEVEL program
# whose inputs are the magic init literals. The K-side claim (corpus/specs/kb-*/)
# pins the entire final scope; here the same claim is one ∀-quantified path
# theorem per feasible path (witness generalization, exactly the B1/B2
# machinery) plus a reachability-logic `spec` theorem in the C2 style:
# straight-line programs derive by a single Rewrites leg, branching programs
# by Case Analysis over their proved paths.
#
# Branch schema (N paths, multi-condition): each path carries `conds` (the
# ordered hypothesis binders, e.g. ["h1 : a ≤ b", "h2 : b ≤ n"]) and
# `results` (one expression per trailing env slot that differs across paths,
# in binding order; substituted RIGHT-TO-LEFT with replace_last). Branch
# theorems classify their conditions by nested `dite`; `split` concludes the
# nested disjunction of kb_tree (2: b1∨b2; 3: b1∨(b2∨b3); 4: (b1∨b2)∨(b3∨b4)),
# and `spec`'s `.caseA` tree mirrors it node for node.

KB_SHA = "b5eced33b16d13b28b9998f05e7b7e945f2fb482"
KB_MAGICS = (31337, 31338, 31339)

KB_PROGRAMS = [
    dict(name="C4KbAssign", stem="kb_assign", problem="assign", params=["a"],
         kind="straight", vals=["(a + 4)"], ground_limit=4,
         claim="b ends as a + 4 and a is unchanged, for every int a"),
    dict(name="C5KbSwap", stem="kb_swap", problem="swap", params=["a", "b"],
         kind="straight", vals=[], ground_limit=0,
         claim="a and b are swapped via temporary r: a ends as b0, "
               "b as a0, r as a0, for arbitrary int inputs"),
    dict(name="C6KbChain", stem="kb_chain", problem="chain", params=["a"],
         kind="straight",
         vals=["(a + 1)", "((a + 1) * 2)", "((a + 1) * 2 - a)"], ground_limit=2,
         claim="x ends as a+1, y as (a+1)*2, z as (a+1)*2 - a; a unchanged"),
    dict(name="C7KbDoubleHalf", stem="kb_double_half", problem="double-half",
         params=["a"], kind="straight", vals=["(a + a)"], ground_limit=2,
         claim="r ends as exactly a: doubling first makes the floor "
               "division exact"),
    dict(name="C8KbArithMix", stem="kb_arith_mix", problem="arith-mix",
         params=["a", "b"], kind="straight",
         vals=["(a * b)", "(a * b + a)", "(a * b + a - b)"], ground_limit=0,
         claim="res ends as a*b + a - b; a and b unchanged"),
    dict(name="C9KbAbs", stem="kb_abs", problem="abs", params=["a"],
         kind="branch", ground_limit=0,
         claim="res ends as |a|; a unchanged",
         post="∃ r : Int, γ = final a (iV r) ∧ 0 ≤ r ∧ (r = a ∨ r = 0 - a)",
         paths=[
             dict(tag="neg", conds=["h : a < 0"], wits={"a": -31337},
                  vals=["(0 - a)"], results=["(0 - a)"],
                  witness_term="⟨0 - a, hγ, by omega, Or.inr rfl⟩"),
             dict(tag="nonneg", conds=["h : 0 ≤ a"], wits={}, vals=[],
                  results=["a"],
                  witness_term="⟨a, hγ, h, Or.inl rfl⟩"),
         ],
         split="fun _γ hγ => if h : a < 0 then Or.inl ⟨hγ, h⟩ "
               "else Or.inr ⟨hγ, by omega⟩"),
    dict(name="C10KbMax", stem="kb_max", problem="max", params=["a", "b"],
         kind="branch", ground_limit=0,
         claim="max ends as the maximum of a and b; a and b unchanged",
         post="∃ m : Int, γ = final a b (iV m) ∧ a ≤ m ∧ b ≤ m ∧ (m = a ∨ m = b)",
         paths=[
             dict(tag="le", conds=["h : a ≤ b"], wits={}, vals=[], results=["b"],
                  witness_term="⟨b, hγ, h, by omega, Or.inr rfl⟩"),
             dict(tag="gt", conds=["h : b < a"], wits={"a": 31338, "b": 31337},
                  vals=[], results=["a"],
                  witness_term="⟨a, hγ, by omega, by omega, Or.inl rfl⟩"),
         ],
         split="fun _γ hγ => if h : a ≤ b then Or.inl ⟨hγ, h⟩ "
               "else Or.inr ⟨hγ, by omega⟩"),
    dict(name="C11KbMin", stem="kb_min", problem="min", params=["a", "b"],
         kind="branch", ground_limit=0,
         claim="res ends as the minimum of a and b; a and b unchanged",
         post="∃ m : Int, γ = final a b (iV m) ∧ m ≤ a ∧ m ≤ b ∧ (m = a ∨ m = b)",
         paths=[
             dict(tag="le", conds=["h : a ≤ b"], wits={}, vals=[], results=["a"],
                  witness_term="⟨a, hγ, by omega, h, Or.inl rfl⟩"),
             dict(tag="gt", conds=["h : b < a"], wits={"a": 31338, "b": 31337},
                  vals=[], results=["b"],
                  witness_term="⟨b, hγ, by omega, by omega, Or.inr rfl⟩"),
         ],
         split="fun _γ hγ => if h : a ≤ b then Or.inl ⟨hγ, h⟩ "
               "else Or.inr ⟨hγ, by omega⟩"),
    dict(name="C17KbMax3", stem="kb_max3", problem="max3", params=["a", "b", "n"],
         kind="branch", ground_limit=0,
         claim="max ends as the maximum of a, b and n; a, b and n unchanged",
         post="∃ m : Int, γ = final a b n (iV m) ∧ a ≤ m ∧ b ≤ m ∧ n ≤ m "
              "∧ (m = a ∨ m = b ∨ m = n)",
         paths=[
             # after `max = a`, the guards run as a≤b / max≤n with max = b or a
             dict(tag="le_le", conds=["h1 : a ≤ b", "h2 : b ≤ n"], wits={},
                  vals=[], results=["n"],
                  witness_term="⟨n, hγ, by omega, h2, by omega, "
                               "Or.inr (Or.inr rfl)⟩"),
             dict(tag="le_gt", conds=["h1 : a ≤ b", "h2 : n < b"],
                  wits={"b": 31339, "n": 31338}, vals=[], results=["b"],
                  witness_term="⟨b, hγ, h1, by omega, by omega, "
                               "Or.inr (Or.inl rfl)⟩"),
             dict(tag="gt_le", conds=["h1 : b < a", "h2 : a ≤ n"],
                  wits={"a": 31338, "b": 31337}, vals=[], results=["n"],
                  witness_term="⟨n, hγ, h2, by omega, by omega, "
                               "Or.inr (Or.inr rfl)⟩"),
             dict(tag="gt_gt", conds=["h1 : b < a", "h2 : n < a"],
                  wits={"a": 31339, "b": 31338, "n": 31337}, vals=[],
                  results=["a"],
                  witness_term="⟨a, hγ, by omega, by omega, by omega, "
                               "Or.inl rfl⟩"),
         ],
         split="fun _γ hγ =>\n"
               "    if h1 : a ≤ b then\n"
               "      if h2 : b ≤ n then Or.inl (Or.inl ⟨hγ, h1, h2⟩)\n"
               "      else Or.inl (Or.inr ⟨hγ, h1, by omega⟩)\n"
               "    else\n"
               "      if h2 : a ≤ n then Or.inr (Or.inl ⟨hγ, by omega, h2⟩)\n"
               "      else Or.inr (Or.inr ⟨hγ, by omega, by omega⟩)"),
    dict(name="C18KbClamp", stem="kb_clamp", problem="clamp", params=["a"],
         kind="branch", ground_limit=10,
         claim="res ends as min(max(a, 0), 10); a unchanged",
         post="∃ r : Int, γ = final a (iV r) ∧ r = min (max a 0) 10",
         paths=[
             # mid witness must sit in [0, 10] but off the program literals
             # 0/10: a single digit (kb_seed checks its printed int form)
             dict(tag="neg", conds=["h : a < 0"], wits={"a": -31337},
                  vals=[], results=["0"],
                  witness_term="⟨0, hγ, by omega⟩"),
             dict(tag="hi", conds=["h1 : 0 ≤ a", "h2 : 10 < a"], wits={},
                  vals=[], results=["10"],
                  witness_term="⟨10, hγ, by omega⟩"),
             dict(tag="mid", conds=["h1 : 0 ≤ a", "h2 : a ≤ 10"],
                  wits={"a": 7}, vals=[], results=["a"],
                  witness_term="⟨a, hγ, by omega⟩"),
         ],
         split="fun _γ hγ =>\n"
               "    if h : a < 0 then Or.inl ⟨hγ, h⟩\n"
               "    else if h2 : 10 < a then Or.inr (Or.inl ⟨hγ, by omega, h2⟩)\n"
               "    else Or.inr (Or.inr ⟨hγ, by omega, by omega⟩)"),
    dict(name="C19KbAbsTimes", stem="kb_abs_times", problem="abs-times",
         params=["a", "b"], kind="branch", ground_limit=0,
         claim="t ends as |a| and res as |a| * b; a and b unchanged",
         post="∃ t r : Int, γ = final a b (iV t) (iV r) ∧ 0 ≤ t "
              "∧ (t = a ∨ t = 0 - a) ∧ r = t * b",
         paths=[
             # two result slots (binding order t, res) — both differ per path
             dict(tag="neg", conds=["h : a < 0"], wits={"a": -31337},
                  vals=["(0 - a)", "((0 - a) * b)"],
                  results=["(0 - a)", "((0 - a) * b)"],
                  witness_term="⟨0 - a, (0 - a) * b, hγ, by omega, "
                               "Or.inr rfl, rfl⟩"),
             dict(tag="nonneg", conds=["h : 0 ≤ a"], wits={},
                  vals=["(a * b)"], results=["a", "(a * b)"],
                  witness_term="⟨a, a * b, hγ, h, Or.inl rfl, rfl⟩"),
         ],
         split="fun _γ hγ => if h : a < 0 then Or.inl ⟨hγ, h⟩ "
               "else Or.inr ⟨hγ, by omega⟩"),
]


def replace_last(text: str, old: str, new: str) -> str:
    """Replace the LAST occurrence (the result variable is bound last at
    module level, hence innermost/rightmost in the printed env)."""
    i = text.rindex(old)
    return text[:i] + new + text[i + len(old):]


NUM_WORDS = {2: "two", 3: "three", 4: "four"}
KB_SLOTS = ("v", "w", "u")  # final-config result-slot binders, binding order


def kb_tree(items: list):
    """Balanced-split tree over the path list — the shape shared by `split`'s
    disjunction and `spec`'s nested `.caseA`: 2 → (1∨2); 3 → 1∨(2∨3);
    4 → (1∨2)∨(3∨4)."""
    if len(items) == 1:
        return items[0]
    mid = len(items) // 2
    return (kb_tree(items[:mid]), kb_tree(items[mid:]))


def kb_disj(node, top: bool = False) -> str:
    """Render a kb_tree of (already parenthesized) disjunct leaves."""
    if isinstance(node, tuple):
        s = f"{kb_disj(node[0])} ∨ {kb_disj(node[1])}"
        return s if top else f"({s})"
    return node


def kb_casea(node, top: bool = False) -> str:
    """Render a kb_tree of branch-theorem applications as nested `.caseA`."""
    if isinstance(node, tuple):
        left, right = kb_casea(node[0]), kb_casea(node[1])
        return f".caseA {left}\n    {right}" if top else f"(.caseA {left} {right})"
    return node


def kb_proj(i: int, n: int) -> str:
    """Projection of condition i (0-based, of n) out of the right-nested
    branch pattern `hp : pat … γ ∧ c1 ∧ … ∧ cn`."""
    return "hp.2" + ".2" * i + (".1" if i < n - 1 else "")


def kb_dite(conds: list, hnames: list, tag: str, var_args: str,
            witness_term: str, i: int = 0) -> str:
    """Branch-theorem body: nested `if hi : ci then … else <vacuous>`; the
    innermost then-arm enters the proved path as an Axiom over `SRew`, every
    else-arm refutes its condition's projection by Reflexivity-on-False."""
    base = "  " * (i + 1)
    if i == len(conds):
        return (f"{base}.conseq (fun _ hp => hp.1)\n"
                f"{base}  (RL.rw_leg (path_{tag} {var_args} {' '.join(hnames)}))\n"
                f"{base}  (fun _γ hγ => {witness_term})")
    return (f"{base}if {conds[i]} then\n"
            + kb_dite(conds, hnames, tag, var_args, witness_term, i + 1) + "\n"
            + f"{base}else\n"
            f"{base}  .conseq (fun _ hp => absurd {kb_proj(i, len(conds))} {hnames[i]})\n"
            f"{base}    (.refl (φ := fun _ => False))\n"
            f"{base}    (fun _ f => f.elim)")


def kb_seed(mpy: str, params: list[str], wits: dict) -> tuple[str, list, tuple]:
    """Witness-seeded mpy text + ordered subs + gone digits for one path."""
    magic = {p: KB_MAGICS[i] for i, p in enumerate(params)}
    witness = {p: wits.get(p, magic[p]) for p in params}
    # two-stage literal replacement (witnesses may permute the magics)
    seeded = mpy
    for i, p in enumerate(params):
        seeded = seeded.replace(str(magic[p]), f"@{i}@")
    for i, p in enumerate(params):
        seeded = seeded.replace(f"@{i}@", str(witness[p]))
    subs, gone = [], set()
    for p in params:
        w = witness[p]
        lit = f"({w})" if w < 0 else str(w)
        subs += [(INT_LIT.format(lit), INT_LIT.format(p)),
                 (VAL_INT.format(lit), VAL_INT.format(p))]
        # a SHORT witness (clamp's mid path: a ∈ 1..9) would false-positive on
        # incidental digits (every digit occurs in the TACTIC's rule uids), so
        # check its printed int form instead of the bare digit string
        d = str(abs(w))
        gone.add(d if len(d) >= 3 else f"» {lit})")
    return seeded, subs, gone, witness


def kb_val_subs(vals: list[str], witness: dict, gone: set) -> list:
    """Computed closed forms -> their witness values, as VAL_INT subs."""
    subs, seen = [], {}
    for expr in vals:
        v = eval(expr, {}, dict(witness))  # int arithmetic only
        digits = f"({v})" if v < 0 else str(v)
        assert digits not in seen, f"value collision {v}: {expr} vs {seen[digits]}"
        # ambiguous only when the PRINTED forms coincide (a negative witness
        # prints parenthesized and is substituted first, so its digits may
        # legitimately reappear as a computed value, cf. B1's 0 - (-31337))
        assert digits not in {f"({w})" if w < 0 else str(w) for w in witness.values()}, \
            f"computed value {v} of {expr} collides with a witness input"
        seen[digits] = expr
        subs.append((VAL_INT.format(digits), VAL_INT.format(expr)))
        gone.add(str(abs(v)))
    return subs


def gen_kb(printer, arities, ord2label, rule_by_label, names=None) -> None:
    for prog in KB_PROGRAMS:
        if names and prog["name"] not in names:
            continue
        name, stem, params = prog["name"], prog["stem"], prog["params"]
        src = (glt.REPO / "programs" / f"{stem}.py").read_text()
        mpy_text = (ROOT / "build/lean/mpy" / f"{stem}.mpy").read_text()
        var_params = "(" + " ".join(params) + " : SortInt)"
        # RL helper binders at Int so omega reads the side conditions (public
        # path/spec signatures stay at SortInt; defeq — the C2AbsVal convention)
        int_params = "(" + " ".join(params) + " : Int)"
        var_args = " ".join(params)
        knum = re.match(r"C(\d+)", name).group(1)
        krec = f"c{knum}_{stem}"

        paths = (prog["paths"] if prog["kind"] == "branch"
                 else [dict(tag="main", conds=[], wits={}, vals=prog["vals"],
                            results=[], witness_term=None)])
        results = {}
        for p in paths:
            seeded, subs, gone, witness = kb_seed(mpy_text, params, p["wits"])
            subs += kb_val_subs(p["vals"], witness, gone)
            subs.sort(key=lambda s: len(s[0]), reverse=True)
            cterms, steps, n = gen_path(f"{stem}_{p['tag']}", seeded, subs,
                                        tuple(sorted(gone, key=len, reverse=True)),
                                        printer, arities, ord2label, rule_by_label)
            for t in cterms:
                assert_counters_ground(t, prog["ground_limit"])
            results[p["tag"]] = (cterms, steps, n)

        init_body = results[paths[0]["tag"]][0][0]
        for p in paths[1:]:
            assert results[p["tag"]][0][0] == init_body, \
                f"{name}: depth-0 configs disagree across paths"

        if prog["kind"] == "straight":
            final_body = results["main"][0][-1]
            final_params = var_params
        else:
            slots = list(KB_SLOTS[:len(paths[0]["results"])])
            for p in paths:
                assert len(p["results"]) == len(slots), f"{name}: ragged results"

            def sub_slots(cterm: str, res_list: list) -> str:
                # trailing env slots are innermost/rightmost: substitute
                # RIGHT-TO-LEFT; a literal result (clamp's 0/10) must be the
                # unique such value in the final config
                for slot, res in zip(reversed(slots), reversed(res_list)):
                    if re.fullmatch(r"-?\d+", res):
                        assert cterm.count(VAL_INT.format(res)) == 1, \
                            f"{name}: literal result slot {res} not unique"
                    cterm = replace_last(cterm, VAL_INT.format(res), slot)
                return cterm

            final_body = sub_slots(results[paths[0]["tag"]][0][-1],
                                   paths[0]["results"])
            for p in paths[1:]:
                assert sub_slots(results[p["tag"]][0][-1], p["results"]) == final_body, \
                    f"{name}: final configs disagree beyond the result slots ({p['tag']})"
            final_params = f"{var_params} ({' '.join(slots)} : SortVal)"

        sections, nsteps = [], {}
        for p in paths:
            cterms, steps, n = results[p["tag"]]
            nsteps[p["tag"]] = n
            hnames = [c.split(" : ", 1)[0] for c in p["conds"]]
            binders = var_params + "".join(f" ({c})" for c in p["conds"])
            fold_args = var_args + "".join(f" {h}" for h in hnames)
            fref = (f"(final {var_args})" if prog["kind"] == "straight"
                    else f"(final {var_args} "
                         + " ".join(f"(iV {r})" for r in p["results"]) + ")")
            defs, fold = emit_path(p["tag"], var_params, var_args, binders,
                                   fold_args, f"(init {var_args})", fref,
                                   cterms, steps, n)
            rec = f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
            doc = ("The single (unconditional) path." if not p["conds"] else
                   "Path under " + ", ".join(f"`{c}`" for c in p["conds"]) + ".")
            sections.append(f"""{defs}
{rec}/-- {doc} -/
theorem path_{p['tag']} {binders} :
    Rewrites (init {var_args}) {fref} :=
  {fold}
""")

        if prog["kind"] == "straight":
            rl = f"""/-- {name} K-claim mirror ({krec}): {prog['claim']}.
A straight-line program: the reachability derivation is a single
machine-checked `Rewrites` leg entering as an Axiom over `SRew`. -/
theorem spec {var_params} :
    RLOne (pat (init {var_args})) (pat (final {var_args})) :=
  RL.rw_leg (path_main {var_args})
"""
        else:
            conjs = {p["tag"]: " ∧ ".join(c.split(" : ", 1)[1] for c in p["conds"])
                     for p in paths}
            branch_thms = []
            for p in paths:
                hnames = [c.split(" : ", 1)[0] for c in p["conds"]]
                branch_thms.append(f"""/-- Branch under `{conjs[p['tag']]}`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_{p['tag']} {int_params} :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init {var_args}) γ ∧ {conjs[p['tag']]}, post {var_args}) :=
{kb_dite(p['conds'], hnames, p['tag'], var_args, p['witness_term'])}
""")
            nword = NUM_WORDS[len(paths)]
            disj = kb_disj(kb_tree([f"(pat (init {var_args}) γ ∧ {conjs[p['tag']]})"
                                    for p in paths]), top=True)
            casea = kb_casea(kb_tree([f"(branch_{p['tag']} {var_args})"
                                      for p in paths]), top=True)
            rl = f"""/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post {int_params} : Pat := fun γ =>
  {prog['post']}

{chr(10).join(branch_thms)}
/-- Every pre-state satisfies one of the {nword} branch patterns. -/
theorem split {int_params} : ∀ γ, pat (init {var_args}) γ →
    {disj} :=
  {prog['split']}

/-- {name} K-claim mirror ({krec}): {prog['claim']}.
Case Analysis over the {nword} machine-checked paths, C2 style. -/
theorem spec {var_params} :
    RLOne (pat (init {var_args})) (post {var_args}) :=
  .conseq (split {var_args}) ({casea}) (fun _ h => h)
"""

        steps_doc = " / ".join(f"{nsteps[p['tag']]} ({p['tag']})" for p in paths)
        body = f"""import KMiniPy.Relations
import KMiniPy.RL

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform path binders; hyps used only on branch steps

/-! # {name}: ported KleverBench problem `{prog['problem']}` — {prog['claim']}

K-side record: corpus/k/verification/{krec} (claim proved by kprove over the
MPY semantics); upstream problem problems/imp/{prog['problem']} at
KleverBench {KB_SHA[:7]} (see programs/PROVENANCE.md). The program is
module-level MiniPy; its inputs are the init literals, generalized here to
∀-quantified `SortInt` binders by witness generalization (B1/B2 machinery).
The reachability-logic `spec` theorem mirrors the K claim's full final-scope
characterization.
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: tran-folds of {steps_doc} steps; `spec` in the RL calculus of KMiniPy.RL.
-/

open RLogic

namespace {name}

def init {var_params} : SortGeneratedTopCell :=
  {init_body}

def final {final_params} : SortGeneratedTopCell :=
  {final_body}

{chr(10).join(sections)}
{rl}
end {name}
"""
        out = PKG / "KMiniPy" / "Verification" / f"{name}.lean"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(body)
        print(f"[ok] {name}: proved, steps {steps_doc}")


def main() -> int:
    only = ([a for a in sys.argv[sys.argv.index("--only") + 1:] if not a.startswith("-")]
            if "--only" in sys.argv else None)
    check_simp_names()
    printer = glt.load_printer()
    arities = glt.ctor_arities(PKG / "KMiniPy" / "Rewrite.lean")
    ord2label = glt.ordinal_to_label(glt.HINTS_DEFN)
    rule_by_label = {glt._rule_name(r): r for r in printer.defn.rewrites}

    if only is None or "b1" in only:
        gen_b1(printer, arities, ord2label, rule_by_label)
    if only is None or "b2" in only:
        gen_b2(printer, arities, ord2label, rule_by_label)
    if only is None or "c1" in only:
        gen_c1(printer, arities, ord2label, rule_by_label)
    if only is None or "kb12" in only:
        gen_kb_countdown(printer, arities, ord2label, rule_by_label)
    kb_sel = [t.split(":", 1)[1] for t in (only or []) if t.startswith("kb:")]
    if only is None or "kb" in only or kb_sel:
        gen_kb(printer, arities, ord2label, rule_by_label, names=kb_sel or None)
    return 0


if __name__ == "__main__":
    sys.exit(main())
