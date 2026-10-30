#!/usr/bin/env python3
"""kclaims — parse, freeze-compare and evaluate K reachability claims written
against the klever MPY semantics.

One file, two consumers:

* the task generator (scripts/harbor/build_tasks.py) uses it to extract the
  entry claim of every reference spec.k, build the frozen skeletons handed to
  the agent, and self-check that every reference claim passes the verifier's
  semantic checks;
* every K task's verifier (tests/kclaims.py, a verbatim copy) uses it to
  decide whether the agent's spec.k is admissible BEFORE kprove runs:
  whitelist grammar, frozen regions intact, and — for the proved-spec family —
  that the pinned final state is a full characterization: every program
  variable bound, every existential determined by exactly one `?X ==Int TERM`
  conjunct (so no disjunction of candidates, no region-restricted postcondition
  can pass), and the pinned values equal to CPython's on random inputs.

The module is dependency-free (stdlib only) and must stay that way: inside the
sandbox it runs under `python3 -I`.
"""
from __future__ import annotations

import random
import re
from dataclasses import dataclass, field

# ---------------------------------------------------------------------------
# Whitelist grammar for an agent-written spec.k
# ---------------------------------------------------------------------------

ALLOWED_REQUIRES = 'requires "verification.k"'
ALLOWED_ATTRS = {"all-path"}

# Any of these words outside string literals makes the file inadmissible: they
# are the K constructs that could add rules, lemmas, trusted claims or
# attributes that change what kprove accepts.
FORBIDDEN_WORDS = (
    "rule", "syntax", "configuration", "context", "trusted", "simplification",
    "owise", "priority", "concrete", "symbolic", "anywhere", "macro",
    "smt-lemma", "smt-hook", "unboundVariables", "function", "total", "hook",
    "alias", "cool", "heat", "strict", "seqstrict", "label", "one-path",
    "preserves-definedness", "depends", "comm", "assoc", "unit", "idem",
)


class SpecError(Exception):
    """A structural or semantic problem with a spec.k file."""


def strip_comments(text: str) -> str:
    """Remove // line comments and /* block */ comments, leaving string
    literals untouched."""
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            if j < 0:
                raise SpecError("unterminated block comment")
            i = j + 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def strip_strings(text: str) -> str:
    """Replace every string literal by "" (for keyword scans)."""
    return re.sub(r'"(?:[^"\\]|\\.)*"', '""', text)


def normalize(text: str) -> str:
    """Whitespace-insensitive form used for frozen-region comparison."""
    return re.sub(r"\s+", "", text)


@dataclass
class Module:
    name: str
    imports: list[str]
    claims: list[str]           # raw claim texts (comments stripped), in order


def parse_module(text: str, *, verification_module: str) -> Module:
    """Parse an admissible spec.k: one requires line, one module importing
    exactly the verification module, and nothing but claims inside."""
    body = strip_comments(text)
    if any(ord(c) > 127 for c in body):
        raise SpecError("spec.k must be ASCII outside comments")
    scan = strip_strings(body)
    for word in FORBIDDEN_WORDS:
        if re.search(rf"(?<![\w-]){re.escape(word)}(?![\w-])", scan):
            raise SpecError(f"forbidden token {word!r} in spec.k")
    m = re.match(r"\s*(requires\s+\"[^\"]*\")?\s*module\s+([A-Z][A-Z0-9-]*)\s*(.*?)\s*endmodule\s*$",
                 body, re.S)
    if not m:
        raise SpecError("spec.k must be: optional `requires \"verification.k\"`, one module, endmodule")
    req, name, inner = m.group(1), m.group(2), m.group(3)
    if req is not None and normalize(req) != normalize(ALLOWED_REQUIRES):
        raise SpecError(f"only {ALLOWED_REQUIRES} is allowed as a requires line")
    if re.search(r"(?<![\w-])(module|endmodule)(?![\w-])", strip_strings(inner)):
        raise SpecError("exactly one module is allowed")
    imports: list[str] = []
    rest = inner
    while True:
        im = re.match(r"\s*imports\s+([A-Z][A-Z0-9-]*)", rest)
        if not im:
            break
        imports.append(im.group(1))
        rest = rest[im.end():]
    if imports != [verification_module]:
        raise SpecError(f"the module must import exactly {verification_module}")
    rest = rest.strip()
    if not rest.startswith("claim"):
        raise SpecError("the module body must consist of claims only")
    parts = re.split(r"(?m)^\s*claim(?![\w-])", "\n" + rest)
    if parts[0].strip():
        raise SpecError("unexpected text before the first claim")
    claims = [p.strip() for p in parts[1:]]
    if not claims:
        raise SpecError("no claims")
    for c in claims:
        if re.search(r"(?<![\w-])(imports|requires\s+\")", strip_strings(c)):
            raise SpecError("imports/requires inside a claim")
    return Module(name=name, imports=imports, claims=claims)


# ---------------------------------------------------------------------------
# Claim structure
# ---------------------------------------------------------------------------

CELL_RE = re.compile(r"<([a-zA-Z][\w-]*)(?:\s+[^>]*)?>(.*?)</\1>", re.S)
ATTR_GROUP_RE = re.compile(r"\[([^\[\]]*)\]\s*$")


@dataclass
class Claim:
    text: str
    cells: dict[str, str]        # cell name -> inner text (raw)
    requires: str | None
    ensures: str | None
    attrs: list[str]

    @property
    def has_scope_loc(self) -> bool:
        return "scopeLoc" in self.cells


def parse_claim(text: str) -> Claim:
    cells: dict[str, str] = {}
    last_end = 0
    for m in CELL_RE.finditer(text):
        if m.group(1) in cells:
            raise SpecError(f"cell <{m.group(1)}> appears twice in one claim")
        cells[m.group(1)] = m.group(2)
        last_end = m.end()
    if "k" not in cells:
        raise SpecError("claim without a <k> cell")
    tail = text[last_end:]
    # at most one trailing attribute group `[key, key, ...]`, every key allowed, no arguments
    attrs: list[str] = []
    am = ATTR_GROUP_RE.search(tail)
    if am:
        for item in am.group(1).split(","):
            key = item.strip()
            if not re.fullmatch(r"[A-Za-z][\w-]*", key):
                raise SpecError(f"claim attribute {key!r} is not allowed")
            if key not in ALLOWED_ATTRS:
                raise SpecError(f"claim attribute [{key}] is not allowed")
            attrs.append(key)
        tail = tail[:am.start()]
    if "[" in strip_strings(tail) or "]" in strip_strings(tail):
        raise SpecError("unexpected bracket after the cells (only one trailing [all-path] group is allowed)")
    requires = ensures = None
    rm = re.search(r"(?<![\w-])requires(?![\w-])", tail)
    em = re.search(r"(?<![\w-])ensures(?![\w-])", tail)
    if rm and em and em.start() < rm.start():
        raise SpecError("ensures before requires")
    if rm:
        requires = tail[rm.end(): em.start() if em else None].strip()
    if em:
        ensures = tail[em.end():].strip()
    head = tail[: (rm or em).start()] if (rm or em) else tail
    if head.strip():
        raise SpecError(f"unexpected text after the cells: {head.strip()[:60]!r}")
    return Claim(text=text, cells=cells, requires=requires, ensures=ensures, attrs=attrs)


def split_scopes(scopes: str) -> tuple[str, str]:
    """Split an entry claim's <scopes> cell at its top-level `=>`."""
    depth = 0
    i = 0
    while i < len(scopes) - 1:
        c = scopes[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c == "=" and scopes[i + 1] == ">" and depth == 0:
            return scopes[:i], scopes[i + 2:]
        i += 1
    raise SpecError("<scopes> cell of the entry claim has no top-level `=>`")


SCOPE_RHS_RE = re.compile(
    r"^\s*-1\s*\|->\s*builtinsScope\s*0\s*\|->\s*scope\(\s*(.*?)\s*,\s*parent\(\s*-1\s*\)\s*\)\s*$", re.S)
ENTRY_RE = re.compile(r'\[\s*"([A-Za-z_]\w*)"\s*<-\s*([^\]]+?)\s*\]')


def parse_scope_map(rhs: str) -> list[tuple[str, str]]:
    """`-1 |-> builtinsScope 0 |-> scope(.Map [ "x" <- T ] ..., parent(-1))`
    -> [("x", "T"), ...]."""
    m = SCOPE_RHS_RE.match(rhs)
    if not m:
        raise SpecError("the final <scopes> must be `-1 |-> builtinsScope  0 |-> scope(.Map [ ... ], parent(-1))`")
    mp = m.group(1)
    if not mp.startswith(".Map"):
        raise SpecError("the final scope map must start with .Map")
    body = mp[len(".Map"):]
    entries = ENTRY_RE.findall(body)
    if normalize("".join(f'["{k}"<-{v}]' for k, v in entries)) != normalize(body):
        raise SpecError("the final scope map must be a sequence of [ \"name\" <- term ] updates")
    names = [k for k, _ in entries]
    if len(set(names)) != len(names):
        raise SpecError("a variable is bound twice in the final scope")
    return entries


# ---------------------------------------------------------------------------
# K Int / Bool expression evaluator (the admissible subset)
# ---------------------------------------------------------------------------

TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<op>\+Int|-Int|\*Int|/Int|%Int|divInt|modInt|\^Int|<=Int|>=Int|<Int|>Int|==Int|=/=Int
          |andBool|orBool|notBool)
  | (?P<kw>\#if|\#then|\#else|\#fi)
  | (?P<int>-?\d+)
  | (?P<ident>\??[A-Za-z_][A-Za-z0-9_]*)
  | (?P<punct>[(),])
""", re.X)

# operator -> precedence tier (higher binds tighter), mirroring K's domains.md:
# ^Int > (*Int /Int %Int divInt modInt) > (+Int -Int) > comparisons (non-assoc)
# > (andBool orBool: ONE tier in K, so mixing them without parentheses is
# ambiguous and refused here).
BINOPS = {
    "^Int": 60, "*Int": 50, "/Int": 50, "%Int": 50, "divInt": 50, "modInt": 50,
    "+Int": 40, "-Int": 40,
    "<Int": 30, "<=Int": 30, ">Int": 30, ">=Int": 30, "==Int": 30, "=/=Int": 30,
    "andBool": 20, "orBool": 20,
}
NON_ASSOC_TIER = 30
FUNCS = {"minInt": 2, "maxInt": 2, "absInt": 1}


class EvalError(Exception):
    pass


def tokenize(expr: str) -> list[tuple[str, str]]:
    toks: list[tuple[str, str]] = []
    pos = 0
    while pos < len(expr):
        m = TOKEN_RE.match(expr, pos)
        if not m:
            raise EvalError(f"cannot tokenize at {expr[pos:pos + 20]!r}")
        pos = m.end()
        kind = m.lastgroup
        if kind == "ws":
            continue
        val = m.group(kind)
        if kind == "ident":
            sm = re.match(r"\s*:\s*[A-Za-z][A-Za-z0-9]*", expr[pos:])
            if sm:
                pos += sm.end()
        toks.append((kind, val))
    return toks


class Parser:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else (None, None)

    def take(self, kind=None, val=None):
        k, v = self.peek()
        if k is None or (kind and k != kind) or (val and v != val):
            raise EvalError(f"expected {val or kind}, got {v!r}")
        self.i += 1
        return v

    def parse(self):
        e = self.expr(0)
        if self.peek()[0] is not None:
            raise EvalError(f"trailing tokens at {self.peek()[1]!r}")
        return e

    def expr(self, min_prec):
        left = self.unary()
        chain_op = None
        while True:
            k, v = self.peek()
            if k != "op" or v not in BINOPS or BINOPS[v] < min_prec:
                return left
            prec = BINOPS[v]
            if chain_op is not None and BINOPS[chain_op] == prec:
                if prec == NON_ASSOC_TIER:
                    raise EvalError(f"chained comparison {chain_op} ... {v} needs parentheses")
                if chain_op != v and prec == BINOPS["andBool"]:
                    raise EvalError(f"mixing {chain_op} and {v} needs parentheses (K parses them in one tier)")
            self.i += 1
            right = self.expr(prec + 1)  # left-assoc
            left = ("bin", v, left, right)
            chain_op = v

    def unary(self):
        k, v = self.peek()
        if k == "op" and v == "notBool":
            self.i += 1
            return ("not", self.unary())
        return self.atom()

    def atom(self):
        k, v = self.peek()
        if k == "int":
            self.i += 1
            return ("int", int(v))
        if k == "punct" and v == "(":
            self.i += 1
            e = self.expr(0)
            self.take("punct", ")")
            return e
        if k == "kw" and v == "#if":
            self.i += 1
            c = self.expr(0)
            self.take("kw", "#then")
            t = self.expr(0)
            self.take("kw", "#else")
            f = self.expr(0)
            self.take("kw", "#fi")
            return ("ite", c, t, f)
        if k == "ident":
            self.i += 1
            if v in ("true", "false"):
                return ("bool", v == "true")
            if v in FUNCS:
                self.take("punct", "(")
                args = [self.expr(0)]
                while self.peek() == ("punct", ","):
                    self.i += 1
                    args.append(self.expr(0))
                self.take("punct", ")")
                if len(args) != FUNCS[v]:
                    raise EvalError(f"{v} takes {FUNCS[v]} arguments")
                return ("call", v, args)
            return ("var", v)
        raise EvalError(f"unexpected token {v!r}")


def parse_expr(expr: str):
    return Parser(tokenize(expr)).parse()


def _tdiv(a: int, b: int) -> int:
    if b == 0:
        raise EvalError("division by zero")
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def _ediv(a: int, b: int) -> int:
    if b == 0:
        raise EvalError("division by zero")
    return a // b if b > 0 else -(a // -b)


def eval_expr(ast, env: dict):
    kind = ast[0]
    if kind == "int" or kind == "bool":
        return ast[1]
    if kind == "var":
        if ast[1] not in env:
            raise EvalError(f"unbound variable {ast[1]}")
        return env[ast[1]]
    if kind == "not":
        v = eval_expr(ast[1], env)
        _need(v, bool, "notBool")
        return not v
    if kind == "ite":
        c = eval_expr(ast[1], env)
        _need(c, bool, "#if")
        return eval_expr(ast[2] if c else ast[3], env)
    if kind == "call":
        args = [eval_expr(a, env) for a in ast[2]]
        for a in args:
            _need(a, int, ast[1])
        if ast[1] == "minInt":
            return min(args)
        if ast[1] == "maxInt":
            return max(args)
        return abs(args[0])
    op, l, r = ast[1], eval_expr(ast[2], env), eval_expr(ast[3], env)
    if op in ("andBool", "orBool"):
        _need(l, bool, op)
        _need(r, bool, op)
        return (l and r) if op == "andBool" else (l or r)
    _need(l, int, op)
    _need(r, int, op)
    if op == "+Int":
        return l + r
    if op == "-Int":
        return l - r
    if op == "*Int":
        return l * r
    if op == "/Int":
        return _tdiv(l, r)
    if op == "%Int":
        return l - r * _tdiv(l, r)
    if op == "divInt":
        return _ediv(l, r)
    if op == "modInt":
        return l - r * _ediv(l, r)
    if op == "^Int":
        if r < 0:
            raise EvalError("negative exponent")
        if r > 64:
            raise EvalError("exponent too large")
        return l ** r
    return {"<Int": l < r, "<=Int": l <= r, ">Int": l > r, ">=Int": l >= r,
            "==Int": l == r, "=/=Int": l != r}[op]


def _need(v, ty, what):
    if ty is int and (isinstance(v, bool) or not isinstance(v, int)):
        raise EvalError(f"{what}: expected Int")
    if ty is bool and not isinstance(v, bool):
        raise EvalError(f"{what}: expected Bool")


def free_vars(ast) -> set[str]:
    kind = ast[0]
    if kind == "var":
        return {ast[1]}
    if kind in ("int", "bool"):
        return set()
    out: set[str] = set()
    for sub in ast[1:]:
        if isinstance(sub, tuple):
            out |= free_vars(sub)
        elif isinstance(sub, list):
            for s in sub:
                out |= free_vars(s)
    return out


def existentials(ast) -> set[str]:
    return {v for v in free_vars(ast) if v.startswith("?")}


def conjuncts(ast) -> list:
    if ast[0] == "bin" and ast[1] == "andBool":
        return conjuncts(ast[2]) + conjuncts(ast[3])
    return [ast]


def pinned_var(side):
    """`?X`, `c *Int ?X` or `?X *Int c` (literal c != 0) -> "?X", else None."""
    if side[0] == "var" and side[1].startswith("?"):
        return side[1]
    if side[0] == "bin" and side[1] == "*Int":
        l, r = side[2], side[3]
        if l[0] == "int" and l[1] != 0 and r[0] == "var" and r[1].startswith("?"):
            return r[1]
        if r[0] == "int" and r[1] != 0 and l[0] == "var" and l[1].startswith("?"):
            return l[1]
    return None


def determination_problems(ensures_ast, needed: set[str]) -> list[str]:
    """The structural uniqueness rule of the proved-spec family.

    `ensures` must be a conjunction (over andBool) in which every existential
    `?X` that the final scope uses occurs in EXACTLY one conjunct, of the shape
    `?X ==Int TERM`, `TERM ==Int ?X`, `c *Int ?X ==Int TERM` or symmetric, with
    a non-zero literal `c` and TERM free of existentials. No existential may
    occur anywhere else (in particular not under orBool, notBool, #if, or in a
    conjunct with another existential). Then on every input the ensures has at
    most one solution, by construction, whatever region of the inputs a
    conjunct about the inputs selects."""
    problems: list[str] = []
    pinned: dict[str, int] = {}
    for c in conjuncts(ensures_ast):
        ex = existentials(c)
        if not ex:
            continue  # a pure constraint on the inputs is fine
        if c[0] == "bin" and c[1] == "==Int":
            for lhs, rhs in ((c[2], c[3]), (c[3], c[2])):
                v = pinned_var(lhs)
                if v and not existentials(rhs) and ex == {v}:
                    pinned[v] = pinned.get(v, 0) + 1
                    break
            else:
                problems.append(f"conjunct with existentials {sorted(ex)} is not of the form `?X ==Int TERM`")
        else:
            problems.append(f"existentials {sorted(ex)} occur outside a `?X ==Int TERM` conjunct")
    for v in sorted(needed):
        if pinned.get(v, 0) != 1:
            problems.append(f"existential {v} must be pinned by exactly one `{v} ==Int TERM` conjunct (found {pinned.get(v, 0)})")
    return problems


# ---------------------------------------------------------------------------
# Entry-claim metadata (shared by generator and verifier)
# ---------------------------------------------------------------------------

MODULE_INPUT_RE = re.compile(r'Assign\(Name\("([A-Za-z_]\w*)"\)\s*,\s*([A-Za-z_]\w*)\s*:\s*Int\s*\)')
CALL_INPUT_RE = re.compile(r'Call\(Name\("[A-Za-z_]\w*"\)\s*,\s*([^()]*?)\)')


@dataclass
class Inputs:
    module: list[tuple[str, str]] = field(default_factory=list)   # (python name, K var)
    call: list[tuple[str, str]] = field(default_factory=list)     # (python name, K var)

    @property
    def kvars(self) -> list[str]:
        return [k for _, k in self.module + self.call]

    def to_json(self) -> dict:
        return {"module": self.module, "call": self.call}

    @classmethod
    def from_json(cls, d: dict) -> "Inputs":
        return cls(module=[tuple(x) for x in d["module"]], call=[tuple(x) for x in d["call"]])


def discover_inputs(k_lhs: str, arg_names: list[str]) -> Inputs:
    """Inputs of the program as they appear in the entry claim's <k> LHS:
    module-level `Assign(Name("n"), N:Int)` and function-call `Call(Name("f"),
    X:Int)` arguments (python names for the latter come from the record)."""
    inp = Inputs()
    for py, kv in MODULE_INPUT_RE.findall(k_lhs):
        inp.module.append((py, kv))
    cm = CALL_INPUT_RE.search(k_lhs)
    if cm:
        kvs = [re.sub(r"\s*:\s*Int$", "", a.strip()) for a in cm.group(1).split(",") if a.strip()]
        kvs = [k for k in kvs if re.fullmatch(r"[A-Za-z_]\w*", k)]
        if len(kvs) != len(arg_names):
            raise SpecError(f"call inputs {kvs} do not match record args {arg_names}")
        inp.call = list(zip(arg_names, kvs))
    return inp


# ---------------------------------------------------------------------------
# Verifier-side checks
# ---------------------------------------------------------------------------

def entry_claim(mod: Module, k_cell: str | None = None) -> tuple[Claim, list[Claim]]:
    """The entry claim is the unique claim whose <k> cell is the frozen program
    (normalized text `k_cell`); without a reference, the unique claim carrying a
    <scopeLoc> cell (the generator's view of the corpus)."""
    parsed = [parse_claim(c) for c in mod.claims]
    if k_cell is not None:
        entries = [c for c in parsed if normalize(c.cells["k"]) == k_cell]
        what = "whose <k> cell is the frozen program"
    else:
        entries = [c for c in parsed if c.has_scope_loc]
        what = "with <scopeLoc>"
    if len(entries) != 1:
        raise SpecError(f"expected exactly one entry claim ({what}), found {len(entries)}")
    others = [c for c in parsed if c is not entries[0]]
    return entries[0], others


def frozen_entry_parts(c: Claim) -> dict[str, str]:
    """The regions of an entry claim the proved-spec family freezes: every cell
    except the final scope map, plus the precondition."""
    lhs, _rhs = split_scopes(c.cells["scopes"])
    parts = {f"cell:{k}": normalize(v) for k, v in c.cells.items() if k != "scopes"}
    parts["scopes_lhs"] = normalize(lhs)
    parts["requires"] = normalize(c.requires or "")
    parts["attrs"] = ",".join(c.attrs)
    return parts


def check_frozen(agent: Claim, ref_parts: dict[str, str]) -> list[str]:
    problems = []
    got = frozen_entry_parts(agent)
    for key, val in ref_parts.items():
        if got.get(key) != val:
            problems.append(f"frozen region changed: {key}")
    for key in got:
        if key not in ref_parts:
            problems.append(f"unexpected extra cell: {key}")
    return problems


def run_program(code: str, inputs: dict[str, int]) -> dict:
    g: dict = dict(inputs)
    g["__name__"] = "__harbor__"
    exec(compile(code, "<program>", "exec"), g)  # noqa: S102 — trusted corpus program
    return g


def sample_inputs(kvars: list[str], requires: str | None, *, n: int, seed: int) -> list[dict[str, int]]:
    """Deterministic inputs satisfying the frozen precondition: `n` draws in
    [-25, 25], n/3 draws in [-400, 400] (loops still run instantly in CPython),
    and the boundary points suggested by the literals of the precondition."""
    rng = random.Random(seed)
    req = parse_expr(requires) if requires else None
    out: list[dict[str, int]] = []
    seen: set[tuple] = set()

    def admit(cand: dict[str, int]) -> bool:
        key = tuple(cand[k] for k in kvars)
        if key in seen:
            return False
        if req is not None and eval_expr(req, dict(cand)) is not True:
            return False
        seen.add(key)
        out.append(cand)
        return True

    for lo, hi, want in ((-25, 25, n), (-400, 400, max(1, n // 3))):
        got, tries = 0, 0
        while got < want and tries < 5000:
            tries += 1
            got += admit({k: rng.randint(lo, hi) for k in kvars})
        if got < want:
            raise SpecError("could not sample enough inputs satisfying the precondition")
    lits = {0, 1, -1}
    for lit in re.findall(r"-?\d+", requires or ""):
        v = int(lit)
        lits |= {v - 1, v, v + 1}
    points = sorted(lits)
    boundary = 0
    for combo in _combos(points, len(kvars)):
        if boundary >= 12:
            break
        boundary += admit(dict(zip(kvars, combo)))
    return out


def _combos(points, k):
    if k == 0:
        yield ()
        return
    for p in points:
        for rest in _combos(points, k - 1):
            yield (p,) + rest


def check_closed_forms(entry: Claim, *, code: str, inputs: Inputs, requires: str | None,
                       fn_names: list[str], n_samples: int = 24, seed: int = 20261030) -> list[str]:
    """The proved-spec semantic check: the final scope pins every program
    variable to a term whose value agrees with CPython on random inputs
    satisfying the precondition, and `ensures` determines every existential
    uniquely by construction (see determination_problems)."""
    problems: list[str] = []
    try:
        _lhs, rhs = split_scopes(entry.cells["scopes"])
        entries = parse_scope_map(rhs)
    except SpecError as e:
        return [str(e)]
    bound = dict(entries)
    terms: dict[str, object] = {}
    for name, term in entries:
        if name in fn_names:
            continue
        try:
            terms[name] = parse_expr(term)
        except EvalError as e:
            problems.append(f"cannot parse the term bound to {name!r}: {e}")
    ensures_ast = None
    if entry.ensures:
        try:
            ensures_ast = parse_expr(entry.ensures)
        except EvalError as e:
            problems.append(f"cannot parse ensures: {e}")
    if problems:
        return problems
    for fn in fn_names:
        if fn not in bound:
            problems.append(f"the function binding {fn!r} is missing from the final scope")
    # existentials: every one used must be bound bare to a program variable, and
    # the scope terms themselves may not combine existentials with anything
    bare: dict[str, str] = {}
    for name, ast in terms.items():
        ex = existentials(ast)
        if ast[0] == "var" and ast[1].startswith("?"):
            bare.setdefault(ast[1], name)
        elif ex:
            problems.append(f"the term bound to {name!r} mixes existentials {sorted(ex)} with other symbols; bind a bare ?X and pin it in ensures")
    used: set[str] = set()
    for ast in terms.values():
        used |= existentials(ast)
    if ensures_ast is not None:
        used |= existentials(ensures_ast)
    for v in sorted(used):
        if v not in bare:
            problems.append(f"existential {v} is not bound directly to a program variable in the final scope")
    kv = set(inputs.kvars)
    for ast in list(terms.values()) + ([ensures_ast] if ensures_ast is not None else []):
        for v in free_vars(ast):
            if not v.startswith("?") and v not in kv:
                problems.append(f"unknown variable {v} (inputs are {sorted(kv)})")
    if problems:
        return problems
    if bare:
        if ensures_ast is None:
            return [f"existentials {sorted(bare)} are bound but there is no ensures to pin them"]
        problems = determination_problems(ensures_ast, set(bare))
        if problems:
            return problems
    call_names = {py for py, _ in inputs.call}
    samples = sample_inputs(inputs.kvars, requires, n=n_samples, seed=seed)
    for sample in samples:
        py_inputs = {py: sample[k] for py, k in inputs.module + inputs.call}
        g = run_program(code, py_inputs)
        finals = {k: v for k, v in g.items()
                  if isinstance(v, int) and not isinstance(v, bool)
                  and not k.startswith("__") and k not in call_names}
        for name in finals:
            if name not in bound:
                problems.append(f"program variable {name!r} is not bound in the final scope")
        for name in terms:
            if name not in finals:
                problems.append(f"the final scope binds {name!r}, which the program never assigns")
        if problems:
            return problems
        env: dict = dict(sample)
        for ex, name in bare.items():
            env[ex] = finals[name]
        try:
            for name, ast in terms.items():
                got = eval_expr(ast, env)
                if got != finals[name]:
                    problems.append(f"at inputs {sample}: {name} is pinned to {got}, CPython gives {finals[name]}")
            if ensures_ast is not None and eval_expr(ensures_ast, env) is not True:
                problems.append(f"at inputs {sample}: ensures is false on the actual final state")
            if problems:
                return problems
            for ex in bare:  # belt and braces: the structural rule already forces this
                for delta in (1, -1, 7):
                    env2 = dict(env)
                    env2[ex] += delta
                    if eval_expr(ensures_ast, env2) is not False:
                        return [f"{ex} is not pinned: ensures also holds at {ex} {delta:+d}"]
        except EvalError as e:
            return [f"evaluation error at inputs {sample}: {e}"]
    return problems
