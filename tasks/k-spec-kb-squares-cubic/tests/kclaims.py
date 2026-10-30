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
  that the pinned final state is a full characterization that agrees with
  CPython on random inputs.

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


@dataclass
class Claim:
    text: str
    cells: dict[str, str]        # cell name -> inner text (raw)
    requires: str | None
    ensures: str | None
    attrs: list[str]

    @property
    def is_entry(self) -> bool:
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
    attrs: list[str] = []
    while True:
        am = re.search(r"\[\s*([A-Za-z][\w-]*)\s*\]\s*$", tail)
        if not am:
            break
        attrs.insert(0, am.group(1))
        tail = tail[:am.start()]
    for a in attrs:
        if a not in ALLOWED_ATTRS:
            raise SpecError(f"claim attribute [{a}] is not allowed")
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
# K Int / Bool expression evaluator
# ---------------------------------------------------------------------------

TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<op>\+Int|-Int|\*Int|/Int|%Int|divInt|modInt|\^Int|<=Int|>=Int|<Int|>Int|==Int|=/=Int
          |andBool|orBool|xorBool|impliesBool|notBool|==Bool|=/=Bool)
  | (?P<kw>\#if|\#then|\#else|\#fi)
  | (?P<int>-?\d+)
  | (?P<ident>\??[A-Za-z_][A-Za-z0-9_]*)
  | (?P<punct>[(),])
""", re.X)

BINOPS = {  # operator -> precedence (higher binds tighter)
    "^Int": 60, "*Int": 50, "/Int": 50, "%Int": 50, "divInt": 50, "modInt": 50,
    "+Int": 40, "-Int": 40,
    "<Int": 30, "<=Int": 30, ">Int": 30, ">=Int": 30, "==Int": 30, "=/=Int": 30,
    "==Bool": 25, "=/=Bool": 25,
    "andBool": 20, "xorBool": 18, "orBool": 16, "impliesBool": 14,
}
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
        while True:
            k, v = self.peek()
            if k != "op" or v not in BINOPS or BINOPS[v] < min_prec:
                return left
            self.i += 1
            right = self.expr(BINOPS[v] + 1)  # left-assoc
            left = ("bin", v, left, right)

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
    if op in ("andBool", "orBool", "xorBool", "impliesBool", "==Bool", "=/=Bool"):
        _need(l, bool, op)
        _need(r, bool, op)
        return {"andBool": l and r, "orBool": l or r, "xorBool": l != r,
                "impliesBool": (not l) or r, "==Bool": l == r, "=/=Bool": l != r}[op]
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

def entry_claim(mod: Module) -> tuple[Claim, list[Claim]]:
    parsed = [parse_claim(c) for c in mod.claims]
    entries = [c for c in parsed if c.is_entry]
    if len(entries) != 1:
        raise SpecError(f"expected exactly one entry claim (with <scopeLoc>), found {len(entries)}")
    others = [c for c in parsed if not c.is_entry]
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


def sample_inputs(kvars: list[str], requires: str | None, *, n: int, seed: int,
                  lo: int = -25, hi: int = 25) -> list[dict[str, int]]:
    """Deterministic random inputs satisfying the frozen precondition."""
    rng = random.Random(seed)
    req = parse_expr(requires) if requires else None
    out: list[dict[str, int]] = []
    seen: set[tuple] = set()
    tries = 0
    while len(out) < n and tries < 5000:
        tries += 1
        cand = {k: rng.randint(lo, hi) for k in kvars}
        key = tuple(cand[k] for k in kvars)
        if key in seen:
            continue
        if req is not None and eval_expr(req, dict(cand)) is not True:
            continue
        seen.add(key)
        out.append(cand)
    if len(out) < n:
        raise SpecError("could not sample enough inputs satisfying the precondition")
    return out


def check_closed_forms(entry: Claim, *, code: str, inputs: Inputs, requires: str | None,
                       fn_names: list[str], n_samples: int = 24, seed: int = 20261030) -> list[str]:
    """The proved-spec semantic check: the final scope pins every program
    variable to a term whose value agrees with CPython on random inputs
    satisfying the precondition, and the ensures clause determines every
    existential uniquely."""
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
    bare: dict[str, str] = {}
    for name, ast in terms.items():
        if ast[0] == "var" and ast[1].startswith("?"):
            bare.setdefault(ast[1], name)
    used: set[str] = set()
    for ast in terms.values():
        used |= {v for v in free_vars(ast) if v.startswith("?")}
    if ensures_ast is not None:
        used |= {v for v in free_vars(ensures_ast) if v.startswith("?")}
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
            for ex in bare:
                for delta in (1, -1, 7):
                    env2 = dict(env)
                    env2[ex] += delta
                    if ensures_ast is None or eval_expr(ensures_ast, env2) is not False:
                        problems.append(f"{ex} is not pinned: ensures also holds at {ex} {delta:+d}")
                        return problems
        except EvalError as e:
            return [f"evaluation error at inputs {sample}: {e}"]
    return problems
