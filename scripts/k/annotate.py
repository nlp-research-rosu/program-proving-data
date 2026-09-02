#!/usr/bin/env python3
"""annotate — attach rule-level `k_rules` annotations to the concrete samples.

Pipeline per sample:
  krun --proof-hint (traced-hints build)          -> binary rewrite trace
  kore-proof-trace --verbose (with definition)    -> text: every rule application
                                                     with its source file:line
  stack-parse (function/function exit nesting)    -> depth-0 rule stream
                                                     = the semantic rewrite steps
  segment at instrumentation boundaries           -> one rule segment per trace event
     trace.k LineMark rule   = line events
     patched/call.k push     = call events
     patched/functions.k pop = return events
  enrich via semantics/mpy-traced/rules.yaml                 -> {rule, name, kind, desc}

Alignment is positional and exact: the traced and traced-hints builds run the
same deterministic rewrite sequence, and the script asserts that boundary
counts equal event counts for every sample."""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent.parent
HINTS = ROOT / "build/k/hints"
DEF = ROOT / "build/k/traced-hints"

BOUNDARY_KINDS = {
    "trace.k:28": "line",
    "patched/call.k:70": "call",
    "patched/functions.k:86": "return",
}

SAMPLES = {
    "a1_sum_to_n": "sum_to_n",
    "a2_gcd": "gcd",
    "a3_collatz_steps": "collatz_steps",
    "a4_half_of_even": "half_of_even",
}


def rules_meta() -> dict[str, dict]:
    return yaml.safe_load((ROOT / "semantics/mpy-traced/rules.yaml").read_text())


def gen_hints_text(stem: str) -> Path:
    txt = HINTS / f"{stem}.txt"
    if txt.exists():
        return txt
    HINTS.mkdir(parents=True, exist_ok=True)
    header = HINTS / "header.bin"
    if not header.exists():
        subprocess.run(["timeout", "120", "kore-rich-header", str(DEF / "definition.kore"),
                        "-o", str(header)], check=True)
    hints = HINTS / f"{stem}.hints"
    with open(hints, "wb") as fh:
        subprocess.run(["timeout", "120", "krun", "--definition", str(DEF),
                        str(ROOT / "build/k/mpy" / f"{stem}.mpy"), "--proof-hint"],
                       stdout=fh, check=False)  # exit code mirrors <exit-code>
    with open(txt, "w") as fh:
        subprocess.run(["timeout", "300", "kore-proof-trace", "--verbose", str(header),
                        str(hints), str(DEF / "definition.kore")], stdout=fh,
                       stderr=subprocess.STDOUT, check=True)
    return txt


def short_src(src: str) -> str:
    """/abs/.../semantics/mpy-traced/patched/core.k:127 -> patched/core.k:127
       /abs/.../vendor/klever/src/semantics/controls.k:9 -> controls.k:9"""
    if not src:
        return "(generated)"
    path, line = src.rsplit(":", 1)
    p = Path(path)
    name = f"{p.name}:{line}"
    return f"patched/{name}" if p.parent.name == "patched" else name


def depth0_rules(txt: Path) -> list[str]:
    out, depth = [], 0
    rule_re = re.compile(r"rule: (\d+) \S+ \[[^\]]*\] \[([^\]]*)\]")
    for line in txt.read_text().splitlines():
        if line.startswith("function:"):
            depth += 1
        elif line.startswith("function exit:"):
            depth -= 1
        elif line.startswith("rule:") and depth == 0:
            m = rule_re.match(line)
            out.append(short_src(m.group(2)) if m else "(generated)")
    return out


def segment(rules: list[str]) -> tuple[list[str], list[tuple[str, list[str]]]]:
    """-> (prelude-rules, [(boundary-kind, segment-rules), ...])"""
    prelude: list[str] = []
    segs: list[tuple[str, list[str]]] = []
    cur: list[str] | None = None
    kind = None
    for r in rules:
        if r in BOUNDARY_KINDS:
            if cur is not None:
                segs.append((kind, cur))
            kind, cur = BOUNDARY_KINDS[r], []
            if kind in ("call", "return"):
                cur.append(r)  # the frame rule itself is part of the event
        elif cur is None:
            prelude.append(r)
        else:
            cur.append(r)
    if cur is not None:
        segs.append((kind, cur))
    return prelude, segs


def enrich(seq: list[str], meta: dict[str, dict]) -> list[dict]:
    """Collapse consecutive repeats and attach name/kind/desc."""
    out: list[dict] = []
    for r in seq:
        if out and out[-1]["rule"] == r:
            out[-1]["count"] += 1
            continue
        m = meta.get(r)
        if m is None:
            raise KeyError(f"rule {r} missing from semantics/mpy-traced/rules.yaml")
        out.append({"rule": r, "name": m["name"], "kind": m["kind"],
                    "desc": m["desc"], "count": 1})
    for e in out:
        if e["count"] == 1:
            del e["count"]
    return out


def annotate_record(rec: dict, stem: str, meta: dict[str, dict]) -> dict:
    txt = gen_hints_text(stem)
    prelude, segs = segment(depth0_rules(txt))

    events = rec["trace"]
    k_events = [e for e in events if e["event"] != "exception"]
    assert len(segs) == len(k_events), (
        f"{stem}: {len(segs)} rule segments vs {len(k_events)} trace events")
    for (kind, seg), ev in zip(segs, k_events):
        assert kind == ev["event"], f"{stem}: boundary kind {kind} vs event {ev['event']}"
        ev["k_rules"] = enrich(seg, meta)
    # the synthesized exception event owns no segment: the assert.fail rule sits
    # at the tail of the preceding line event's segment — point at it explicitly
    for e in events:
        if e["event"] == "exception":
            e["k_rules"] = [r for r in events[events.index(e) - 1]["k_rules"]
                            if r["name"].startswith("assert.")]
    rec["k_prelude_rules"] = enrich(prelude, meta)
    rec["provenance"]["k_rules_generator"] = (
        "krun --proof-hint + kore-proof-trace (depth-0 rewrite steps, "
        "positionally aligned; counts asserted)")
    return rec


def main() -> int:
    import run_concrete
    import tracelib
    meta = rules_meta()
    for sample_id, stem in SAMPLES.items():
        path = ROOT / "data/k/concrete" / f"{sample_id}.jsonl"
        rec = json.loads(path.read_text())
        rec = annotate_record(rec, stem, meta)
        path.write_text(json.dumps(rec, sort_keys=True) + "\n")
        ft = tracelib.FuncTable(str(ROOT / rec["source"]["file"]))
        (ROOT / "data/k/concrete" / f"{sample_id}.md").write_text(
            run_concrete.to_markdown(rec, ft))
        n = sum(len(e.get("k_rules", [])) for e in rec["trace"])
        print(f"[ok] {sample_id}: k_rules attached ({n} entries across {len(rec['trace'])} events)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
