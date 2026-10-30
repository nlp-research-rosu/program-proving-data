#!/usr/bin/env python3
"""run_concrete — generate the A-family (concrete) trace samples.

For each program: py2mpy_traced -> krun (traced build, watchdogged) ->
extract <trace> events -> assemble CWM-style stream -> differentially
validate against CPython sys.settrace -> emit JSONL + Markdown.

A sample is only written if validation passes (exact event match)."""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts"))

import kastjson  # noqa: E402
import tracelib  # noqa: E402
from py2mpy_traced import to_mpy  # noqa: E402

KRUN_TIMEOUT = 120  # watchdog: krun of these programs takes seconds; longer = stuck

SAMPLES = [
    ("a1_sum_to_n", "programs/sum_to_n.py", "sum_to_n", {"n": 5}),
    ("a2_gcd", "programs/gcd.py", "gcd", {"a": 48, "b": 18}),
    ("a3_collatz_steps", "programs/collatz_steps.py", "collatz_steps", {"n": 6}),
    ("a4_half_of_even", "programs/half_of_even.py", "half_of_even", {"x": 7}),
]


def klever_sha() -> str:
    m = re.search(r"Git SHA: (\w+)", (ROOT / "vendor/klever/VENDOR.md").read_text())
    return m.group(1) if m else "unknown"


def k_version() -> str:
    out = subprocess.run(["kompile", "--version"], capture_output=True, text=True).stdout
    m = re.search(r"v[\d.]+", out)
    return m.group(0) if m else "unknown"


def krun_json(mpy_path: Path) -> dict:
    cmd = ["krun", "--definition", str(ROOT / "build/k/traced"), str(mpy_path), "--output", "json"]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=KRUN_TIMEOUT)
    # krun's exit code mirrors the <exit-code> cell (1 after an assertion
    # failure), so judge success by parseable output, not the return code.
    try:
        return json.loads(p.stdout)["term"]
    except (json.JSONDecodeError, KeyError):
        raise RuntimeError(
            f"krun produced no config on {mpy_path} (exit {p.returncode}):\n{p.stderr[:2000]}"
        ) from None


def to_markdown(rec: dict, ft: tracelib.FuncTable) -> str:
    has_rules = any("k_rules" in e for e in rec["trace"])
    hdr = "| # | event | line | source | locals / value |"
    sep = "|---|---|---|---|---|"
    if has_rules:
        hdr += " K rules applied |"
        sep += "---|"
    lines = [f"# {rec['id']}", "", "```python", rec["source"]["code"].rstrip(), "```", "",
             f"Entry: `{rec['source']['entry']}({rec['source']['args']})` — "
             f"validation: **{rec['provenance']['validation']['cpython_settrace']}**", "",
             hdr, sep]
    for i, e in enumerate(rec["trace"]):
        src = ft.src_line(e["line"])
        if e["event"] == "line":
            detail = json.dumps(e["locals"])
        elif e["event"] == "call":
            detail = f"args: {json.dumps(e['locals'])}"
        elif e["event"] == "return":
            detail = f"returns `{e['value']}` — locals {json.dumps(e['locals'])}"
        else:
            detail = f"**{e['exc']}** — locals {json.dumps(e['locals'])}"
        row = f"| {i} | {e['event']} | {e['line']} | `{src}` | {detail} |"
        if has_rules:
            names = " → ".join(
                r["name"] + (f"×{r['count']}" if r.get("count", 1) > 1 else "")
                for r in e.get("k_rules", []))
            row += f" {names} |"
        lines.append(row)
    lines.append("")
    if has_rules:
        lines += ["Rule names are defined in `semantics/mpy-traced/rules.yaml` "
                  "(file:line -> name/kind/description).", ""]
    return "\n".join(lines)


def build_one(sample_id: str, program: str, entry: str, args: dict) -> dict:
    py = ROOT / program
    ft = tracelib.FuncTable(str(py))

    mpy = ROOT / "build/k/mpy" / (py.stem + ".mpy")
    mpy.parent.mkdir(parents=True, exist_ok=True)
    mpy.write_text(to_mpy(str(py)))

    term = krun_json(mpy)
    raw = kastjson.raw_events(term)
    exc = kastjson.exc_name(term)
    k_events = tracelib.assemble_k_events(raw, ft, exc)

    py_events = tracelib.cpython_events(str(py))
    problems = tracelib.diff_events(k_events, py_events)
    if problems:
        print(f"[FAIL] {sample_id}: {len(problems)} differing steps", file=sys.stderr)
        for p in problems[:5]:
            print(p, file=sys.stderr)
        raise SystemExit(1)

    return {
        "id": f"concrete/{py.stem}/" + ",".join(f"{k}={v}" for k, v in args.items()),
        "kind": "concrete_trace",
        "source": {"file": program, "code": ft.source, "entry": entry, "args": args},
        "result": None if exc else kastjson.module_result(term),
        "exception": exc,
        "trace": k_events,
        "provenance": {
            "generator": "krun(MPY-TRACED)+llvm",
            "k": k_version(),
            "klever_sha": klever_sha(),
            "validation": {"cpython_settrace": "exact_match",
                           "cpython": ".".join(map(str, sys.version_info[:3]))},
        },
    }


def main() -> int:
    outdir = ROOT / "corpus/k/concrete"
    outdir.mkdir(parents=True, exist_ok=True)
    for sample_id, program, entry, args in SAMPLES:
        rec = build_one(sample_id, program, entry, args)
        (outdir / f"{sample_id}.jsonl").write_text(json.dumps(rec, sort_keys=True) + "\n")
        ft = tracelib.FuncTable(str(ROOT / program))
        (outdir / f"{sample_id}.md").write_text(to_markdown(rec, ft))
        n = len(rec["trace"])
        print(f"[ok] {sample_id}: {n} events, validated exact vs sys.settrace")
    return 0


if __name__ == "__main__":
    sys.exit(main())
