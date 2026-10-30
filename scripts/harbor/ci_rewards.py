#!/usr/bin/env python3
"""ci_rewards — assert the rewards of a finished `harbor run` job.

    python scripts/harbor/ci_rewards.py JOBS_DIR --expect 1   # oracle: every trial 1
    python scripts/harbor/ci_rewards.py JOBS_DIR --expect 0   # nop: every trial 0

Walks every trial result.json under JOBS_DIR, prints one line per trial and
exits 1 if any trial is missing a reward or has a reward other than --expect.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("jobs_dir", type=Path)
    ap.add_argument("--expect", type=float, required=True)
    ap.add_argument("--min-trials", type=int, default=1)
    a = ap.parse_args()
    results = sorted(p for p in a.jobs_dir.rglob("result.json") if p.parent.parent != a.jobs_dir or True)
    bad = 0
    n = 0
    for p in results:
        data = json.loads(p.read_text(encoding="utf-8"))
        if "task_name" not in data:  # a job-level result.json
            continue
        n += 1
        vr = data.get("verifier_result") or {}
        rewards = vr.get("rewards") or {}
        reward = rewards.get("reward", next(iter(rewards.values()), None)) if rewards else None
        exc = (data.get("exception_info") or {}).get("exception_type")
        ok = reward is not None and float(reward) == a.expect
        bad += not ok
        print(f"[{'ok' if ok else 'FAIL'}] {data['task_name']:34s} reward={reward!r}" + (f" exception={exc}" if exc else ""))
    print(f"{n} trial(s), {bad} unexpected")
    if n < a.min_trials:
        print(f"expected at least {a.min_trials} trial(s)")
        return 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
