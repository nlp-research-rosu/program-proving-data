"""Regression checks for oracle/nop coverage and infrastructure failures."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(__file__).with_name("ci_rewards.py")


class RewardChecks(unittest.TestCase):
    def run_checker(self, trials: list[dict], *, expect: int, minimum: int) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            # Harbor also writes a job-level result, which is not a trial.
            (root / "result.json").write_text(json.dumps({"stats": {}}), encoding="utf-8")
            for i, trial in enumerate(trials):
                folder = root / f"run-{i}" / f"trial-{i}"
                folder.mkdir(parents=True)
                (folder / "result.json").write_text(json.dumps(trial), encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(CHECKER), str(root), "--expect", str(expect),
                 "--min-trials", str(minimum)], capture_output=True, text=True, check=False,
            )

    @staticmethod
    def trial(name: str, reward: int | None, *, exception: dict | None = None) -> dict:
        return {"task_name": name, "verifier_result": {"rewards": {"reward": reward}},
                "exception_info": exception}

    def test_completed_oracle_trials(self) -> None:
        result = self.run_checker([self.trial("task-a", 1), self.trial("task-b", 1)],
                                  expect=1, minimum=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("2 trial(s), 0 unexpected", result.stdout)

    def test_completed_nop_trials(self) -> None:
        result = self.run_checker([self.trial("task-a", 0), self.trial("task-b", 0)],
                                  expect=0, minimum=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_exception_fails_even_with_matching_nop_reward(self) -> None:
        result = self.run_checker(
            [self.trial("task-a", 0, exception={"exception_type": "AgentSetupError"})],
            expect=0, minimum=1,
        )
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("exception=AgentSetupError", result.stdout)

    def test_duplicate_trials_do_not_establish_coverage(self) -> None:
        result = self.run_checker([self.trial("task-a", 1), self.trial("task-a", 1)],
                                  expect=1, minimum=2)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("duplicate task", result.stdout)

    def test_missing_or_wrong_reward_fails(self) -> None:
        for reward in (None, 0):
            with self.subTest(reward=reward):
                result = self.run_checker([self.trial("task-a", reward)], expect=1, minimum=1)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)

    def test_insufficient_trials_fail(self) -> None:
        result = self.run_checker([self.trial("task-a", 1)], expect=1, minimum=2)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("expected at least 2 trial(s)", result.stdout)


if __name__ == "__main__":
    unittest.main()
