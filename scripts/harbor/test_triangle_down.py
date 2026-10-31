"""The task's solver-friendly triangle target must retain the corpus meaning."""
from pathlib import Path
import unittest

import kclaims as K

ROOT = Path(__file__).resolve().parents[2]


class TriangleDownChecks(unittest.TestCase):
    def test_entry_and_circularity_preserve_negative_zero_and_positive_inputs(self) -> None:
        corpus = (ROOT / "corpus/specs/kb-triangle-down/spec.k").read_text()
        original = K.parse_module(corpus, verification_module="KB-TRIANGLE-DOWN-VERIFICATION")
        original_entry, original_loops = K.entry_claim(original)
        _, original_rhs = K.split_scopes(original_entry.cells["scopes"])
        original_n = K.parse_expr(dict(K.parse_scope_map(original_rhs))["n"])
        original_loop = K.parse_expr(original_loops[0].ensures)
        for family in ("inv", "spec"):
            with self.subTest(family=family):
                text = (ROOT / f"tasks/k-{family}-kb-triangle-down/solution/spec.k").read_text()
                target = K.parse_module(text, verification_module="MPY-VERIFICATION")
                entry, loops = K.entry_claim(target)
                _, rhs = K.split_scopes(entry.cells["scopes"])
                target_n = K.parse_expr(dict(K.parse_scope_map(rhs))["n"])
                target_loop = K.parse_expr(loops[0].ensures)
                self.assertNotIn("minInt", K.strip_comments(text))
                self.assertEqual(len(loops), 1)
                self.assertEqual(entry.requires, original_entry.requires)
                self.assertEqual(entry.ensures, original_entry.ensures)
                self.assertEqual(loops[0].cells, original_loops[0].cells)
                self.assertEqual(loops[0].requires, original_loops[0].requires)
                for n in (-10**20, -2, -1, 0, 1, 2, 10**20):
                    self.assertEqual(K.eval_expr(original_n, {"N": n}),
                                     K.eval_expr(target_n, {"N": n}))
                    for s in (-13, 0, 17):
                        expected_f = min(n, 0)
                        expected_t = s + max(n, 0) * (max(n, 0) + 1) // 2
                        for f, t in ((expected_f, expected_t), (expected_f + 1, expected_t),
                                     (expected_f, expected_t + 1)):
                            env = {"I": n, "S": s, "?F": f, "?T": t}
                            self.assertEqual(K.eval_expr(original_loop, env),
                                             K.eval_expr(target_loop, env))


if __name__ == "__main__":
    unittest.main()
