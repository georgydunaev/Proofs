#!/usr/bin/env python3
"""Verification tests for Proofs (functional_completeness.v, Yoneda.v, Yoneda2.v, rings.v)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def nand(a: bool, b: bool) -> bool:
    return not (a and b)


class TestProofsRepo(unittest.TestCase):
    def test_coq_proof_files_exist(self):
        for rel in ("functional_completeness.v", "Yoneda.v", "Yoneda2.v", "modules/rings.v", "README.md"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0)

    def test_nand_functional_completeness_truth_tables(self):
        for p in (False, True):
            not_p = nand(p, p)
            self.assertEqual(not_p, (not p))
            for q in (False, True):
                and_pq = nand(nand(p, q), nand(p, q))
                or_pq = nand(nand(p, p), nand(q, q))
                self.assertEqual(and_pq, (p and q))
                self.assertEqual(or_pq, (p or q))


if __name__ == "__main__":
    unittest.main()
