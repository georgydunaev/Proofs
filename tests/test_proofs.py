#!/usr/bin/env python3
"""Verification tests for Proofs (functional_completeness.v, Yoneda.v, Yoneda2.v, rings.v, submodules)."""

import os
import subprocess
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def nand(a: bool, b: bool) -> bool:
    return not (a and b)


def nor(a: bool, b: bool) -> bool:
    return not (a or b)


class BForm:
    pass


class BVar(BForm):
    def __init__(self, var_id: int):
        self.var_id = var_id


class BConst(BForm):
    def __init__(self, val: bool):
        self.val = val


class BNot(BForm):
    def __init__(self, sub: BForm):
        self.sub = sub


class BAnd(BForm):
    def __init__(self, left: BForm, right: BForm):
        self.left = left
        self.right = right


class BOr(BForm):
    def __init__(self, left: BForm, right: BForm):
        self.left = left
        self.right = right


class BImp(BForm):
    def __init__(self, left: BForm, right: BForm):
        self.left = left
        self.right = right


class BIff(BForm):
    def __init__(self, left: BForm, right: BForm):
        self.left = left
        self.right = right


class Fm:
    pass


class Jst(Fm):
    def __init__(self, var_id: int):
        self.var_id = var_id


class NandFm(Fm):
    def __init__(self, left: Fm, right: Fm):
        self.left = left
        self.right = right


class NorFm:
    pass


class NorVar(NorFm):
    def __init__(self, var_id: int):
        self.var_id = var_id


class NorOp(NorFm):
    def __init__(self, left: NorFm, right: NorFm):
        self.left = left
        self.right = right


def eval_bform(f: BForm, env: dict) -> bool:
    if isinstance(f, BVar):
        return env.get(f.var_id, False)
    if isinstance(f, BConst):
        return f.val
    if isinstance(f, BNot):
        return not eval_bform(f.sub, env)
    if isinstance(f, BAnd):
        return eval_bform(f.left, env) and eval_bform(f.right, env)
    if isinstance(f, BOr):
        return eval_bform(f.left, env) or eval_bform(f.right, env)
    if isinstance(f, BImp):
        return (not eval_bform(f.left, env)) or eval_bform(f.right, env)
    if isinstance(f, BIff):
        return eval_bform(f.left, env) == eval_bform(f.right, env)
    raise ValueError(f"Unknown formula: {f}")


def eval_nand(f: Fm, env: dict) -> bool:
    if isinstance(f, Jst):
        return env.get(f.var_id, False)
    if isinstance(f, NandFm):
        return nand(eval_nand(f.left, env), eval_nand(f.right, env))
    raise ValueError(f"Unknown NAND formula: {f}")


def eval_nor(f: NorFm, env: dict) -> bool:
    if isinstance(f, NorVar):
        return env.get(f.var_id, False)
    if isinstance(f, NorOp):
        return nor(eval_nor(f.left, env), eval_nor(f.right, env))
    raise ValueError(f"Unknown NOR formula: {f}")


def nand_not_fm(f: Fm) -> Fm:
    return NandFm(f, f)


def nand_and_fm(f1: Fm, f2: Fm) -> Fm:
    return nand_not_fm(NandFm(f1, f2))


def nand_or_fm(f1: Fm, f2: Fm) -> Fm:
    return NandFm(nand_not_fm(f1), nand_not_fm(f2))


def nand_true_fm() -> Fm:
    return NandFm(Jst(0), nand_not_fm(Jst(0)))


def nand_false_fm() -> Fm:
    return nand_not_fm(nand_true_fm())


def nand_imp_fm(f1: Fm, f2: Fm) -> Fm:
    return NandFm(f1, nand_not_fm(f2))


def nand_iff_fm(f1: Fm, f2: Fm) -> Fm:
    return nand_and_fm(nand_imp_fm(f1, f2), nand_imp_fm(f2, f1))


def to_nand(f: BForm) -> Fm:
    if isinstance(f, BVar):
        return Jst(f.var_id)
    if isinstance(f, BConst):
        return nand_true_fm() if f.val else nand_false_fm()
    if isinstance(f, BNot):
        return nand_not_fm(to_nand(f.sub))
    if isinstance(f, BAnd):
        return nand_and_fm(to_nand(f.left), to_nand(f.right))
    if isinstance(f, BOr):
        return nand_or_fm(to_nand(f.left), to_nand(f.right))
    if isinstance(f, BImp):
        return nand_imp_fm(to_nand(f.left), to_nand(f.right))
    if isinstance(f, BIff):
        return nand_iff_fm(to_nand(f.left), to_nand(f.right))
    raise ValueError(f"Unknown formula: {f}")


def nor_not_fm(f: NorFm) -> NorFm:
    return NorOp(f, f)


def nor_or_fm(f1: NorFm, f2: NorFm) -> NorFm:
    return nor_not_fm(NorOp(f1, f2))


def nor_and_fm(f1: NorFm, f2: NorFm) -> NorFm:
    return NorOp(nor_not_fm(f1), nor_not_fm(f2))


def nor_false_fm() -> NorFm:
    return NorOp(NorVar(0), nor_not_fm(NorVar(0)))


def nor_true_fm() -> NorFm:
    return nor_not_fm(nor_false_fm())


def nor_imp_fm(f1: NorFm, f2: NorFm) -> NorFm:
    return nor_or_fm(nor_not_fm(f1), f2)


def nor_iff_fm(f1: NorFm, f2: NorFm) -> NorFm:
    return nor_and_fm(nor_imp_fm(f1, f2), nor_imp_fm(f2, f1))


def to_nor(f: BForm) -> NorFm:
    if isinstance(f, BVar):
        return NorVar(f.var_id)
    if isinstance(f, BConst):
        return nor_true_fm() if f.val else nor_false_fm()
    if isinstance(f, BNot):
        return nor_not_fm(to_nor(f.sub))
    if isinstance(f, BAnd):
        return nor_and_fm(to_nor(f.left), to_nor(f.right))
    if isinstance(f, BOr):
        return nor_or_fm(to_nor(f.left), to_nor(f.right))
    if isinstance(f, BImp):
        return nor_imp_fm(to_nor(f.left), to_nor(f.right))
    if isinstance(f, BIff):
        return nor_iff_fm(to_nor(f.left), to_nor(f.right))
    raise ValueError(f"Unknown formula: {f}")


class TestProofsRepo(unittest.TestCase):
    def test_coq_proof_files_exist(self):
        required_files = (
            "functional_completeness.v",
            "Yoneda.v",
            "Yoneda2.v",
            "modules/rings.v",
            "modules/algebra/rings.v",
            "modules/logic/sheffer_peirce.v",
            "modules/combinatorics/shannon_expansion.v",
            "modules/topology/yoneda_helpers.v",
            "README.md",
        )
        for rel in required_files:
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0)

    def test_nand_functional_completeness_truth_tables(self):
        for p in (False, True):
            not_p = nand(p, p)
            self.assertEqual(not_p, (not p))
            true_p = nand(p, nand(p, p))
            self.assertTrue(true_p)
            false_p = nand(true_p, true_p)
            self.assertFalse(false_p)
            for q in (False, True):
                and_pq = nand(nand(p, q), nand(p, q))
                or_pq = nand(nand(p, p), nand(q, q))
                imp_pq = nand(p, nand(q, q))
                iff_pq = nand(nand(imp_pq, nand(q, nand(p, p))), nand(imp_pq, nand(q, nand(p, p))))
                self.assertEqual(and_pq, (p and q))
                self.assertEqual(or_pq, (p or q))
                self.assertEqual(imp_pq, ((not p) or q))
                self.assertEqual(iff_pq, (p == q))

    def test_nor_functional_completeness_truth_tables(self):
        for p in (False, True):
            not_p = nor(p, p)
            self.assertEqual(not_p, (not p))
            false_p = nor(p, nor(p, p))
            self.assertFalse(false_p)
            true_p = nor(false_p, false_p)
            self.assertTrue(true_p)
            for q in (False, True):
                or_pq = nor(nor(p, q), nor(p, q))
                and_pq = nor(nor(p, p), nor(q, q))
                imp_pq = nor(nor(nor(p, p), q), nor(nor(p, p), q))
                self.assertEqual(or_pq, (p or q))
                self.assertEqual(and_pq, (p and q))
                self.assertEqual(imp_pq, ((not p) or q))

    def test_bform_to_nand_and_nor_semantic_equivalence(self):
        sample_formulas = [
            BVar(0),
            BNot(BVar(0)),
            BAnd(BVar(0), BVar(1)),
            BOr(BVar(0), BVar(1)),
            BImp(BVar(0), BVar(1)),
            BIff(BVar(0), BVar(1)),
            BAnd(BOr(BVar(0), BNot(BVar(1))), BImp(BVar(2), BVar(0))),
            BIff(BAnd(BVar(0), BVar(1)), BOr(BNot(BVar(2)), BConst(True))),
        ]

        environments = [
            {0: v0, 1: v1, 2: v2}
            for v0 in (False, True)
            for v1 in (False, True)
            for v2 in (False, True)
        ]

        for formula in sample_formulas:
            nand_ast = to_nand(formula)
            nor_ast = to_nor(formula)
            for env in environments:
                orig_val = eval_bform(formula, env)
                nand_val = eval_nand(nand_ast, env)
                nor_val = eval_nor(nor_ast, env)
                self.assertEqual(orig_val, nand_val, f"NAND mismatch on {env}")
                self.assertEqual(orig_val, nor_val, f"NOR mismatch on {env}")

    def test_shannon_expansion_completeness(self):
        # Test all 16 two-variable truth tables
        for code in range(16):
            table = {
                (False, False): bool(code & 1),
                (False, True): bool(code & 2),
                (True, False): bool(code & 4),
                (True, True): bool(code & 8),
            }

            f_true_true = BConst(table[(True, True)])
            f_true_false = BConst(table[(True, False)])
            f_false_true = BConst(table[(False, True)])
            f_false_false = BConst(table[(False, False)])

            f_x0_true = BOr(BAnd(BVar(1), f_true_true), BAnd(BNot(BVar(1)), f_true_false))
            f_x0_false = BOr(BAnd(BVar(1), f_false_true), BAnd(BNot(BVar(1)), f_false_false))
            shannon_ast = BOr(BAnd(BVar(0), f_x0_true), BAnd(BNot(BVar(0)), f_x0_false))

            nand_ast = to_nand(shannon_ast)
            nor_ast = to_nor(shannon_ast)

            for x0 in (False, True):
                for x1 in (False, True):
                    env = {0: x0, 1: x1}
                    expected = table[(x0, x1)]
                    self.assertEqual(eval_bform(shannon_ast, env), expected)
                    self.assertEqual(eval_nand(nand_ast, env), expected)
                    self.assertEqual(eval_nor(nor_ast, env), expected)

    def test_coq_compilation_all_files(self):
        coq_files = [
            "functional_completeness.v",
            "modules/rings.v",
            "modules/algebra/rings.v",
            "modules/logic/sheffer_peirce.v",
            "modules/combinatorics/shannon_expansion.v",
            "modules/topology/yoneda_helpers.v",
        ]
        for rel in coq_files:
            path = os.path.join(ROOT, rel)
            res = subprocess.run(["coqc", path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            self.assertEqual(res.returncode, 0, f"coqc failed on {rel}:\n{res.stderr}\n{res.stdout}")


if __name__ == "__main__":
    unittest.main()
