# Project Overview: Propositional Functional Completeness and Yoneda Proofs in Coq (`Proofs`)

## 1. Purpose and Scope
`Proofs` (`/botworkspace/Proofs`) contains mechanized Coq formalizations of truth-functional completeness for propositional logic (`functional_completeness.v` and `modules/`) and categorical Yoneda Lemma encodings (`Yoneda.v`, `Yoneda2.v`). Compiled `.vo` object files are treated as immutable build artifacts per Fact 11.

## 2. Architecture and Key Files
- [functional_completeness.v](file:///botworkspace/Proofs/functional_completeness.v) — Monolithic Coq development proving truth-table representation, Disjunctive Normal Form (`DNF`) / Conjunctive Normal Form (`CNF`) synthesis, and functional completeness of classical connectives (`NAND` / Sheffer stroke).
- `modules/` — Modular decomposition of `functional_completeness.v` into syntax, valuation semantics, normal form transformations, and completeness theorems.
- [Yoneda.v](file:///botworkspace/Proofs/Yoneda.v) and [Yoneda2.v](file:///botworkspace/Proofs/Yoneda2.v) — Coq formalizations of categories, functors, natural transformations, and the Yoneda Lemma.
- [REPOSITORY_CATALOG_AND_NOTES.md](file:///botworkspace/Proofs/REPOSITORY_CATALOG_AND_NOTES.md) and [FUNCTIONAL_COMPLETENESS_PROOF_NOTES.md](file:///botworkspace/Proofs/FUNCTIONAL_COMPLETENESS_PROOF_NOTES.md) — Detailed theorem catalog and proof architecture notes.
- `tests/` — Automated Python verification suite inspecting theorem declarations and proof structure.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/Proofs/tests -p "test_*.py"
```
