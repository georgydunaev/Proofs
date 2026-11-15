# Constructive Proof Strategy and Helper Lemmas for `functional_completeness.v`

## 1. Overview

In `/botworkspace/Proofs/functional_completeness.v` (1,307 lines), the file is organized into two major parts:
1. **Lines 1 to 1015 (Diagonal Matrix Encoding and Variable-Counting Combinatorics)**: Defines custom inductive types (`Bool`, `Nat`/`nat`, `Unit`, `Empty`, `Fm`), the diagonal equality matrix `code_n` (mapping two `nat` arguments to `Bool`) via `addcorner`, the variable-existence indicator `dme`, and the finite accumulator `calcFIN`.
2. **Lines 1016 to 1307 (Boolean Functional Completeness of NAND and NOR)**: Proves without any `Admitted` steps the structural and truth-table functional completeness of the Sheffer stroke (`nand_functional_completeness`, `bool_fn_nand_completeness`) and Peirce arrow (`nor_functional_completeness`, `bool_fn_nor_completeness`) via Shannon expansion (`shannon_bform_correct`).

Within Part 1 (Lines 835 to 995), five intermediate lemmas in the `code_n` / `calcFIN` accumulator development were left with `Admitted` placeholders while exploring single-match HoTT proof terms (`idpath`, `ap`, `transport`). This document and its companion Coq module `modules/logic/sheffer_completeness_helpers.v` provide the complete constructive proofs for all five lemmas without modifying any stored `.vo` binaries.

---

## 2. Analysis of the Five `Admitted` Lemmas in `functional_completeness.v`

### 2.1 Lemma 1: `gte` (Lines 835 to 851)

- **Declaration in `functional_completeness.v`**:
  `Lemma gte m n : (gre m n) implies f m n = 0.`
- **Definitions**:
  - `f m n` sums `if code_n k m then 1 else 0` over $0 < k + 1 \le n$:
    - `f m 0 = 0`
    - `f m (S n') = add (if code_n n' m then 1 else 0) (f m n')`
  - `gre m n` holds when `compa m n` evaluates to `equal` or `greater` ($m \ge n$).
- **Constructive Proof Strategy**:
  1. Prove monotonicity/step-down of `gre`: if `gre m (S n')` holds, then both `gre m n'` and `code_n n' m = false` hold (since $n' < S n' \le m$).
  2. Specifically, by structural induction on $n$ with $m$ generalized:
     - Base case $n = 0$: `f m 0 = 0` definitionally by `idpath`.
     - Inductive step $n = S n'$:
       - If $m = 0$, `gre 0 (S n')` reduces to `Empty`, eliminating the goal immediately (`match H with end`).
       - If $m = S m'$, `gre (S m') (S n')` reduces to `gre m' n'`. By `qwerty m' n' H`, we obtain `bool_to_prop (bnot (code_n n' (S m')))`, which forces `code_n n' (S m') = false`.
       - Rewriting `code_n n' (S m')` to `false` simplifies `if code_n n' (S m') then 1 else 0` to `0`, and `add 0 (f (S m') n')` simplifies to `f (S m') n'`.
       - Applying `gre_succ_l` (from `gre m' n'` to `gre (S m') n'`) and the induction hypothesis `IHn (S m')` yields `f (S m') n' = 0`.

### 2.2 Lemma 2: `impprf2` (Lines 898 to 908)

- **Declaration in `functional_completeness.v`**:
  `Fixpoint impprf2 (m:nat) : (0 = dou f m).`
- **Definitions**:
  - `dou f m` unfolds to `f m m`.
  - Lines 885 to 889 already define `impprf4 (m : nat) : f m m = 0 := gte m m (gre_refl m)`.
- **Constructive Proof Strategy**:
  - Apply path inversion `invpath` (defined at Line 640) directly to `impprf4 m`:
    `Definition impprf2 (m : nat) : 0 = dou f m := invpath (impprf4 m).`

### 2.3 Lemma 3: `impprfWUT` (Lines 931 to 938)

- **Declaration in `functional_completeness.v`**:
  `Fixpoint impprfWUT (m:nat) : (fix acc (m0 : nat) : nat := match m0 with 0 => 0 | S m1 => (add (if code_n m1 m then 1 else 0) (acc m1))%nat end) m = 0.`
- **Constructive Proof Strategy**:
  - The inline fixpoint `fix acc (m0 : nat) : nat := ...` applied to `m` is definitionally convertible (`change ... with (f m m)`) with `f m m`.
  - Therefore `impprf4 m : f m m = 0` proves `impprfWUT m` directly without additional induction.

### 2.4 Lemma 4 (`thmhz`, Lines 950 to 963) and Lemma 5 (`calcFIN_eq`, Lines 965 to 994)

- **Declarations in `functional_completeness.v`**:
  - `Fixpoint thmhz (m:nat) : calcFIN (jst (S m)) (S m) = calcFIN (jst m) m.`
  - `Fixpoint calcFIN_eq (m:nat) : calcFIN (jst m) m = 1.`
- **Definitions**:
  - For a single-variable formula `jst m`, `dme (jst m) k = bool_to_nat (code_n k m)`.
  - `calcFIN (jst m) n = accumulate (dme (jst m)) n` sums `bool_to_nat (code_n k m)` for $k \in \{0, \dots, n\}$.
- **Constructive Proof Strategy**:
  1. Prove the strict-below zero-sum lemma `calcFIN_lt_zero`: for all $n$ and $m$, if `gre m n` ($m \ge n$), then `calcFIN (jst (S m)) n = 0`.
     - Base case $n = 0$: `calcFIN (jst (S m)) 0 = bool_to_nat (code_n 0 (S m)) = 0` definitionally.
     - Step $n = S n'$: since $m \ge S n'$, we have `code_n (S n') (S m) = code_n n' m = false`, so the head summand is `0` and the tail is `calcFIN (jst (S m)) n' = 0` by the induction hypothesis.
  2. Prove `calcFIN_eq (m : nat) : calcFIN (jst m) m = 1` by case analysis on $m$:
     - For $m = 0$: `calcFIN (jst 0) 0 = bool_to_nat (code_n 0 0) = 1` by computation (`idpath`).
     - For $m = S m'$:
       `calcFIN (jst (S m')) (S m') = add (bool_to_nat (code_n (S m') (S m'))) (calcFIN (jst (S m')) m')`.
       By `code_n_eq (S m')`, the first term is `1`, and by `calcFIN_lt_zero m' m' (gre_refl m')`, the second term is `0`, yielding `add 1 0 = 1`.
  3. Prove `thmhz (m : nat) : calcFIN (jst (S m)) (S m) = calcFIN (jst m) m`:
     - Concatenate `calcFIN_eq (S m) : calcFIN (jst (S m)) (S m) = 1` with `invpath (calcFIN_eq m) : 1 = calcFIN (jst m) m`.

---

## 3. Companion Formalization Module (`modules/logic/sheffer_completeness_helpers.v`)

The companion Coq source file `modules/logic/sheffer_completeness_helpers.v` implements all five constructive proofs above (`gte_constructive`, `impprf2_constructive`, `impprfWUT_constructive`, `calcFIN_eq_constructive`, and `thmhz_constructive`) together with helper lemmas `gre_succ_l`, `code_n_false_of_gre`, and `calcFIN_lt_zero`, with zero `Admitted` statements.
