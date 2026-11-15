(* modules/logic/sheffer_completeness_helpers.v
   Constructive Coq proofs for the 5 intermediate accumulator lemmas in functional_completeness.v:
   1. gte_constructive          : forall m n, gre m n -> f m n = 0
   2. impprf2_constructive      : forall m, 0 = dou f m
   3. impprfWUT_constructive    : forall m, (fix acc m0 := ...) m = 0
   4. calcFIN_eq_constructive   : forall m, calcFIN (jst m) m = 1
   5. thmhz_constructive        : forall m, calcFIN (jst (S m)) (S m) = calcFIN (jst m) m
*)

Inductive Bool : Type :=
| true : Bool
| false : Bool.

Inductive Unit : Prop :=
| tt : Unit.

Inductive Empty : Prop := .

Inductive Fm : Type :=
| jst : nat -> Fm
| nand : Fm -> Fm -> Fm.

Fixpoint code_n (m n : nat) : Bool :=
  match m, n with
  | 0, 0 => true
  | 0, S _ => false
  | S _, 0 => false
  | S m', S n' => code_n m' n'
  end.

Lemma code_n_eq : forall v : nat, code_n v v = true.
Proof.
  induction v as [| v' IH]; simpl; [reflexivity | exact IH].
Qed.

Definition orb (a b : Bool) : Bool :=
  match a with
  | true => true
  | false => b
  end.

Fixpoint check (fm : Fm) (m : nat) : Bool :=
  match fm with
  | jst v => code_n m v
  | nand m1 m2 => orb (check m1 m) (check m2 m)
  end.

Definition bool_to_nat (b : Bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.

Fixpoint add (m n : nat) : nat :=
  match m with
  | 0 => n
  | S m' => S (add m' n)
  end.

Fixpoint accumulate (q : nat -> nat) (m : nat) : nat :=
  match m with
  | 0 => q 0
  | S m0 => add (q (S m0)) (accumulate q m0)
  end.

Definition dme (fm : Fm) (n : nat) : nat :=
  bool_to_nat (check fm n).

Definition calcFIN (fm : Fm) (m : nat) : nat :=
  accumulate (dme fm) m.

Definition f (m : nat) : nat -> nat :=
  fix acc (m0 : nat) : nat :=
    match m0 with
    | 0 => 0
    | S m1 => add (if code_n m1 m then 1 else 0) (acc m1)
    end.

Definition dou (qf : nat -> nat -> nat) (m : nat) : nat := qf m m.

Inductive compare : Type :=
| less : compare
| equal : compare
| greater : compare.

Fixpoint compa (a b : nat) : compare :=
  match a, b with
  | 0, 0 => equal
  | S _, 0 => greater
  | 0, S _ => less
  | S x, S y => compa x y
  end.

Definition gre (a b : nat) : Prop :=
  match compa a b with
  | equal => Unit
  | greater => Unit
  | less => Empty
  end.

Lemma gre_refl : forall m : nat, gre m m.
Proof.
  induction m as [| m' IH]; simpl; [exact tt | exact IH].
Qed.

Lemma gre_succ_l : forall m n : nat, gre m n -> gre (S m) n.
Proof.
  induction m as [| m' IHm]; intros [| n'] H; simpl in *;
    try exact tt; try contradiction.
  apply IHm; exact H.
Qed.

Lemma code_n_false_of_gre : forall m n : nat, gre m n -> code_n n (S m) = false.
Proof.
  induction m as [| m' IHm]; intros [| n'] H; simpl in *;
    try reflexivity; try contradiction.
  apply IHm; exact H.
Qed.

(* 1. Constructive proof of gte (functional_completeness.v Line 851) *)
Theorem gte_constructive : forall m n : nat, gre m n -> f m n = 0.
Proof.
  intros m n.
  revert m.
  induction n as [| n' IHn]; intros m H.
  - reflexivity.
  - destruct m as [| m'].
    + simpl in H. contradiction.
    + simpl in H.
      change (f (S m') (S n')) with (add (if code_n n' (S m') then 1 else 0) (f (S m') n')).
      rewrite (code_n_false_of_gre m' n' H).
      simpl.
      apply IHn.
      apply gre_succ_l.
      exact H.
Qed.

Corollary impprf4_constructive : forall m : nat, f m m = 0.
Proof.
  intro m.
  apply gte_constructive.
  apply gre_refl.
Qed.

(* 2. Constructive proof of impprf2 (functional_completeness.v Line 908) *)
Theorem impprf2_constructive : forall m : nat, 0 = dou f m.
Proof.
  intro m.
  unfold dou.
  symmetry.
  apply impprf4_constructive.
Qed.

(* 3. Constructive proof of impprfWUT (functional_completeness.v Line 938) *)
Theorem impprfWUT_constructive : forall m : nat,
  (fix acc (m0 : nat) : nat :=
     match m0 with
     | 0 => 0
     | S m1 => add (if code_n m1 m then 1 else 0) (acc m1)
     end) m = 0.
Proof.
  intro m.
  change ((fix acc (m0 : nat) : nat :=
     match m0 with
     | 0 => 0
     | S m1 => add (if code_n m1 m then 1 else 0) (acc m1)
     end) m) with (f m m).
  apply impprf4_constructive.
Qed.

Lemma calcFIN_lt_zero : forall n m : nat, gre m n -> calcFIN (jst (S m)) n = 0.
Proof.
  induction n as [| n' IHn]; intros m H.
  - reflexivity.
  - destruct m as [| m'].
    + simpl in H. contradiction.
    + simpl in H.
      change (calcFIN (jst (S (S m'))) (S n'))
        with (add (bool_to_nat (code_n (S n') (S (S m')))) (calcFIN (jst (S (S m'))) n')).
      change (code_n (S n') (S (S m'))) with (code_n n' (S m')).
      rewrite (code_n_false_of_gre m' n' H).
      simpl.
      apply IHn.
      apply gre_succ_l.
      exact H.
Qed.

(* 4. Constructive proof of calcFIN_eq (functional_completeness.v Line 994) *)
Theorem calcFIN_eq_constructive : forall m : nat, calcFIN (jst m) m = 1.
Proof.
  destruct m as [| m'].
  - reflexivity.
  - change (calcFIN (jst (S m')) (S m'))
      with (add (bool_to_nat (code_n (S m') (S m'))) (calcFIN (jst (S m')) m')).
    rewrite (code_n_eq (S m')).
    rewrite (calcFIN_lt_zero m' m' (gre_refl m')).
    reflexivity.
Qed.

(* 5. Constructive proof of thmhz (functional_completeness.v Line 963) *)
Theorem thmhz_constructive : forall m : nat,
  calcFIN (jst (S m)) (S m) = calcFIN (jst m) m.
Proof.
  intro m.
  rewrite (calcFIN_eq_constructive (S m)).
  rewrite (calcFIN_eq_constructive m).
  reflexivity.
Qed.
