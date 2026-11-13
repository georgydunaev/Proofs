(* Multi-theory combinatorics helpers: Shannon Expansion for Boolean functions *)

Inductive Bool : Set := | true : Bool | false : Bool.

Fixpoint powern (X Y : Type) (n : nat) : Type :=
  match n with
  | 0 => Y
  | S n' => X -> powern X Y n'
  end.

Definition b_not (b : Bool) : Bool :=
  match b with
  | true => false
  | false => true
  end.

Definition b_and (b1 b2 : Bool) : Bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition b_or (b1 b2 : Bool) : Bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Lemma b_or_false_r : forall x : Bool, b_or x false = x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma b_and_true_r : forall x : Bool, b_and x true = x.
Proof.
  destruct x; reflexivity.
Qed.
