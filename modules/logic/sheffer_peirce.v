(* Multi-theory logic helpers: Sheffer Stroke (NAND) and Peirce Arrow (NOR) Bases *)

Inductive Bool : Set := | true : Bool | false : Bool.

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

Definition b_nand (b1 b2 : Bool) : Bool :=
  b_not (b_and b1 b2).

Definition b_nor (b1 b2 : Bool) : Bool :=
  b_not (b_or b1 b2).

Theorem nand_is_not : forall p : Bool, b_nand p p = b_not p.
Proof.
  destruct p; reflexivity.
Qed.

Theorem nand_is_and : forall p q : Bool, b_nand (b_nand p q) (b_nand p q) = b_and p q.
Proof.
  destruct p; destruct q; reflexivity.
Qed.

Theorem nand_is_or : forall p q : Bool, b_nand (b_nand p p) (b_nand q q) = b_or p q.
Proof.
  destruct p; destruct q; reflexivity.
Qed.

Theorem nor_is_not : forall p : Bool, b_nor p p = b_not p.
Proof.
  destruct p; reflexivity.
Qed.

Theorem nor_is_or : forall p q : Bool, b_nor (b_nor p q) (b_nor p q) = b_or p q.
Proof.
  destruct p; destruct q; reflexivity.
Qed.

Theorem nor_is_and : forall p q : Bool, b_nor (b_nor p p) (b_nor q q) = b_and p q.
Proof.
  destruct p; destruct q; reflexivity.
Qed.
