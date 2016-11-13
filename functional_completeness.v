Require Import HoTT.

Section logic.
Context (Var:Type).


(* Inductive Fm (n:nat) :=
| jst : (Var)-> (Fm 1). *)

Check negb.

Inductive Fm :=
| jst : (Var)-> Fm
| not : Fm->Fm.
(*| and : Fm -> Fm -> Fm. *)

Fixpoint expansion (f:Var->Bool) (m:Fm) : Bool.
Proof.
induction m.
exact (f v).
Check not.
exact (negb IHm). (*?*)
Defined.
End logic.

Eval simpl in  (@expansion Bool (idmap) (jst Bool true)).
Eval simpl in  (@expansion Bool (idmap) (not Bool (jst Bool true))).


(*===*)







destruct m as [[a][b]].


Theorem(*)
Fixpoint*) expansion:(Var->Bool)->(Fm->Bool).
Proof.
intros f m.
destruct m.
exact (f v).

Defined.

Theorem con  : Fm -> {n : nat & (((Fin n) -> Bool) -> Bool)}.
Proof.
intro fm.
destruct fm.
refine (1; _).
intro f.
exact (f (inr tt)).

Admitted.

Theorem fcompleteness (n : nat)
(phi : ((Fin n) -> Bool) -> Bool) 
: { A : Fm & phi = (con A).2}.



(*===*)
(forall m, () -> Bool)