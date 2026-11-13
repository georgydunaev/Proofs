(* Multi-theory algebra helpers: Rings and Polynomials *)

Record Monoid := {
 Monoid_set :> Set
}.

Record Ring : Type := {
 Ring_set :> Set;
 Ring_zero : Ring_set;
}.

Record Polynomes (R : Ring) : Set :=
{
 polynome : (nat -> (Ring_set R));
 poly_finite : forall n, (polynome n) = (Ring_zero R)
}.

Theorem polys_are_ring (R : Ring) : Ring.
Proof.
simple refine (@Build_Ring _ _).
exact (nat -> (Ring_set R)).
intro n.
exact (Ring_zero R).
Defined.
