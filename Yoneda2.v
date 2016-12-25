Definition hom {A:Type} (P Q: A -> Type) := forall x:A, (P x) -> (Q x).
Context {A:Type}.
Context (P P': A -> Type).
Context (tau : @hom A P P'). (*Anomaly!*)

Require Import HoTT.




Definition lem1 {A:Type} (P Q: A -> Type) (tau : hom P Q) (x y:A) (p:x=y) 
: (transport Q p) o (tau x) = (tau y) o (transport P p) 
:= match p with
   | idpath => idpath
   end.

Definition y {A:Type} (a x:A) := x = a.

Definition f {A:Type} (P:A->Type) (a:A): (P a) -> (hom (y a) P)
:= fun z x p => match p in (_ = y) return (P y -> P x) with
                | idpath => idmap
                end z.
(*Proof.
unfold hom, y.
intros z x p.
destruct p.
exact z.
Show Proof.
Defined.*)

Definition invf {A:Type} (P:A->Type) (a:A): (hom (y a) P) -> (P a) 
:= fun q => (q a idpath).
(*Proof.
unfold hom, y.
intros q.
exact (q a idpath).
Defined.*)

Definition f_sect A P a b: @invf A P a (@f A P a b) = b 
:= idpath.
(*unfold f, invf.
reflexivity.
Show Proof.*)

Definition f_retr `{Funext} A P a b: @f A P a (@invf A P a b) = b.
Proof.
unfold hom, y in b.
unfold f, invf.
unfold hom, y.
apply path_forall.
intro u.
apply path_forall.
intro p.
destruct p.
reflexivity.
Defined.

Context {A:Type}.
Context (P P': A -> Type).
Context (tau : @hom A P P').
 (a a':A) (p:a=a').

Definition natur {A:Type} (P P': A -> Type) (tau : hom P P') (a a':A) (p:a=a') :
hom((transport (y a) p) tau) = hom(transport y p, tau).


Eval compute in fun A P a b => @f A P a (@invf A P a b).

Check .