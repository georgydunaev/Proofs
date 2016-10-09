Require Import HoTT.
Require Import HoTT.Categories.
Require Import HoTT.Categories.Functor.Prod.Core.
Require Import HoTT.Categories.Category.Objects.

Open Scope morphism.

Theorem qwe
(H : Funext)
(C : Category)
(F : Functor C set_cat)
(A : C)
(w : F A):
(F _1 1)%morphism w = w.
Proof.
  simple refine (@happly _ _ _ _ _ _).
  exact (@identity_of C set_cat F A).
Defined.

Section eqpro.
Context (H : Funext) (C : Category) (A : C).
Definition hA  := induced_snd (hom_functor C) A.

Section calc.
Context (X : C) (f: @morphism C A X).
Definition hAf := @morphism_of _ _ hA _ _ f.
Theorem fuho : hAf (identity A) = f.
Proof.
 unfold hAf.
 simpl.
 refine (@concat _ _ _ _ _ _ ).
 refine (@right_identity C A X (f o 1)).
 refine (@right_identity C A X f).
Defined.
End calc.

Section YonProo.
Context (F : Functor C set_cat).
Theorem Yoneda : Equiv (NaturalTransformation hA F) (F A).
Proof.
  simple refine (@BuildEquiv _ _ _ _).
  * intro T. (* F A <- Nat hA F *)
    exact ((components_of T A) (@identity C A) ). 
  * simple refine (@BuildIsEquiv _ _ _ _ _ _ _).
    + intro u. (* F A -> Nat hA F *)
      simple refine (@Build_NaturalTransformation _ _ _ _ _ _ ).
      - simpl.
        intro X.
        intro f.
        exact ((@Core.morphism_of _ _ F _ _ f) u).
      - simpl.
        intros s d m.
        refine (@path_forall _ _ _ _ _ _).
        intro j.
        simple refine (@happly _ _ _ _ _ _).
        refine (F _1 (m o j o 1))%morphism.
        reflexivity.
    + simpl. (* Section -> *)
      intro u.
      simpl.
      refine (@qwe H C F A u). (*strange behaviour here*)
    + simpl. (* Section <- *)
      intro T.
      simpl.
(*====stop here====*)

Admitted.
End YonProo.


End eqpro.

(*
 Check (@right_identity C A X f)^.
 set (hA := induced_snd (hom_functor C) A).
 set (hAf := @morphism_of _ _ hA _ _ f).

  reflexivity.
  destruct F.
  hott_simpl.
  refine @funext_Op.*)

(*Require Import Category.Core Category.Morphisms.
Require Import HoTT.Tactics Trunc.
Require Import HoTT.Categories.Category.Univalent.
Require Import InitialTerminalCategory.
Check Equiv Unit Unit.
Check Isomorphic.
Check hom_functor C.
Check induced_snd (hom_functor C) A.*)