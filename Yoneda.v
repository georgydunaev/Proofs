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


Section YonProo.
Context `{Funext} (C : Category) (F : Functor C set_cat) (A : C).
Theorem Yoneda : Equiv (NaturalTransformation (induced_snd (hom_functor C) A) F) (F A).
Proof.
simple refine (@BuildEquiv _ _ _ _).
* intro g.
  simple refine ((components_of g A) _).
  simpl.
  exact (@identity C A).
* simpl.
simple refine (@BuildIsEquiv _ _ _ _ _ _ _).
intro u.
+ simple refine (@Build_NaturalTransformation _ _ _ _ _ _ ).
  simpl.
  intro X.
  intro f.
  Check @Core.object_of .
  exact ((@Core.morphism_of _ _ F _ _ f) u).
  simpl.
  intros s d m.

  refine (@path_forall _ _ _ _ _ _).
  intro j.
  simple refine (@happly _ _ _ _ _ _).
  refine (F _1 (m o j o 1))%morphism.
  reflexivity.
+ simpl.
  intro w.
  simpl.
  refine (@qwe H C F A w). (*strange behaviour here*)
+ simpl.
  intro w.
  simpl.
(*====stop here====*)

(*
  reflexivity.
  destruct F.
  hott_simpl.
  refine @funext_Op.*)

Admitted.
End YonProo.

(*Require Import Category.Core Category.Morphisms.
Require Import HoTT.Tactics Trunc.
Require Import HoTT.Categories.Category.Univalent.
Require Import InitialTerminalCategory.
Check Equiv Unit Unit.
Check Isomorphic.
Check hom_functor C.
Check induced_snd (hom_functor C) A.*)