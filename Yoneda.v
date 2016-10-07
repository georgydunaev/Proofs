Require Import HoTT.
Require Import HoTT.Categories.
Require Import HoTT.Categories.Functor.Prod.Core.
Require Import HoTT.Categories.Category.Objects.
Section YonProo.
Context `{Funext} (C : Category) (F : Functor C set_cat) (A : C).
(*Context (u:(Core.object_of (induced_snd (hom_functor C) A) A) ->
         (Core.object_of F A)).*)
(*Context (w :(F _1 (m o x o 1))%morphism == (F _1 m)%morphism o ((F _1 x)%morphism)).*)
Theorem Yoneda : Equiv (NaturalTransformation (induced_snd (hom_functor C) A) F) (F A).
Proof.
simple refine (@BuildEquiv _ _ _ _).
intro g.
destruct g.
simple refine ((components_of A) _).
simpl.
exact (@identity C A).
simpl.
simple refine (@BuildIsEquiv _ _ _ _ _ _ _).
intro u.
Check Build_NaturalTransformation.
+ simple refine (@Build_NaturalTransformation _ _ _ _ _ _ ).
  simpl.
  intro X.
  intro f.
  Check @Core.object_of .
  exact ((@Core.morphism_of _ _ F _ _ f) u).
  simpl.
  intros s d m.
  refine (@path_forall _ _ _ _ _ _).
  intro x.
  Check (F _1 (m o x o 1))%morphism .
  simple refine (@happly _ _ _ _ _ _).
  refine (F _1 (m o x o 1))%morphism.
  reflexivity.
+ simpl.

(*====stop here====*)

(*  hott_simpl.
  refine @funext_Op.*)

Admitted.
End YonProo.

(*Require Import Category.Core Category.Morphisms.
Require Import HoTT.Tactics Trunc.
Require Import HoTT.Categories.Category.Univalent.
Require Import InitialTerminalCategory.*)

Check Equiv Unit Unit.
Check Isomorphic.
Check hom_functor C.
Check induced_snd (hom_functor C) A.