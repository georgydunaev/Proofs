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
  revert u.
  Check ((F _1 (m o x o 1))%morphism = (F _1 m)%morphism o ((F _1 x)%morphism)).
  Check @path_forall.
  refine (@happly _ _ _ _ _).
  simpl.
  rewrite ((F _1 (m o x o 1))%morphism == (F _1 m)%morphism o ((F _1 x)%morphism)) .
  
  associativity.
  simpl.
  refine (@ap).

  refine (@path_forall _ _ _ _ _ _).

  hott_simpl.
  
  reflexivity.
  simpl.
  Check.
  refine @funext_Op.
  Goal 
fun x : Core.morphism C A s => (((F _1 (m o x o 1))%morphism u) =
 (F _1 m)%morphism ((F _1 x)%morphism u))
  simpl.
  Check ((F _1 (m o x o 1))%morphism u) = ((F _1 m)%morphism ((F _1 x)%morphism u)).
  Check ap.
  
  Check .
  reflexivity.

Check components_of A.
Check Core.object_of (induced_snd (hom_functor C) A) A.
(*Check fun (y : Core.object_of (induced_snd (hom_functor C) A) A) => u y.*)
Check Core.object_of (induced_snd (hom_functor C) A) A.


Check (Unit, tt).
construct.
Check morphism_of.
Check Build

Check Core.morphism.

Check Core.morphism.

Check Core.object_of F A.
split.
Check Equiv.

refine Build_Equiv.
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

(*
  Definition hom_functor_A : Functor  C set_cat.
    refine (Build_Functor (C) set_cat
                          (fun c => obj_of c)
                          hom_functor_morphism_of
                          _
                          _);
Theorem q : Core.Functor (C^op * C) Core.set_cat.
intro q;*)

Check (NaturalTransformation (induced_snd (hom_functor C) A) F).