Require Import HoTT.
Require Import HoTT.Categories.
Require Import HoTT.Categories.Functor.Prod.Core.
Require Import HoTT.Categories.Category.Objects.
Require Import HoTT.Categories.NaturalTransformation.Paths.

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
Context `{Funext} (C : Category) (A : C). (*H : Funext*)
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
Theorem u_to_T : F A -> NaturalTransformation hA F.
Proof.
  intro u. 
  simple refine (@Build_NaturalTransformation _ _ _ _ _ _ ).
  - simpl.
    intro X.
    intro f.
    exact ((@Core.morphism_of _ _ F _ _ f) u).
  - simpl.
    intros s d m.
    simple refine (@path_forall _ _ _ _ _ _).
    intro j.
    simple refine (@concat _ _ _ _ _ _).  (*here*)
    + exact ((@morphism_of _ _ F _ _ (m o j)) u).
    + revert u.
      simple refine (@happly _ _ _ _ _).
      simple refine (@ap _ _ _ _ _ _).
      exact (@right_identity C _ _ (m o j)).
    + simple refine (@concat _ _ _ _ _ _). 
      * exact (((F _1 m) o (F _1 j)) u).
      * revert u.
        simple refine (@happly _ _ _ _ _).
        simple refine (@composition_of _ _ F _ _ _ _ _).
      * reflexivity.
Defined.

Theorem T_to_u : NaturalTransformation hA F -> F A .
Proof.
  intro T.
  exact ((components_of T A) (@identity C A) ). 
Defined.

Theorem Yoneda : Equiv (NaturalTransformation hA F) (F A).
Proof.
  simple refine (@BuildEquiv _ _ _ _).
  * exact T_to_u. (* F A <- Nat hA F *)
  * simple refine (@BuildIsEquiv _ _ _ _ _ _ _).
  simpl.
    + exact u_to_T. (* F A -> Nat hA F *)
    + simpl. (* Section -> *)
      intro u.
      simpl.
      refine (@qwe H C F A u). (*strange behaviour here*)
    + simpl. (* Section <- *)
      intro T.
      simple refine (@path_natural_transformation _ _ _ _ _ _ _ _ ).
      simpl.
      intro X .
      Check Core.components_of T X.
      simple refine (@path_forall _ _ _ _ _ _).
      intro f.
      unfold T_to_u.
      Check Core.components_of T X f.
      simple refine (@concat _ _ _ _ _ _). 
      - exact (((F _1 f) o (T A)) 1).
      - reflexivity.
      - simple refine (@concat _ _ _ _ _ _).
        ** exact ((T X o hA _1 f) 1).
        ** simple refine ((@happly _ _ _ _ _) 1).
           exact (@commutes _ _ _ _ T A X f)^.
        ** simple refine (@concat _ _ _ _ _ _).
           ++ exact (T X (hA _1 f 1)).
           ++ reflexivity.
           ++ simple refine ((@ap _ _ _ _ _ _)).
              refine (@fuho _ _).
    + simpl.
      intro T.
      unfold qwe.
      Check ap10 (identity_of F A) (T_to_u T).
      simpl.
(*====stop here====*)
      admit.
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