(* Multi-theory topology and category theory helpers: Categories and Presheaves *)

Record Category : Type := {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  id_m : forall A : Obj, Hom A A;
  comp_m : forall A B C : Obj, Hom B C -> Hom A B -> Hom A C;
  id_l : forall (A B : Obj) (f : Hom A B), comp_m A B B (id_m B) f = f;
  id_r : forall (A B : Obj) (f : Hom A B), comp_m A A B f (id_m A) = f;
  assoc_m : forall (A B C D : Obj) (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp_m A C D h (comp_m A B C g f) = comp_m A B D (comp_m B C D h g) f
}.

Record Presheaf (C : Category) : Type := {
  P_obj : Obj C -> Type;
  P_map : forall (A B : Obj C), Hom C A B -> P_obj B -> P_obj A;
  P_id : forall (A : Obj C) (x : P_obj A), P_map A A (id_m C A) x = x;
  P_comp : forall (A B C0 : Obj C) (f : Hom C A B) (g : Hom C B C0) (x : P_obj C0),
    P_map A C0 (comp_m C A B C0 g f) x = P_map A B f (P_map B C0 g x)
}.
