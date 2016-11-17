Require Import HoTT.

Section somelogic.
(*Context (n:nat). (pv:(Fin n) = Var).*)
(*Definition Var := nat.*) (*Fin n.*)
Context {Var:Type}.
(*Context (n:nat). Definition Var := Fin n.*)
Context {decpavar:DecidablePaths Var}.

Inductive Fm :=
 | jst  : Var -> Fm
 | nand : Fm -> Fm -> Fm.

Coercion jst : Var >-> Fm.

(* Number of placeholders in formula. Higher bound of amount of variables.*)
Fixpoint Count (fm : Fm ) : nat.
Proof.
destruct fm as [v|m1 m2].
exact 1.
exact ((Count m1)+(Count m2))%nat.
Defined.

(* True if threre exist a varianle 'm' in formula 'fm'*)
(*Fixpoint check (fm : Fm ) (m:Var) : Bool :=
   match fm with
   | jst v =>
       match (decpavar v m) with
       | inl _ => true
       | inr _ => false
       end
   | nand m1 m2 => (check m1 m || check m2 m)%Bool
   end.*)
   
Definition check_help (fm : Fm ) (m:Var) (qqq: Fm -> Var -> Bool) : Bool :=
   match fm with
   | jst v =>
       match (decpavar v m) with
       | inl _ => true
       | inr _ => false
       end
   | nand m1 m2 => (qqq m1 m || qqq m2 m)%Bool
   end.

Fixpoint check (fm : Fm ) (m:Var) : Bool := check_help fm m check.

Definition repr : Bool -> nat :=
  fun b:Bool => match b with
  | true  => 1
  | false => 0
  end.

(*Calculate*)
Fixpoint accumulate (q:nat->nat) (m:nat) : nat :=
 (match m with
   | 0 => q 0
   | m0.+1 => ((q (m0.+1)) + accumulate q m0)%nat
   end).
   
   
(*(repr (check fm (num m0.+1))*)
   
Section ss00.
Context (num:nat->Var) (fm:Fm).
Definition qq : nat->nat := fun n => repr (check fm (num n)).
Definition calcFIN (m:nat) := 
 accumulate qq m.
End ss00.
 
(*Fixpoint calcFIN (num:nat->Var) (fm:Fm) (m:nat) : nat.
Proof.
destruct m.
exact (repr (check fm (num 0))).
exact ((repr (check fm (num (S m))))+(calcFIN num fm m))%nat.
Show Proof.
Defined.*)


Section Mun.
Context (mun:Var->nat).
Definition maximal_help (f:Fm->nat) (fm : Fm )  : nat :=
   match fm with
   | jst v => mun v
   | nand m1 m2 => max (f m1) (f m2)
   end.
   
Fixpoint maximal (fm : Fm ) : nat := (maximal_help (maximal) fm).

Definition calcINF (num:nat->Var) (fm:Fm) : nat :=
 calcFIN num fm (maximal fm).

End Mun.
End somelogic.
Check @calcINF.
Eval simpl in maximal idmap (nand (jst 3) (nand (jst 3) (jst 2))).
Eval simpl in calcINF idmap idmap (nand (jst 3) (nand (jst 3) (jst 2))).
Eval simpl in calcFIN idmap (nand (jst 3) (nand (jst 3) (jst 2))) 3. *)


Definition maximal_help (mun:Var->nat) (fm : Fm ) (f:Fm->nat) : nat :=
(*(fix maximal (mun : Var -> nat) (fm : Fm) {struct fm} : nat :=*)
   match fm with
   | jst v => mun v
   | nand m1 m2 => max (f m1) (f m2)
   end.
   
(*Function maximal_help2 mun fm f :=
   match fm with
   | jst v => mun v
   | nand m1 m2 => max (f m1) (f m2)
   end.*)
(*f:=maximal mun*)
Fixpoint maximal (mun:Var->nat) (fm : Fm ) : nat.
Proof.
exact (maximal_help mun fm (maximal mun)).
Defined.
(*destruct fm as [v|m1 m2].
exact (mun v).
exact (max (maximal mun m1) (maximal mun m2)).
Show Proof.
Defined.*)

Definition calcINF (num:nat->Var) (mun:Var->nat) (fm:Fm) : nat :=
 calcFIN num fm (maximal mun fm).
(*Reset calcINF.
Definition calcINF (num:nat->Var) (mun:Var->nat) (fm:Fm) : nat.
Proof.
set (tmp:=maximal mun fm).
unfold tmp.
exact (calcFIN num fm tmp).
Defined.*)
(* calcFIN num fm (maximal mun fm).*)

Definition usedvars (fm:Fm) : Type := hfiber (check fm) true.

Theorem calc (fm:Fm) : nat.
Proof.
Admitted.

End somelogic.
Check @calcINF.
Eval simpl in maximal idmap (nand (jst 3) (nand (jst 3) (jst 2))).
Eval simpl in calcINF idmap idmap (nand (jst 3) (nand (jst 3) (jst 2))).

Eval simpl in calcFIN idmap (nand (jst 3) (nand (jst 3) (jst 2))) 3.


exact (repr (check fm (num m))).
exact ((repr (check fm m))+calcFIN)
destruct fm as [v|m1 m2].
Admitted.



Check max.
Defined.

Eval simpl in (fun A B :Var => (Count (nand A B))). (*= fun _ _ : Var => 2*)


(*Coercion jst {Var:Type}{decpavar:DecidablePaths Var}: Var >-> Fm.*)

Eval simpl in calc ((nand (jst 3) (jst 4))). (*must be 2*)
Eval simpl in calc ((nand (jst 3) (jst 3))). (*must be 1*)

(*-----*)

Eval simpl in calc nat decidable_paths_nat ((nand nat (jst _ 3) (jst _ 4))).

Fixpoint add n m :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end.


(*
Check hfiber (check fm).
Definition usedvars (fm:Fm) : Type := sig (fun m:Var=> true = )
Check card.*)


Definition expansion : (Var -> Bool) -> (Fm -> Bool) 
:= (fix expan (f : Var -> Bool) (m : Fm) {struct m} : Bool :=
  match m with
  | jst v      => f v
  | nand m1 m2 => negb (andb (expan f m1) (expan f m2))
  end).

Definition mnot (m:Fm) : Fm := (nand m m).

Definition mand (m1 m2:Fm) : Fm := (mnot (nand m1 m2)).

(*
По построенной формуле можно получить все переменные,
которые были использованы при её построении. Сделаем это.
Точнее - получим число (конечное) использованных
переменных.
*)

Fixpoint Count (fm : Fm ) : nat.
Proof.
destruct fm as [v|m1 m2].
exact 1.
exact ((Count m1)+(Count m2))%nat.
Defined.





//(if tt then 1 else 0).

Fixpoint Count (fm : Fm ) : nat.
Proof.
destruct fm as [v|m1 m2].
exact 1.
exact ((Count m1)+(Count m2))%nat.
Defined.
Context (A B C:Var).

Eval simpl in (Count (jst A)).
Coercion jst : Var >-> Fm.

Eval simpl in (Count (nand A B)).
Eval simpl in (Count ((mnot (jst A)))).
Eval simpl in (Count (nand (mnot (jst A)) (mand (jst B) (jst C)))).


Fixpoint con (fm : Fm ) : {n : nat & (((Fin n) -> Bool) -> Bool)}.
Proof.
destruct fm.
refine (1; _).
intro f.
exact (f (inr tt)).
refine (((con fm1).1 + (con fm2).1)%nat; _).
intro q.

simpl.
Check con fm1.

exact (con (nand fm1 fm2)).
Defined.
Check con (nand fm1 fm2).
Check fcard.
Eval simpl in fcard (Bool).
Eval simpl in fcard (Fin 2) .
Admitted.

Theorem fcompleteness (n : nat)
(phi : ((Fin n) -> Bool) -> Bool) 
: { A : Fm & phi = (con A).2}.

End logic.


Eval simpl in  (@expansion Bool (idmap) (mnot Bool (jst Bool true))).

Eval simpl in  (@expansion Bool (idmap) 
(mand Bool 
 (mnot Bool (jst Bool false))
 (mnot Bool (jst Bool false))
)
).


(*------*)


Inductive Fm :=
| jst : (Var)-> Fm
| not : Fm->Fm
| and : Fm->Fm->Fm.

(*| and : Fm -> Fm -> Fm. *)

Fixpoint expansion (f:Var->Bool) (m:Fm) : Bool.
Proof.
induction m.
exact (f v).
Check not.
exact (negb IHm). (*?*)
exact (andb IHm1 IHm2).
Defined.
End logic.

Eval simpl in  (@expansion Bool (idmap) (jst Bool true)).
Eval simpl in  (@expansion Bool (idmap) (not Bool (jst Bool true))).
Eval simpl in  (@expansion Bool (idmap) 
(and Bool 
 (not Bool (jst Bool false))
 (not Bool (jst Bool false))
)
).


(*
Eval simpl in (forall n:nat, (n + 0)%nat = n). 
Eval simpl in (forall n:nat, (0 + n)%nat = n).
*)

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