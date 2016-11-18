Require Import HoTT.

Section somelogic.
(*Context (n:nat). Definition Var := Fin n.*)
(*Context (n:nat). (pv:(Fin n) = Var).*)
Definition Var := nat. (**) (*Fin n.*)
Definition decpavar := decidable_paths_nat.
Notation num := idmap.
Notation mun := idmap.
(*Reset Var.
Reset decpavar.
Context {Var:Type}.
Context {decpavar:DecidablePaths Var}.
Context {num:nat->Var}.
Context {mun:Var->nat}.*)


Inductive Fm :=
 | jst  : Var -> Fm
 | nand : Fm -> Fm -> Fm.

Coercion jst : Var >-> Fm.

(*code_n(m,n) = (m==n)?true:false *)
Definition code_n := (fix code_n (m n : nat) {struct m} : Bool :=
       match m with
       | 0 =>
           match n with
           | 0 => true
           | n'.+1 =>false 
           end
       | m'.+1 =>
           match n with
           | 0 => false
           | n'.+1 => code_n m' n'
           end
       end).

Fixpoint code_n_eq (v : nat): (code_n v v) = true 
:= match v as n return (code_n n n = true) with
   | 0 => 1
   | v0.+1 => code_n_eq v0
   end.
(*.
Proof.
destruct v.
reflexivity.
exact (eqq v).
Show Proof.
Defined.*)

Definition check_help (fm : Fm ) (m:Var) (qqq: Fm -> Var -> Bool) : Bool :=
   match fm with
   | jst v => code_n m v
   | nand m1 m2 => (qqq m1 m || qqq m2 m)%Bool
   end.

Fixpoint check_help_eq  (qqq: Fm -> Var -> Bool) (m:Var) :
check_help (jst m) m qqq = true
:= (code_n_eq m).
(*Proof.
unfold check_help.
exact (eqq m).
Show Proof.
Defined.*)

(*       match (decpavar v m) with
       | inl _ => true
       | inr _ => false
       end*)


(* True if threre exist a varianle 'm' in formula 'fm'*)
Fixpoint check (fm : Fm ) (m:Var) : Bool := check_help fm m check.

Fixpoint check_eq  (fm : Fm ) (m:Var) :
check m m  = true.
Proof.
unfold check.
unfold check_help.
exact (code_n_eq m).
Defined.

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
Reset accumulate.

Definition accumulate (q:nat->nat) : forall (m:nat), nat := 
(fix acc (m0 : nat) {struct m0} : nat := 
 (match m0 with
   | 0 => q 0
   | m1.+1 => ((q (m1.+1)) + acc m1)%nat
  end)).

(*(
fix acc (m0 : nat) {struct m0} : nat :=
 (match m with
   | 0 => q 0
   | m0.+1 => ((q (m0.+1)) + acc m0)%nat
   end)) m.

forall (m:nat),
(fix accumulate (q : nat -> nat) (m0 : nat) {struct m0} : nat :=
   match m0 with
   | 0 => q 0
   | m1.+1 => (q m1.+1 + accumulate q m1)%nat
   end) (fun n : nat => if code_n n m.+1 then 1 else 0) m = 0
*)

(* Number of placeholders in formula. Higher bound of amount of variables.*)
Fixpoint Count (fm : Fm ) : nat :=
  match fm with
  | jst _ => 1
  | nand m1 m2 => (Count m1 + Count m2)%nat
  end.
(*Proof.
destruct fm as [v|m1 m2].
exact 1.
exact ((Count m1)+(Count m2))%nat.
Show Proof.
Defined.*)


Section ss00.
Context (fm:Fm).
(*dme(n) = 1 if there exist a variable v in formula, such that num(v) = n
         = 0 otherwise. dme = "does [n-th variable] merely exist?" *)
Definition dme : nat->nat := fun n => repr (check fm (num n)).
Definition calcFIN (m:nat) : nat := accumulate dme m.
End ss00.

Fixpoint mneqsm (m:nat) : code_n m m.+1 = false
:=match m as n return (code_n n n.+1 = false) with
   | 0 => 1
   | m0.+1 => mneqsm m0
   end.
(*Proof.
destruct m.
reflexivity.
exact (mneqsm m).
Show Proof.
Defined.*)

Fixpoint thmhz (m:nat) : calcFIN (jst (m.+1)) m.+1 = calcFIN (jst m) m.
Proof.
unfold calcFIN.
unfold dme.
unfold check.
unfold check_help.
unfold accumulate.
unfold repr.

destruct m.
reflexivity.
simpl.
(*exact (thmhz m).*)
Admitted.

Definition QQ (m:nat) := (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | m1.+1 => ((if code_n m1 m then 1 else 0) + acc m1)%nat
   end).

Eval compute in (QQ 0 1). (*1 = QQ a b iff (a<b)*)

    Fixpoint code_n_eq' (v : nat): (code_n v v) = true 
    := match v as n return (code_n n n = true) with
       | 0 => @idpath Bool true
       | v0.+1 => code_n_eq v0
       end.


Definition f (m:nat) := (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | S m1 => ((if code_n m1 m then 1 else 0) + (acc m1))%nat
   end).
   
Check f.

Definition dou (qf : nat -> nat -> nat) (m:nat) := qf m m.

Definition impprf  (p1: forall (m:nat), 0 = dou f m) : forall (m:nat), (0 = dou f (S m)).
intro w.
exact (p1 (S w)).
Defined.

(*Definition hjkjk (m m0 : nat)
:= (fix acc  : nat :=
   match m0 with
   | 0 => 0
   | m1.+1 => ((if code_n m1 m then 1 else 0) + acc m1)%nat
   end) m.*)
   
   
Check @HoTT.Types.Sum.equiv_path_sum.



Check (@equiv_path_sum Unit Unit (inl tt) (inr tt)).

Check  BuildEquiv.

Definition b11_f : Bool -> (Unit + Unit) := (fun b => match b with false=>inl tt | true => inr tt end).

Definition b11_invf : (Unit + Unit) -> Bool := (fun uu => match uu with inl _=>false | inr _ => true end).

Definition b11_f_sect : Sect b11_f b11_invf := (fun x : Bool => if x as b return (b11_invf (b11_f b) = b) then idpath true else idpath false).

Definition b11_invf_sect : Sect b11_invf b11_f := 
(fun x : Unit + Unit =>
 match x as s return (b11_f (b11_invf s) = s) with
 | inl u =>
     match u as u0 return (b11_f (b11_invf (inl u0)) = inl u0) with
     | tt => idpath (inl tt)
     end
 | inr u =>
     match u as u0 return (b11_f (b11_invf (inr u0)) = inr u0) with
     | tt => idpath (inr tt)
     end
 end).

Definition b11_adj (x : Bool) : 
b11_invf_sect (b11_f x) = ap b11_f (b11_f_sect x) 
:= (if x as b return (b11_invf_sect (b11_f b) = ap b11_f (b11_f_sect b))
          then @idpath (inr tt = inr tt) (@idpath (Unit+Unit) (inr tt))
          else @idpath (inl tt = inl tt) (@idpath (Unit+Unit) (inl tt))).

(*
Eval compute in b11_invf_sect (b11_f true).
Eval compute in b11_f true.
(*Type:
b11_invf_sect (b11_f true) = ap b11_f (b11_f_sect true)
*)
Eval compute in ap b11_f (b11_f_sect true).
Check b11_invf_sect (b11_f true).
Definition b11_adj (x : Bool) : 
b11_invf_sect (b11_f x) = ap b11_f (b11_f_sect x).
pose (qqq:=(b11_f (b11_invf (b11_f true)) = b11_f true)).
simpl in qqq.
Check @idpath.

simple refine (if x as b return (b11_invf_sect (b11_f b) = ap b11_f (b11_f_sect b))
          then @idpath (b11_f (b11_invf (b11_f true)) = b11_f true) _
          else @idpath (inl tt = inl tt) (@idpath (Unit+Unit) (inl tt))).
          
          (@inr  tt)
          
exact (if x as b return (b11_invf_sect (b11_f b) = ap b11_f (b11_f_sect b))
          then idpath _
          else idpath (*inl tt*) _ ).
Print All.
Show Proof.
Check b11_adj.*)

Definition b11_f_equi : IsEquiv b11_f :=
(@BuildIsEquiv Bool (Unit+Unit) b11_f b11_invf b11_invf_sect b11_f_sect b11_adj).


Definition b11_f_equi : IsEquiv b11_f.
simple refine (@BuildIsEquiv _ _  b11_f b11_invf b11_invf_sect b11_f_sect _).
intro x.
destruct x.
reflexivity.
reflexivity.
Show Proof.

Check Sect.

Theorem bool_iso_1plus1 : Bool <~> Unit + Unit.
Proof.
simple refine (@BuildEquiv Bool (Unit+Unit) _ _ ).
exact bool_to_1plus1.
(*fun b => match b with false=>inl tt | true => inr tt end.*)
simple refine (@BuildIsEquiv _ _ _ _ _ _ _).
exact (fun uu => match uu with inl _=>false | inr _ => true end).
intro x.
destruct x.
destruct u; reflexivity.
destruct u; reflexivity.
intro x.
destruct x.
reflexivity.
reflexivity.
simpl.
intro x.
destruct x.
reflexivity.
reflexivity.
Show Proof.
Defined.

Print Equiv.
Check Equiv.


compute.

pose 


compute.

reflexivity.

simpl.

Check  BuildIsEquiv.
Check @equiv_inv.


Theorem impos : (false = true) -> Empty.


Lemma code_n_eqk m n :
  (code_n m n) = true <-> m = n.
revert n; induction m; destruct n.
simpl.
try easy.
simpl.


contradiction.
exfalso.
try easy.

reflexivity.

 try easy; firstorder.

Admitted.

(* generalize what we want to prove *)
Lemma gte m n :
  m >= n -> f m n = 0.
  
  revert m; induction n; destruct m; try easy; firstorder.
  simpl. destruct (code_n n (S m)) eqn:E.
  - apply code_n_eq in E; omega.
  - assert (m >= n) by omega. rewrite IHn; auto.
Admitted.

Lemma impprf4 (m:nat): f m m = 0.
Proof.
apply gte.
auto.
apply leq_refl.
Defined.  
  
Proof.
  revert n; induction m; destruct n.
   try easy.
   firstorder.
easy.

Fixpoint impprf2 (m:nat) : (0 = dou f m).
unfold f.
unfold dou.
destruct m.
reflexivity.
destruct m.
reflexivity.

exact ((impprf impprf2) m).
Defined.

Fixpoint impprf (m:nat) (p1: 0 = dou f m) :( 0 = dou f (S m)).
destruct m.
exact (impprf (0) p1). (*reflexivity.*)
exact (impprf (S m) p1).
Defined.

Fixpoint impprf (m:nat) : (dou f m = 0) = dou f (S m).
unfold f.
unfold dou.
compute.

destruct f.
exact 0.
exact 0.
exact (impprf m).
exact (impprf m).
Defined.
unfold dou.


Fixpoint impprf (m:nat): f m m = f (S m) (S m).

Fixpoint impprf (m:nat):(fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | m1.+1 => ((if code_n m1 m then 1 else 0) + acc m1)%nat
   end) m = 0.
   
destruct m; reflexivity.

revert m.
apply happly.
refine 
Check happly.
destruct m.
reflexivity.


Fixpoint calcFIN_eq (m:nat) : calcFIN (jst m) m = 1.
Proof.
(**)
unfold calcFIN.
unfold dme.
unfold check.
unfold check_help.
unfold accumulate.
unfold repr. (**)
destruct m.
compute.
reflexivity.
simpl.
pose (code_n_eq m)^ as vv.
destruct vv. 
simpl.
refine (ap S _). (*OK*)



destruct m.
reflexivity.

pose ((if code_n m m then 1 else 0) = 1) as ww.
change (if code_n m m then 1 else 0) with 1%nat.

refine ((thmhz m) @ _).
exact (calcFIN_eq m).
Defined.



Definition maximal_help (f:Fm->nat) (fm : Fm )  : nat :=
   match fm with
   | jst v => mun v
   | nand m1 m2 => max (f m1) (f m2)
   end.

Fixpoint maximal (fm : Fm ) : nat := maximal_help (maximal) fm.

Definition calcINF (fm : Fm) : nat := calcFIN fm (maximal fm).
End somelogic.

Eval compute in calcFIN (jst 1) 3.

Context (v:Var).
Eval compute in maximal (jst v).

Eval compute in decpavar 0 0.
Eval compute in decpavar 0 1.
Eval compute in decpavar 1 1.

Eval simpl in code_nat v v.
Eval compute in code_nat v v.

(*Theorem q:Bool.       
set (g := (fix code_n (m n : nat) {struct m} : Bool :=
       match m with
       | 0 =>
           match n with
           | 0 => true
           | n'.+1 =>false 
           end
       | m'.+1 =>
           match n with
           | 0 => false
           | n'.+1 => code_n m' n'
           end
       end) v v).
cbv beta in g.
cbv delta in g.
cbv iota in g.
cbv zeta in g.*)


(*delta G.
cbv delta g.
Eval rewrite -> true in g.
Print Strategies.
(*Extraction g.*)
Eval vm_compute in g.
Eval compute in code_nat 1 1.
Eval compute in dhprop_hprop (code_nat v v).
Eval compute in (decpavar v v).
Eval compute in check (jst v) v. (*=1*)
Eval compute in dme (jst v) v. (*=1*)
Eval compute in (calcFIN v 1).
*)

Fixpoint one (v:Var) : 1 = (calcFIN v v).
destruct v.
reflexivity.
Admitted.
(*exact (one v0).
Defined.

unfold calcFIN.
unfold accumulate.
unfold dme.

set (ku := (calcINF v)).
compute in ku.
simpl in ku.
simpl.
reflexivity.
identity.*)

(*Let's construct the function Bool^n -> Bool*)



Fixpoint cons (fm:Fm) : ((Fin (calcINF fm) -> Bool) -> Bool).
Proof.
destruct fm as [v|fm1 fm2].
set (ku := (calcINF v)).
simpl in ku. *)




Check @calcINF.
Eval simpl in maximal (nand (jst 1) (jst 2)).
Eval compute in maximal (*nat idmap*) (nand (jst 3) (nand (jst 3) (jst 2))).
Eval compute in calcFIN (jst 1) 3.
Eval compute in calcFIN (*nat decidable_paths_nat idmap*) (nand (jst 3) (nand (jst 3) (jst 2))) 3.
Eval compute in @calcINF (*nat decidable_paths_nat idmap idmap*) (nand (jst 3) (nand (jst 3) (jst 2))).



Definition decidable_paths_nat : DecidablePaths nat.

 exact (fun n m => decidable_equiv _ (@path_nat n m) _).
Show Proof.


