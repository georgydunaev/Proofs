Require Import HoTT.

Section somelogic.
(*Context (n:nat). Definition Var := Fin n.*)
(*Context (n:nat). (pv:(Fin n) = Var).*)
Definition Var := nat. (*Fin n.*)
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

Definition is_zero_eq_to
(n:nat)
: Bool
:= match n with
   | 0     => true
   | n'.+1 => false
   end.

Definition code_n_helper
 (code_n_tail : forall (_ _ : nat), Bool) (n : nat)
: forall (m' : nat), Bool
:= match n with
   | 0     => fun _:nat => false
   | n'.+1 => code_n_tail n'
   end.
(*Fixpoint code_n (m :nat) {struct m} (n : nat) : Bool.*)

(*
Definition yumi
(m n : nat) (arab : nat -> nat -> Bool)
: Bool
:= match m with
   | 0     => is_zero_eq_to n
   | m'.+1 => code_n_helper arab n m'
   end.

Check yumi.*)

Definition yumi
(m : nat) (arab : nat -> nat -> Bool)
: nat -> Bool
:= match m with
   | 0     => is_zero_eq_to
   | m'.+1 => (code_n_helper arab) m'
   end.

(*code_n(m,n) = (m==n)?true:false *)
(*OLD*)

Fixpoint code_nat
(m n : nat) {struct m}
: Bool
:=match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => code_nat m' n'
  | _, _ => false
  end.
Definition code_n:=code_nat.
Reset code_n.

(*!!!!!*)

Definition code_n_KU (tail : nat->nat->Bool) (m n : nat) := 
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => tail m' n'
  | _, _ => false
  end.

Definition code_n
: nat->nat->Bool
:=fix code_n (m:nat) {struct m} := (code_n_KU code_n m).

(*
Definition code_nBAD
(g:nat) : nat->nat->Bool
:=(fix code_n (m : nat) {struct m} := fun (z:nat) =>
code_n_KU code_n m g).*)


Eval compute in code_n 0 0.
Eval compute in code_n 0 1.
Eval compute in code_n 1 1.

(*
match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => code_n m' n'
  | _, _ => false
  end.*)
  
Definition code_n'
: nat -> nat -> Bool
:= (fix code_n (m n : nat) {struct m} : Bool := (yumi m code_n) n).

Eval compute in code_n' 1 1.
Eval compute in code_n' 0 0.
Eval compute in code_n' 0 1.


(*Definition code_n
: nat -> nat -> Bool
:= (fix code_n (m : nat) {struct m} : nat -> Bool := yumi m code_n).
*)

(*Definition code_n
: nat -> nat -> Bool
:= (fix code_n (m n : nat) {struct m} : Bool :=
       match m with
       | 0 => is_zero_eq_to n
       | m'.+1 => code_n_helper m' n code_n
       end).*)

Check code_n.

Fixpoint code_n_eq (v : nat): (code_n v v) = true.
Proof.
(*unfold code_n.
unfold yumi.
unfold is_zero_eq_to.
unfold code_n_helper.
simpl.*)
destruct v.
unfold code_n.
unfold yumi.
unfold is_zero_eq_to.
reflexivity.
simpl.
exact (code_n_eq v).
Defined.

(*unfold code_n_helper.
simpl.
destruct v.
exact (code_n_eq v).*)
Reset code_n_eq.
Fixpoint code_n_eq (v : nat): (code_n v v) = true
:= match v with
   | 0 => idpath true
   | v0.+1 => code_n_eq v0
   end.

Definition check_help
(fm : Fm ) (m:Var) (qqq: Fm -> Var -> Bool) 
: Bool 
:=
   match fm with
   | jst v => code_n m v
   | nand m1 m2 => (qqq m1 m || qqq m2 m)%Bool
   end.

Definition check_help_eq
(qqq: Fm -> Var -> Bool) (m:Var)
:  check_help (jst m) m qqq = true
:= (code_n_eq m).

(* True if threre exist a varianle 'm' in formula 'fm'*)
Fixpoint check (fm : Fm ) (m:Var) : Bool := check_help fm m check.

Definition check_eq  (fm : Fm ) (m:Var) :
check m m  = true :=
code_n_eq m.
(*Proof.
unfold check.
unfold check_help.
exact (code_n_eq m).
Show Proof.
Defined.*)

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

Definition accumulate
(q:nat->nat)
: forall (m:nat), nat 
:=(fix acc (m0 : nat) {struct m0} : nat := 
   (match m0 with
    | 0 => q 0
    | m1.+1 => ((q (m1.+1)) + acc m1)%nat
    end)).

(* Number of placeholders in formula. Higher bound of amount of variables.*)
Fixpoint Count
(fm : Fm )
: nat
:=match fm with
  | jst _ => 1
  | nand m1 m2 => (Count m1 + Count m2)%nat
  end.



Section ss00.
Context (fm:Fm).
(*dme(n) = 1 if there exist a variable v in formula, such that num(v) = n
         = 0 otherwise. dme = "does [n-th variable] merely exist?" *)
Definition dme : nat->nat := fun n => repr (check fm (num n)).
Definition calcFIN (m:nat) : nat := accumulate dme m.
End ss00.

Fixpoint mneqsm
(m:nat)
:  code_n m m.+1 = false
:= match m with
   | 0 => 1
   | m0.+1 => mneqsm m0
   end.

Fixpoint mneqsm2
(m:nat)
:  code_n m.+1 m = false
:= match m with
   | 0 => 1
   | m0.+1 => mneqsm2 m0
   end.


(* ???
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
Admitted.*)

Definition QQ (m:nat) := (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | m1.+1 => ((if code_n m1 m then 1 else 0) + acc m1)%nat
   end).

Eval compute in (QQ 0 1). (*1 = QQ a b iff (a<b)*)

Fixpoint code_n_eq'
(v : nat)
: (code_n v v) = true
:= match v with
   | 0     => @idpath Bool true
   | v0.+1 => code_n_eq' v0
   end.

Definition f (m:nat) := (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | S m1 => ((if code_n m1 m then 1 else 0) + (acc m1))%nat
   end).

Definition dou (qf : nat -> nat -> nat) (m:nat) := qf m m.

Definition impprf  (p1: forall (m:nat), 0 = dou f m) (w:nat): (0 = dou f (S w)) := (p1 (S w)).

Definition b11_f : Bool -> (Unit + Unit) :=
 (fun b => match b with
           | false => inl tt
           | true  => inr tt
           end).

Definition b11_invf : (Unit + Unit) -> Bool :=
 (fun uu => match uu with
            | inl _ => false
            | inr _ => true
            end).

Definition b11_f_sect : Sect b11_f b11_invf :=
 (fun x : Bool => if x as b return (b11_invf (b11_f b) = b) 
                  then idpath true 
                  else idpath false).

Definition b11_invf_sect : Sect b11_invf b11_f :=
 (fun x : Unit + Unit =>
 match x as s return (b11_f (b11_invf s) = s) with
 | inl u =>
     match u return (b11_f (b11_invf (inl u)) = inl u) with
     | tt => idpath (inl tt)
     end
 | inr u =>
     match u return (b11_f (b11_invf (inr u)) = inr u) with
     | tt => idpath (inr tt)
     end
 end).

Definition b11_adj (x : Bool) :
 b11_invf_sect (b11_f x) = ap b11_f (b11_f_sect x) := 
 match x as b return (b11_invf_sect (b11_f b) = ap b11_f (b11_f_sect b)) with
 | true  => @idpath (inr tt = inr tt) (@idpath (Unit+Unit) (inr tt))
 | false => @idpath (inl tt = inl tt) (@idpath (Unit+Unit) (inl tt))
 end.
 
Definition b11_f_equi : IsEquiv b11_f :=
 @BuildIsEquiv Bool (Unit+Unit) b11_f b11_invf b11_invf_sect b11_f_sect b11_adj.

Definition b11_iso : Equiv Bool (Unit + Unit) :=
 @BuildEquiv Bool (Unit+Unit) b11_f b11_f_equi.

Definition smuzi : (Empty <~> (inl tt = inr tt)) :=
 @equiv_path_sum Unit Unit (inl tt) (inr tt).

Definition eqv : (false = true) -> (inl tt = inr tt) :=
 (fun p : false = true => ap b11_f p).

Definition agag : (Empty -> (inl tt = inr tt)) :=
 @equiv_fun Empty (inl tt = inr tt) smuzi.
 
Definition gaga : ((inl tt = inr tt) -> Empty) :=
 @equiv_inv Empty (inl tt = inr tt) agag (equiv_isequiv smuzi).

Definition impos : (false = true) -> Empty := 
 (fun p:(false = true) =>  (gaga (eqv p))).

Definition ururu {n}: (code_n n.+1 0 = true) -> Empty := impos.

Definition smth (n:nat) : (code_n n 0 = true -> n = 0) := 
 match n as n0 return (code_n n0 0 = true -> n0 = 0) with
       | 0 => fun _ : code_n 0 0 = true => idpath
       | n0.+1 =>
           fun H : code_n n0.+1 0 = true =>
           match (impos H) return (n0.+1 = 0) with end
       end.
Reset smth.

(*Definition smth (n : nat) (H : code_n n 0 = true) : (n = 0) := 
 match n as n0 return (n0 = 0) with
       | 0 => idpath
       | n0.+1 => match (impos H) return (n0.+1 = 0) with end
       end.*)

Definition smth (n:nat) : (code_n n 0 = true -> n = 0) := 
 match n as n0 return (code_n n0 0 = true -> n0 = 0) with
       | 0 => fun _ : code_n 0 0 = true => idpath
       | n0.+1 =>
           fun H : code_n n0.+1 0 = true =>
           match (impos H) return (n0.+1 = 0) with end
       end.

(*Everything may be proved 
1)Using 'Definition'
2)with only one 'match'

Every closed term is a separate theorem.
There exist a smallest proof of theorem.
Every theorem must have meaningful name.
*)

Definition path_n_helper (n m0 : nat)
(hlp : forall (n m : nat), ((code_n n m) = true ) -> (n = m) ) :=
match n as n0 return (code_n n0 m0.+1 = true -> n0 = m0.+1) with
       | 0 =>
           fun y : code_n 0 m0.+1 = true =>
           match impos y return (0 = m0.+1) with end
       | n0.+1 => fun y : code_n n0.+1 m0.+1 = true => ap S (hlp n0 m0 y)
       end.

Definition path_n : forall (n m : nat), ((code_n n m) = true ) -> (n = m) :=
(fix path_n (n m : nat) {struct m} :=
   match m as n0 return (code_n n n0 = true -> n = n0) with
   | 0 => smth n
   | m0.+1 => path_n_helper n m0 path_n
   end).
(*
What is analogue of "firstorder"?
We need an algorithm for automatic solving of first-order formulas.
*)

Definition testw: (true = true) <-> (0 = 0) :=
(fun _ : true = true =>  idpath 0, fun _ : 0 = 0 => idpath true).

Definition exfalso
(m : nat) (natpath : m.+1 = 0)
: False
:= (transport (fun n=>match n with |0 => Unit |_=>False end) natpath^ tt).

Definition invS
(n:nat)
: nat
:= match n with 0 => 0 | S n => n end.

Definition invaps
(m n:nat) (p:S m = S n)
: (m = n)
:= (ap invS p).

Definition uselessthing
(m0 : nat) (y : false = true)
: (m0.+1 = 0)
:= match impos y return (m0.+1 = 0) with end.

Definition ut2
(m0 : nat) (y : m0.+1 = 0)
: false = true
:=match exfalso m0 y return (false = true) with end.

Definition niop
(m0 : nat)
: (false = true -> m0.+1 = 0) * (m0.+1 = 0 -> false = true)
:= (uselessthing m0, ut2 m0).
Check niop.

(*Definition niop 
(m0 : nat) 
:= (fun y : false = true =>
         match impos y return (m0.+1 = 0) with end,
        fun y : m0.+1 = 0 =>
        match exfalso m0 y return (false = true) with end).*)

Definition muss
(m0 n1 : nat)
(IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0)
: code_n m0 n1 = true -> m0.+1 = n1.+1
:= fun qe : code_n m0 n1 = true => ap S (fst (IHm n1) qe).

Definition muss2
(m0 n1 : nat)
(IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0)
(qe : m0.+1 = n1.+1)
: code_n m0 n1 = true
:= snd (IHm n1) (invaps m0 n1 qe).

Definition gonada
(m0 n1 : nat) (IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0)
: (code_n m0 n1 = true) <-> (m0.+1 = n1.+1)
:= (muss m0 n1 IHm, muss2 m0 n1 IHm ).

Definition stalin
(m0 : nat) (IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0) (n0 : nat)
: (code_n m0.+1 n0 = true) <-> (m0.+1 = n0)
:=  match n0 as n1 return (code_n m0.+1 n1 = true <-> m0.+1 = n1) with
    | 0 => niop (m0)
    | n1.+1 => gonada m0 n1 IHm
    end.

(* What is "destruct f" when f is a function? *)
Definition agad
(n : nat)
: code_n 0 n = true <-> 0 = n
:=  match n with
    | 0 => (fun _ : true = true => idpath, fun _ : 0 = 0 => idpath)
    | n1.+1 =>
        (fun y : false = true => match (impos y) with end,
        fun y : 0 = n1.+1 => match (exfalso n1 y^) with end)
    end.

Check agad.

Definition gulag := (fun m0 : nat => forall n0 : nat, code_n m0 n0 = true <-> m0 = n0).

Definition code_n_eqk (m n : nat ) : (code_n m n) = true <-> m = n
:= nat_rect gulag agad stalin m n.

Lemma old_code_n_eqk m n :
  (code_n m n) = true <-> m = n.
Proof.
revert n; induction m; destruct n.
simpl.
try easy.
unfold code_n.
refine (_,_).
intro y.
destruct (impos y).
intro y.
destruct (exfalso n (y^)).
unfold code_n.
refine (_,_).
intro y.
destruct (impos y).
intro y.
destruct (exfalso m (y)).
simpl.
refine (_,_).
intro qe.
exact (ap S ((fst (IHm n)) qe)).
simpl.
intro qe.
Eval compute in invaps m n qe.
exact (snd (IHm n) (invaps m n qe)).
Show Proof.
Defined.

(*Eval compute in ap invS qe.
exact (ap invS ((snd (IHm n)) qe)).
unfold code_n.
simpl.
Show Proof.
contradiction.
exfalso.
try easy.
reflexivity.
 try easy; firstorder.
Admitted.*)

(* generalize what we want to prove *)
Lemma gte m n :
  m >= n -> f m n = 0.
  revert m; induction n; destruct m.
  try easy.
  intro q. 
  reflexivity.
  simpl.
  intro emp.
  destruct emp.
  intro yu.
  Check code_n_eq.
  unfold f.
  Print code_n.
  unfold code_n.
  
  destruct f.
  reflexivity.
  simpl.
  destruct yu.
  destruct (code_n n (S m)).
  try easy.
  
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


