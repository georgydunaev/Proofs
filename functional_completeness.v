(*Require Import HoTT.*)
(* -*- mode: coq; mode: visual-line -*-  *)
Local Set Typeclasses Strict Resolution.
Local Unset Elimination Schemes.
Global Set Keyed Unification.
Global Unset Refine Instance Mode.
Global Unset Strict Universe Declaration.
Global Unset Universe Minimization ToSet.

Notation idmap := (fun x => x).

Inductive Empty : Prop :=.

Scheme Empty_ind := Induction for Empty Sort Type.
Scheme Empty_rec := Minimality for Empty Sort Type.
Definition Empty_rect := Empty_ind.


Inductive Unit : Prop:= | tt:Unit.
Inductive Bool : Set := | true:Bool |false:Bool.
Fixpoint Fin (n : nat) : Set
  := match n with
       | 0 => Empty
       | S n => Fin n + Unit
     end.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.
Arguments paths_ind [A] a P f y p.
Scheme paths_rec := Minimality for paths Sort Type.
Arguments paths_rec [A] a P f y p.

(* See comment above about the tactic [induction]. *)
Definition paths_rect := paths_ind.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.


Section somelogic.
(*Context (n:nat). Definition Var := Fin n.*)
(*Context (n:nat). (pv:(Fin n) = Var).*)
Definition Var := nat. (*Fin n.*)
(*Definition decpavar := decidable_paths_nat.!!*)

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
 | nand : Fm -> (Fm -> Fm).

Coercion jst : Var >-> Fm.

(* ====== *)
Definition is_zero_eq_to
(n:nat)
: Bool
:= match n with
   | 0     => true
   | S n' => false
   end.

(*push_front the b to f:nat->B*)
Definition prepend
(B:Type) (tailm0 : nat -> B) (b : B) (n : nat) 
:= match n with
   | 0     => b
   | S n0 => tailm0 n0
   end.

(*(2->A)->Q  <-> A->(A->Q) *)
Definition thm (A:Type)(Q:Type):(A->(A->Q)) -> ((Bool -> A) -> Q).
Proof.
intros f w.
exact (f (w false) (w true) ).
Show Proof.
Defined.

Reset thm.
Definition thm (A:Type)(Q:Type):(A->(A->Q)) -> (Bool->A)->Q
:=(fun (f : A -> A -> Q) (w : Bool -> A) => f (w false) (w true)).

Definition mht (A:Type)(Q:Type):((Bool->A)->Q) -> (A->(A->Q)).
Proof.
intros h y0 y1.
refine (h _).
intro b.
destruct b.
exact y0.
exact y1.
Show Proof.
Defined.
Reset mht.

Definition mht (A:Type)(Q:Type):((Bool->A)->Q) -> (A->(A->Q)) :=
(fun (h : (Bool -> A) -> Q) (y0 y1 : A) =>
 h (fun b : Bool => if b then y0 else y1)).

Fixpoint power (X Y : Type) (n:nat): Type.
Proof.
destruct n.
exact Y.
exact (X->(power X Y n)).
Show Proof.
Defined.

Reset power.

Definition powern (X Y : Type) : nat -> Type
:= (fix power (n : nat) {struct n} : Type :=
   match n with
   | 0 => Y
   | S n0 => X -> power n0
   end).


Fixpoint thm2 (A:Type)(Q:Type)(n:nat):(powern A Q n) -> ((Fin n->A)->Q).
Proof.
intros f w.
destruct n.
unfold powern in f.
exact f.
unfold powern in f.
unfold Fin in w.
refine (thm2 A Q n (f (w (inr tt))) (fun x => w (inl x)) ).
Show Proof.
Defined.
Reset thm2.

Definition thm2 (A:Type)(Q:Type) : forall (n:nat), (powern A Q n) -> ((Fin n->A)->Q) :=
(fix thm2 (n : nat) (f : powern A Q n) (w : Fin n -> A) {struct n} : Q :=
   match n as n0 return (powern A Q n0 -> (Fin n0 -> A) -> Q) with
   | 0 => fun (f0 : powern A Q 0) (_ : Fin 0 -> A) => f0
   | S n0 =>
       fun (f0 : powern A Q (S n0)) (w0 : Fin (S n0) -> A) =>
       thm2 n0 (f0 (w0 (inr tt))) (fun x : Fin n0 => w0 (inl x))
   end f w).



Fixpoint mht2 (A:Type)(Q:Type)(n:nat):((Fin n->A)->Q) -> (powern A Q n).
Proof.
intros h.
destruct n.
exact (h (Empty_ind (fun _ => A))).
simpl.
intro a.
refine (mht2 A Q n _).
intro g.
refine (h _).
intro w.
destruct w.
exact (g f).
exact a.
Show Proof.
Defined.
Reset mht2.


Definition mht2 (A Q : Type) :=
(fix mht2 (n : nat) (h : (Fin n -> A) -> Q) {struct n} :
 powern A Q n :=
   match n as n0 return (((Fin n0 -> A) -> Q) -> powern A Q n0) with
   | 0 => fun h0 : (Fin 0 -> A) -> Q => h0 (Empty_rect (fun _ : Empty => A))
   | (S n0) =>
       fun (h0 : (Fin (S n0) -> A) -> Q) (a : A) =>
       mht2 n0
         (fun g : Fin n0 -> A =>
          h0 (fun w : Fin (S n0) => match w with
                                   | inl f => g f
                                   | inr _ => a
                                   end))
   end h).

(*need some examples*)

Check powern nat Bool 2.
Eval compute in powern nat Bool 2.


(*Eval compute in thm2 n nat nat*)

(*noname function*)
(*bottom prepend of falses to 2D tabular*)
Definition bottom_false_prep (tail : nat -> (nat -> Bool)) (m0 : nat)
:= prepend Bool (tail m0) false.

(*"addcornerbooltruefalse tail" is 2d prepend of falses to left and bottom of domain of
[un?]curried version of tail with single "true" in the corner (0,0)
Definition addcornerbooltruefalse (tail : nat -> (nat -> Bool)) (x : nat): nat -> Bool :=
 match x with
 | 0 => is_zero_eq_to
 | x0.+1 => bottom_false_prep tail x0
 end.
*)

Definition valatzero (B:Type) (others atzero : B)
(n:nat)
: B
:= match n with
   | 0     => atzero
   | S n' => others
   end.

Definition addcorner (B:Type) (others diags : B) (tail : nat -> (nat -> B))
(x : nat): nat -> B :=
 match x with
 | 0 => valatzero B others diags
 | S x0 => prepend B (tail x0) others
 end.


(* Calculate function "code_n" that is stable under action of "addcorner":
"code_n" defines an 2d half-infinty matrix as a stable under "addcorner"
action. It's diagonal matrix with "true" on diagonal and "false" otherwise.
Value on all diagonals are the same and determined by border. *)

(* aim:
Definition diagonal (A B:Type) (u d:B)
: A -> A -> B.*)

Definition diagonal (B:Type) (others diags : B)
: nat -> (nat -> B)
:= fix yy (m:nat) {struct m} := (addcorner B others diags yy m).

Definition code_n := diagonal Bool false true .

Check thm2 nat Bool 2 code_n.

Definition test01 := mht2 nat Bool 2 (thm2 nat Bool 2 code_n).

Eval compute in test01. (*error!*)
Eval compute in test01 1 1.

Eval compute in mht2 nat Bool 2 (thm2 nat Bool 2 code_n).

(*
Definition code_n
: nat -> nat -> Bool
:= fix code_n (m:nat) {struct m} := (addcornerbooltruefalse code_n m).
*)

Eval compute in code_n 0 0.
Eval compute in code_n 0 1.
(*Eval compute in code_n 34759 34759. MAX *)

(*It is usefull theorem, because not all terms are equally good with "fix".
It may also be useful with S1.*)
Definition code_n_eq_helper
(hlp : forall (v1 : nat), code_n v1 v1 = true) (v : nat)
: (code_n v v = true)
:= 
  match v as v2 return (code_n v2 v2 = true) with
  | 0 => idpath true
  | S v0 => hlp v0
  end.

(*Counterexample.
Definition code_n_eq_helper2
(hlp : forall (v1 : nat), code_n v1 v1 = true) (v : nat)
: (code_n v v = true)
:= hlp v.
*)

Definition code_n_eq
: forall v : nat, code_n v v = true 
:= 
fix code_n_eq (v : nat) : code_n v v = true 
:= code_n_eq_helper code_n_eq v.

Definition orb (a b : Bool) : Bool :=
match a with
| true => true
| false => b
end.

Definition check_help
(fm : Fm ) (m:Var) (qqq: Fm -> Var -> Bool) 
: Bool 
:=
   match fm with
   | jst v => code_n m v
   | nand m1 m2 => (orb (qqq m1 m) (qqq m2 m))
   end.

Definition check_help_eq
(qqq: Fm -> Var -> Bool) (m:Var)
:  check_help (jst m) m qqq = true
:= (code_n_eq m).

(* 'true' if there exist a variable 'm' in formula 'fm'*)
Definition check
: forall (fm : Fm ) (m:Var), Bool
:= fix checkfix (fm : Fm ) (m:Var) : Bool
:= check_help fm m checkfix.

(*there exist variable 'h' in trivial formula 'jst h'*)
Definition check_eq
(fm : Fm ) (m:Var)
: check m m  = true
:= code_n_eq m.

Definition repr
(b:Bool)
: nat
:= match b with
   | true  => 1
   | false => 0
   end.

Definition composition (A B C:Type) (f:A->B) (g:B->C) (a:A) := g (f a).

Definition add : nat -> nat -> nat :=
fix add (m : nat) : nat -> nat :=
match m with
| 0 => idmap
| S m' => composition _ _ _ S (add m')
end.

(* ok
Definition add : nat -> nat -> nat :=
fix add (m n : nat) : nat :=
match m with
| 0 => n
| S m' => S (add m' n)
end.
*)


(*Calculate ... *)
Definition accumulate_helper
(hlp: forall (q:nat->nat) (m:nat), nat) (q:nat->nat) (m:nat)
: nat
:= match m with
   | 0 => q 0
   | S m0 => (add (q (S m0)) (hlp q m0))%nat
   end.

Definition accumulate
: forall (q:nat->nat) (m:nat), nat
:= (fix acc (q:nat->nat) (m:nat) : nat
:= accumulate_helper acc q m).

(* Number of placeholders in formula. Higher bound of amount of variables.*)
Fixpoint Count
(fm : Fm )
: nat
:=match fm with
  | jst _ => 1
  | nand m1 m2 => (add (Count m1) (Count m2))%nat
  end.

Section ss00.
Context (fm:Fm).
(*dme(n) = 1 if there exist a variable v in formula 'fm', such that num(v) = n
         = 0 otherwise. dme = "does [n-th variable] merely exist?" *)
Definition dme : nat->nat := fun n => repr (check fm (num n)).
Definition calcFIN (m:nat) : nat := accumulate dme m.
End ss00.

Fixpoint mneqsm
(m:nat)
: code_n m (S m) = false
:= match m with
   | 0 => idpath
   | S m0 => mneqsm m0
   end.

Fixpoint mneqsm2
(m:nat)
: code_n (S m) m = false
:= match m with
   | 0 => idpath
   | S m0 => mneqsm2 m0
   end.

(*(1 = QQ a b) iff (a<b)*)
Definition QQ (m:nat) := (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | S m1 => (add (if code_n m1 m then 1 else 0) (acc m1))%nat
   end).

Eval compute in (QQ 0 1).

Fixpoint code_n_eq'
(v : nat)
: (code_n v v) = true
:= match v with
   | 0     => @idpath Bool true
   | S v0 => code_n_eq' v0
   end.

Definition f (m:nat) := (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | S m1 => (add (if code_n m1 m then 1 else 0) (acc m1))%nat
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

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
  
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

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

Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Definition b11_iso : Equiv Bool (Unit + Unit) :=
 @BuildEquiv Bool (Unit+Unit) b11_f b11_f_equi.

Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => Empty
                 end)
: z = z'.
  destruct z, z'.
  all:try apply ap, pq.
  all:elim pq.
Defined.

Definition path_sum_inv {A B : Type} {z z' : A + B}
           (pq : z = z')
: match z, z' with
    | inl z0, inl z'0 => z0 = z'0
    | inr z0, inr z'0 => z0 = z'0
    | _, _ => Empty
  end
  := match pq with
       | idpath => match z with
                | inl _ => idpath
                | inr _ => idpath
              end
     end.

Definition inl_ne_inr {A B : Type} (a : A) (b : B)
: (inl a = inr b) -> Empty
:= path_sum_inv.

Definition inr_ne_inl {A B : Type} (b : B) (a : A)
: (inr b = inl a) -> Empty
:= path_sum_inv.

(** This version produces only paths between closed terms, as opposed to paths between arbitrary inhabitants of sum types. *)
Definition path_sum_inl {A : Type} (B : Type) {x x' : A}
: inl x = inl x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.

Definition path_sum_inr (A : Type) {B : Type} {x x' : B}
: inr x = inr x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.

(** This lets us identify the path space of a sum type, up to equivalence. *)

Definition eisretr_path_sum {A B} {z z' : A + B}
: Sect (@path_sum_inv _ _ z z') (path_sum z z')
  := fun p => match p as p in (_ = z') return
                    path_sum z z' (path_sum_inv p) = p
              with
              | idpath => match z as z return
                             path_sum z z (path_sum_inv idpath) = idpath
                       with
                         | inl _ => idpath
                         | inr _ => idpath
                       end
              end.

Definition eissect_path_sum {A B} {z z' : A + B}
: Sect (path_sum z z') (@path_sum_inv _ _ z z').
Proof.
  intro p.
  destruct z, z', p; exact idpath.
Defined.

Global Instance isequiv_path_sum {A B : Type} {z z' : A + B}
: IsEquiv (path_sum z z') | 0.
Proof.
  refine (BuildIsEquiv _ _
                       (path_sum z z')
                       (@path_sum_inv _ _ z z')
                       (@eisretr_path_sum A B z z')
                       (@eissect_path_sum A B z z')
                       _).
  destruct z, z';
    intros [];
    exact idpath.
Defined.

Definition equiv_path_sum {A B : Type} (z z' : A + B)
  := BuildEquiv _ _ _ (@isequiv_path_sum A B z z').


Definition smuzi : (Equiv (Empty) (inl tt = inr tt)) :=
 @equiv_path_sum Unit Unit (inl tt) (inr tt).

Definition eqv : (false = true) -> (inl tt = inr tt) :=
 (fun p : false = true => ap b11_f p).

Definition agag : (Empty -> (inl tt = inr tt)) :=
 @equiv_fun Empty (inl tt = inr tt) smuzi.
 
Definition gaga : ((inl tt = inr tt) -> Empty) := inl_ne_inr tt tt.
(* @equiv_inv Empty (inl tt = inr tt) agag (equiv_isequiv smuzi).*)

Definition impos : (false = true) -> Empty := 
 (fun p:(false = true) =>  (gaga (eqv p))).

Definition ururu {n}: (code_n (S n) 0 = true) -> Empty := impos.

Definition smth (n:nat) : (code_n n 0 = true -> n = 0) := 
 match n as n0 return (code_n n0 0 = true -> n0 = 0) with
       | 0 => fun _ : code_n 0 0 = true => idpath
       | S n0 =>
           fun H : code_n (S n0) 0 = true =>
           match (impos H) return ((S n0) = 0) with end
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
       | S n0 =>
           fun H : code_n (S n0) 0 = true =>
           match (impos H) return ((S n0) = 0) with end
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
match n as n0 return (code_n n0 (S m0) = true -> n0 = (S m0)) with
       | 0 =>
           fun y : code_n 0 (S m0) = true =>
           match impos y return (0 = (S m0)) with end
       | S n0 => fun y : code_n (S n0) (S m0) = true => ap S (hlp n0 m0 y)
       end.

Definition path_n : forall (n m : nat), ((code_n n m) = true ) -> (n = m) :=
(fix path_n (n m : nat) {struct m} :=
   match m as n0 return (code_n n n0 = true -> n = n0) with
   | 0 => smth n
   | S m0 => path_n_helper n m0 path_n
   end).
(*
What is analogue of "firstorder"?
We need an algorithm for automatic solving of first-order formulas.
*)

Definition testw: (true = true) <-> (0 = 0) :=
(fun _ : true = true =>  idpath 0, fun _ : 0 = 0 => idpath true).

Definition invpath {A:Type} {x y: A} (p: x = y) : (y = x) 
:= match p with
   | idpath => idpath
   end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.
  
Definition exfalso
(m : nat) (natpath : (S m) = 0)
: False
:= (transport (fun n=>match n with |0 => Unit |_=>False end) (invpath natpath) tt).

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
: ((S m0) = 0)
:= match impos y return ((S m0) = 0) with end.

Definition ut2
(m0 : nat) (y : (S m0) = 0)
: false = true
:=match exfalso m0 y return (false = true) with end.

Definition niop
(m0 : nat)
: (false = true -> (S m0) = 0) * ((S m0) = 0 -> false = true)
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
: code_n m0 n1 = true -> (S m0) = (S n1)
:= fun qe : code_n m0 n1 = true => ap S (fst (IHm n1) qe).

Definition muss2
(m0 n1 : nat)
(IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0)
(qe : (S m0) = (S n1))
: code_n m0 n1 = true
:= snd (IHm n1) (invaps m0 n1 qe).

Definition gnd
(m0 n1 : nat) (IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0)
: (code_n m0 n1 = true) <-> ((S m0) = (S n1))
:= (muss m0 n1 IHm, muss2 m0 n1 IHm ).

Definition alin
(m0 : nat) (IHm : forall n0 : nat, code_n m0 n0 = true <-> m0 = n0) (n0 : nat)
: (code_n (S m0) n0 = true) <-> ((S m0) = n0)
:=  match n0 as n1 return (code_n (S m0) n1 = true <-> (S m0) = n1) with
    | 0 => niop (m0)
    | (S n1) => gnd m0 n1 IHm
    end.

(* What is "destruct f" when f is a function? *)
Definition agad
(n : nat)
: code_n 0 n = true <-> 0 = n
:=  match n with
    | 0 => (fun _ : true = true => idpath, fun _ : 0 = 0 => idpath)
    | (S n1) =>
        (fun y : false = true => match (impos y) with end,
        fun y : 0 = (S n1) => match (exfalso n1 (invpath y)) with end)
    end.

Check agad.

Definition gula := (fun m0 : nat => forall n0 : nat, code_n m0 n0 = true <-> m0 = n0).

Definition code_n_eqk (m n : nat ) : (code_n m n) = true <-> m = n
:= nat_rect gula agad alin m n.

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
destruct (exfalso n ((invpath y))).
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

Inductive compare :=
| less : compare
| equal : compare
| greater : compare.

Fixpoint compa (a b : nat) : compare :=
match a, b with
| 0,0 => equal
| S x, 0 => greater
| 0, S y => less
| S x, S y => compa x y
end.

(*a>=b*)
Definition gre (a b : nat) : Prop :=
match compa a b with
| equal => Unit
| greater => Unit
| less => Empty
end.


(*Fixpoint gre a b :=
match a, b with
| 0,0 => true
| S x, S y => gre x y
| S x, 0 => true
| 0, S y => false
end.*)

(* generalize what we want to prove *)
Lemma gte m n :
  (gre m n) -> f m n = 0.
Proof.
  revert m; induction n; destruct m.
Admitted.
(*  try easy.
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
Admitted.*)
(*  reflexivity.
  simpl.
  destruct yu.
  destruct (code_n n (S m)).
  try easy.
  
  revert m; induction n; destruct m; try easy; firstorder.
  simpl. destruct (code_n n (S m)) eqn:E.
  - apply code_n_eq in E; omega.
  - assert (m >= n) by omega. rewrite IHn; auto.
Admitted.*)

Lemma impprf4 (m:nat): f m m = 0.
Proof.
apply gte.
auto.
(*apply leq_refl.
Defined.*)
Admitted.

(*Proof.
  revert n; induction m; destruct n.
   try easy.
   firstorder.
easy.*)

Fixpoint impprf2 (m:nat) : (0 = dou f m).
Proof.
unfold f.
unfold dou.
destruct m.
reflexivity.
destruct m.
reflexivity.
(*exact ((impprf impprf2) m).
Defined.*)
Admitted.

(*Fixpoint impprf (m:nat) (p1: 0 = dou f m) :( 0 = dou f (S m)).
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

Fixpoint impprf (m:nat): f m m = f (S m) (S m).*)

Fixpoint impprfWUT (m:nat)
: (fix acc (m0 : nat) : nat :=
   match m0 with
   | 0 => 0
   | S m1 => (add (if code_n m1 m then 1 else 0) (acc m1))%nat
   end) m = 0.
Proof.
Admitted.

(*
destruct m; reflexivity.

revert m.
apply happly.
refine 
Check happly.
destruct m.
reflexivity.*)

Fixpoint thmhz (m:nat) : calcFIN (jst (S m)) (S m) = calcFIN (jst m) m.
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
pose (invpath (code_n_eq m)) as vv.
destruct vv. 
simpl.
refine (ap S _). (*OK*)



destruct m.
reflexivity.

pose ((if code_n m m then 1 else 0) = 1) as ww.
change (if code_n m m then 1 else 0) with 1%nat.

(*refine ((thmhz m) @ _).
exact (calcFIN_eq m).
Defined.*)
Admitted.

Fixpoint max (a b: nat) : nat :=
match a, b with
| 0, 0 => 0
| S a, 0 => S a
| 0, S b => S b
| S a, S b => S (max a b)
end.

Definition maximal_help (f:Fm->nat) (fm : Fm )
: nat
:= match fm with
   | jst v => mun v
   | nand m1 m2 => max (f m1) (f m2)
   end.

Fixpoint maximal (fm : Fm )
: nat
:= maximal_help (maximal) fm.

Definition calcINF (fm : Fm)
: nat
:= calcFIN fm (maximal fm).

End somelogic.

Eval compute in calcFIN (jst 1) 3.

Context (v:Var).
Eval compute in maximal (jst v).

(*
Eval compute in decpavar 0 0.
Eval compute in decpavar 0 1.
Eval compute in decpavar 1 1.

Eval simpl in code_nat v v.
Eval compute in code_nat v v.
*)


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
simpl in ku.




Check @calcINF.
Eval simpl in maximal (nand (jst 1) (jst 2)).
Eval compute in maximal (*nat idmap*) (nand (jst 3) (nand (jst 3) (jst 2))).
Eval compute in calcFIN (jst 1) 3.
Eval compute in calcFIN (*nat decidable_paths_nat idmap*) (nand (jst 3) (nand (jst 3) (jst 2))) 3.
Eval compute in @calcINF (*nat decidable_paths_nat idmap idmap*) (nand (jst 3) (nand (jst 3) (jst 2))).


(*
Definition decidable_paths_nat : DecidablePaths nat.

 exact (fun n m => decidable_equiv _ (@path_nat n m) _).
Show Proof.
*)

