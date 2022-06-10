From Coq Require Export Bool.
From Coq Require Export Relations.
From Coq Require Export List.
From Coq Require Export Ensembles.
From Coq Require Export Relations.

Module Modal.

Definition var := nat.

Inductive Form : Type :=
  | F_
  | Var (v : var)
  | Impl (f1 : Form) (f2 : Form)
  | Box (f : Form).

Definition Neg (f : Form) := Impl f F_.

Definition Disj (f1 f2 : Form) := Impl (Neg f1) f2.

Definition Conj (f1 f2 : Form) := Neg (Disj (Neg f1) (Neg f2)).

Definition Diamond (f : Form) := Neg (Box (Neg f)).

Search Ensemble.

Section Kripke_Frame.

Variable X : Type.

Structure model := {
  world : Ensemble X;
  rel : relation X;
  val: X -> Ensemble X;
  eq : equiv X rel
}.

Record model1 : Type := Model {
  state :> Type;
  trans : state -> state -> Prop;
  label : state -> var -> Prop;
  eq1 : forall x y z : state, trans x x /\ ((trans x y /\ trans y z) -> trans x z) /\ trans x y -> trans y x;
  (* dec : forall x : Type, x -> True \/ x -> False *)
}.

(*  @Verification of Dynamic Bisimulation Theorems in Coq
    @ Fervari, Trucco, Ziliani

From Mtac2 Require Export Mtac2.
From Coq.Sets Require Export Constructive_sets.
From Coq.Relations Require Export Relations.
From Coq.Logic Require Export Classical.
From Coq.Lists Require Export List.
From RCLIC Require Export utilities.
From mathcomp Require Export ssreflect ssrnat ssrbool eqtype.

Definition valuation (W: Set) : Type := set (prop * W).

Structure model := {
  m_states :> Set;
  m_rel : relation m_states;
  m_val: valuation m_states
}.

*)

(* @Doczkal & Smolka, 2011 (for K)*)
Record model2 := Model2 {
  state2 :> Type;
  trans2 : state2 -> state2 -> Prop;
  label2 : var -> (state2 -> Prop);
  BOX : (state2 -> Prop) -> (state2 -> Prop);
  boxE : forall p w, BOX p w <-> forall v, trans2 w v -> p v;
  DIA : (state2 -> Prop) -> (state2 -> Prop);
  diaE : forall p w, DIA p w <-> exists v, trans2 w v /\ p v;
}.


End Kripke_Frame.

Type world.

(*
f : X -> bool
x : X
g y = if x = y then true else f y
*)


Definition implies (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => true
  end.

Definition neg (b:bool) : bool := implies b false.

Definition and (b1:bool) (b2:bool) : bool := neg (implies b1 (neg b2)).

Definition or (b1:bool) (b2:bool) : bool := implies (neg b1) b2.

Definition ifonlyif (b1:bool) (b2:bool) : bool :=
  and (implies b1 b2) (implies b2 b1).

Search relation.

Fixpoint interpret (f : Form) (m : model1) (w : state m) (i : model1 -> state m -> var -> bool) : bool :=
  match f with
  | F_ => false
  | Var x => i m w x
  | Impl f1 f2 => implies (interpret f1 m w i) (interpret f2 m w i)
  | Box f => true
(*  | Box f => forall x y : state m, trans m x y -> interpretP f m w i *)
  end.

Fixpoint interpretP (f : Form) (m : model1) (w : state m) (i : model1 -> state m -> var -> bool) : Prop :=
  match f with
  | F_ => Is_true (interpret f m w i)
  | Var x => Is_true (interpret f m w i)
  | Impl f1 f2 => Is_true (interpret f m w i)
  | Box f => forall x y : state m, trans m x y -> interpretP f m w i 
  end.

Inductive ax_s5 : Form -> Prop :=
  | a_1 (x y : Form) : ax_s5 (Impl x (Impl y x))
  | a_2 (x y z : Form) : ax_s5 (Impl (Impl x (Impl y z)) (Impl (Impl x y) (Impl x z)))
  | a_3 (x y : Form) : ax_s5 (Impl (Impl (Neg x) (Neg y)) (Impl y x))
  | a_k (x y : Form) : ax_s5 (Impl (Box (Impl x y)) (Impl (Box x) (Box y)))
  | a_t (x : Form) : ax_s5 (Impl (Box x) x)
  | a_4 (x : Form) : ax_s5 (Impl (Box x) (Box (Box x)))
  | a_b (x : Form) : ax_s5 (Impl x (Box (Diamond x)))
  | mp (x y z : Form) : ax_s5 (Impl x y) -> ax_s5 x -> ax_s5 y
  | nec (x : Form) : ax_s5 x -> ax_s5 (Box x).

Lemma ax_s5_sound (x : Form) :
  ax_s5 x -> forall m w i, interpretP x m w i.
Proof.
  intros H. induction H.
Admitted.
(* Qed. *)

End Modal.



