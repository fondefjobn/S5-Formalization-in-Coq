From Coq Require Export Bool.

Module Propositional.

Definition neg (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition and (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition or (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition implies (b1:bool) (b2:bool) : bool :=
  or (neg b1) b2.

Definition ifonlyif (b1:bool) (b2:bool) : bool :=
  and (implies b1 b2) (implies b2 b1).

Definition var := nat.

Inductive Form : Type :=
  | Const (b:bool)
  | Var (n:nat)
  | Neg (f1:Form)
  | Conj (f1:Form) (f2:Form)
  | Disj (f1:Form) (f2:Form)
  | Impl (f1:Form) (f2:Form)
  | Bi (f1:Form) (f2:Form).

Fixpoint interpret (f:Form) (i : var -> bool) : bool :=
  match f with
  | Const c => c
  | Var x => i x
  | Neg f1 => neg (interpret f1 i)
  | Conj f1 f2 => and (interpret f1 i) (interpret f2 i)
  | Disj f1 f2 => or (interpret f1 i) (interpret f2 i)
  | Impl f1 f2 => implies (interpret f1 i) (interpret f2 i)
  | Bi f1 f2 => ifonlyif (interpret f1 i) (interpret f2 i)
  end.

Definition interpretP (f:Form) (i : var -> bool) : Prop := Is_true (interpret f i).

Inductive ax_pl : Form -> Prop :=
  | a_1 : forall x : Form, ax_pl (Impl x x)
  | a_2 : forall x y : Form, ax_pl (Impl x (Impl y x))
  | a_3 : forall x y z : Form, ax_pl (Impl (Impl x (Impl y z)) (Impl (Impl x y) (Impl x z)))
  | a_4 : forall x y : Form, ax_pl (Impl (Impl (Neg x) (Neg y)) (Impl y x))
  | mp : forall x y : Form, ax_pl (Impl x y) -> ax_pl x -> ax_pl y.
(*  | mp (x y z : Form) : ax_pl (Impl x y) -> ax_pl x -> ax_pl y. *)

Check ax_pl.
Check ax_pl_ind.
Check ax_pl_sind.

Lemma excluded_middle : forall P : bool,
  Is_true (or P (neg P)).
Proof.
  intros P. unfold Is_true, or, neg. destruct P; reflexivity.
Qed.

Lemma mp1 : forall x y : Prop, (x /\ (x -> y)) -> y.
Proof.
  intros x y H. destruct H. pose proof (H0 H) as H1. apply H1.
Qed.

Lemma mp2 : forall x y : Prop, (x -> y) -> x -> y.
Proof.
  intros x y H0 H1. pose proof (H0 H1) as H2. apply H2.
Qed.

Lemma mp3 : forall x y : Prop, (x /\ (x -> y)) -> y = (x -> y) -> x -> y.
Proof.
  intros x y H0 H1 H2. destruct H0. pose proof (H0 H). apply H3.
Qed.

Lemma ax_pl_sound (x : Form) :
  ax_pl x -> forall i, interpretP x i.
Proof.
  intros H. induction H.
  - intros i. unfold interpretP, Is_true. simpl. unfold implies, or, neg. destruct (interpret x i); reflexivity.
  - intros i. unfold interpretP, Is_true. simpl. unfold implies, or, neg. destruct (interpret x i).
    + destruct (interpret y i); reflexivity.
    + reflexivity.
  - intros i. unfold interpretP, Is_true. simpl. unfold implies, or, neg. destruct (interpret x i).
    + destruct (interpret y i).
      * destruct (interpret z i); reflexivity.
      * reflexivity.
    + reflexivity.
  - intros i. unfold interpretP, Is_true. simpl. unfold implies, or, neg. destruct (interpret x i).
    + destruct (interpret y i); reflexivity.
    + destruct (interpret y i); reflexivity.
  - intros i. unfold interpretP, Is_true. pose proof (IHax_pl1 i). pose proof (IHax_pl2 i). 
    unfold interpretP, Is_true in H1, H2. simpl in H1. unfold implies, or, neg in H1. destruct (interpret y i).
    + reflexivity.
    + destruct (interpret x i).
      * apply H1.
      * apply H2.
Qed.

(*
destruct H eqn:EE. destruct H0 eqn:EEE.
unfold interpretP, Is_true. unfold interpretP, Is_true in IHax_pl1, IHax_pl2. simpl in IHax_pl1.
     assert (H1: Is_true (or (interpret x i) (neg (interpret x i)))). apply excluded_middle. unfold Is_true, or, neg in H1. unfold implies in IHax_pl1.

destruct (interpret y i).
    + reflexivity.
*)

Declare Scope bool_scope.
Delimit Scope bool_scope with B.

Notation "~ x" := (neg x).
Notation "x && y" := (and x y).
Notation "x || y" := (or x y).
Notation "x → y" := (implies x y) (at level 50, left associativity) : bool_scope.
Notation "x ↔ y" := (ifonlyif x y) (at level 50, left associativity).

Example test_or1:  (or true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_or2:  (or false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_or3:  (or false true) = true.
Proof. simpl. reflexivity.  Qed.
Example test_or4:  (or true  true) = true.
Proof. simpl. reflexivity.  Qed.

Example test_implies1:  (implies true  true) = true.
Proof. simpl. reflexivity.  Qed.
Example test_implies2:  (implies true  false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_implies3:  (implies false  true) = true.
Proof. simpl. reflexivity.  Qed.
Example test_implies4:  (implies false false) = true.
Proof. simpl. reflexivity.  Qed.

Example test_notation:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

End Propositional.
