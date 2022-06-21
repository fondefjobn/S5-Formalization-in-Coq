From Coq Require Export Bool.
From Coq Require Export Relations.
From Coq Require Export List.
From Coq Require Export Ensembles.
From Coq Require Export Relations.
From Coq Require Export Bool.

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

Record model : Type := Model {
  world :> Type;
  rel : world -> world -> Prop;
  val : world -> var -> Prop;
  eq : equiv world rel
  (* dec : forall x : Type, x -> True \/ x -> False *)
}.

Arguments val {_} w x.
Arguments rel {_} x y.

Fixpoint interpret (f : Form) (m : model) (w : m) : Prop :=
  match f with
  | F_ => False
  | Var x => val w x
  | Impl f1 f2 => interpret f1 m w -> interpret f2 m w
  | Box f => forall (y : m), rel w y -> interpret f m y
  end.

Lemma excluded_middle_double_negation (f : Form) (m : model) (w : m) :
  ~~(interpret f m w \/ not (interpret f m w)).
Proof.
  unfold not. intros H. apply H. right. intros X. destruct H. left. apply X.
Qed.

Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Lemma reflex (m : model) : 
  forall x : m, rel x x.
Proof.
  apply m.
Qed.

Lemma trans (m : model) : 
  forall x y z : m, rel x y -> rel y z -> rel x z.
Proof.
  apply m.
Qed.

Lemma sym (m : model) : 
  forall x y : m, rel x y -> rel y x.
Proof.
  apply m.
Qed.


Definition emptyG : Form -> Prop := fun (f : Form) => False.

Inductive ax_s5 : (Form -> Prop) -> Form -> Prop :=
  | a_0 G (x : Form) : (G x : Prop) -> ax_s5 G x
  | a_1 G (x y : Form) : ax_s5 G (Impl x (Impl y x))
  | a_2 G (x y z : Form) : ax_s5 G (Impl (Impl x (Impl y z)) (Impl (Impl x y) (Impl x z)))
  | a_3 G (x y : Form) : ax_s5 G (Impl (Impl (Neg x) (Neg y)) (Impl y x))
  | a_k G (x y : Form) : ax_s5 G (Impl (Box (Impl x y)) (Impl (Box x) (Box y)))
  | a_t G (x : Form) : ax_s5 G (Impl (Box x) x)
  | a_4 G (x : Form) : ax_s5 G (Impl (Box x) (Box (Box x)))
  | a_b G (x : Form) : ax_s5 G (Impl x (Box (Diamond x)))
  | mp G (x y z : Form) : ax_s5 G (Impl x y) -> ax_s5 G x -> ax_s5 G y
  | nec (x : Form) : ax_s5 emptyG x -> ax_s5 emptyG (Box x).

Theorem ax_s5_soundness (G : Form -> Prop) (f : Form) :
  ax_s5 G f ->
  forall m w, (forall y, G y -> interpret y m w) -> interpret f m w.
Proof.
  intros H M. induction H; intros W HW.
  - specialize (HW x H).
    apply HW.
  - intros X Y. apply X.
  - intros Z Y X. simpl in Z, Y. apply Z.
    + apply X.
    + apply Y, X.
  - simpl. intros A B. assert (H: interpret x M W \/ (interpret x M W -> False)).
    + apply excluded_middle.
    + destruct H.
      * apply H.
      * apply A in B. 
        -- destruct B.
        -- apply H.  
  - intros A B X R. simpl in A, B. specialize (A X). specialize (B X). apply A.
    + apply R.
    + apply B, R.
  - intros A. simpl in A. specialize (A W). apply A. apply reflex.
  - intros A X1 R1 X2 R2. apply A. assert (H: rel W X1 -> rel X1 X2 -> rel W X2).
    + apply trans.
    + apply H.
      * apply R1.
      * apply R2.
  - intros A X R B. simpl. simpl in B. specialize (B W). apply B.
    + apply sym, R.
    + apply A.
  - simpl in IHax_s5_1. apply IHax_s5_1.
    + apply HW.
    + apply IHax_s5_2. apply HW.
  -  intros X R. specialize (IHax_s5 X) as Y. apply Y.
     intros y Hy. unfold emptyG in Hy. destruct Hy.
Qed.

Definition subset (F G : Form -> Prop) : Prop :=
  forall x, F x -> G x.

Definition consistent (G : Form -> Prop) : Prop :=
  ~ (ax_s5 G F_).

Lemma deduce_subset (F G : Form -> Prop) :
  forall x, ax_s5 F x /\ subset F G -> ax_s5 G x.
Proof.
  intros f H. destruct H. unfold subset in H0. specialize (H0 f). apply a_0, H0.
Admitted.

Lemma consistent_subset (F G : Form -> Prop) :
  subset F G /\ consistent G -> consistent F.
Proof.
  intros H. destruct H. 
  intros X. unfold consistent, not in H0. apply H0. 
  assert (D: ax_s5 F F_ /\ subset F G -> ax_s5 G F_). 
  - apply deduce_subset.
  - apply D. split.
    + apply X.
    + apply H. 
Qed.

Definition max_consistent_set (G : Form -> Prop) : Prop :=
  consistent G /\ forall x, G x \/ G (Neg x).

Definition decode : nat -> Form.
Admitted.

Definition encode : Form -> nat.
Admitted.

Lemma decode_encode n :
  encode (decode n) = n.
Admitted.

Definition singletonG (f : Form) : Form -> Prop :=
  fun x => x = f.

Definition add_singleton (G : Form -> Prop) (f : Form) : Form -> Prop :=
  fun x => (x = f) \/ G x.

Definition is_consistent_choose (G : Form -> Prop) : bool.
Admitted.

Lemma is_consistent_choose_correct G :
  is_consistent_choose G = true <-> consistent G.
Proof.
Admitted.
(*  split. *)

Lemma is_consistent_choose_correct_F G :
  is_consistent_choose G = false <-> ~consistent G.
Proof.
Admitted.
(*  split. *)

Definition insert (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  let f := decode n in
  match is_consistent_choose (add_singleton G f) with
  | true => add_singleton G f
  | false => add_singleton G (Neg f)
  end.

Lemma insert_correct G n :
  consistent G -> consistent (insert G n).
Proof.
  intros H. pose (f := decode n). destruct n as [| n'] eqn:E.
  - unfold insert. case_eq (is_consistent_choose (add_singleton G (decode 0))); intros X.
    + apply is_consistent_choose_correct in X. apply X.
    + apply is_consistent_choose_correct_F in X.
Admitted.

Fixpoint step (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  match n with
  | 0 => G
  | S n => step (insert G n) n
  end.
(*    let f := decode n in
      match is_consistent_choose (add_singleton (step G n) f) with
      | true => add_singleton (step G n) f
      | false => add_singleton (step G n) (Neg f)
      end
  end. *)

Lemma step_subset G n : 
  subset (step G n) (step G (S n)).
Proof.
Admitted.

Lemma step_correct G n :
  consistent G -> consistent (step G n).
Proof.
  induction n.
  - intros H. apply H.
  - intros H0. pose (f := decode n). apply IHn in H0 as H1.
    assert (X: consistent G -> consistent (insert G n)).
    + apply insert_correct.
    + apply X in H0 as H2.
Admitted.





Definition bigUnion (F : nat -> (Form -> Prop)) (x : Form) : Prop := exists i, F i x.

Definition max_consistent_compl (X : Form -> Prop) : Form -> Prop := bigUnion (step X).

Lemma max_consistent_compl_maximal X f :
  max_consistent_compl X f \/ max_consistent_compl X (Neg f).
Proof.
  unfold max_consistent_compl, bigUnion.
  (* assume f does not belong to X *)
  pose (n := encode f). 
  case_eq (is_consistent_choose (add_singleton (step X n) f)); intros A.
  - left. exists n. destruct n as [| n'] eqn:E.
Admitted.

Lemma max_consistent_compl_consistent X :
  consistent (max_consistent_compl X).
Proof.
  unfold consistent, max_consistent_compl, bigUnion, not. intros H.
Admitted.

End Modal.



