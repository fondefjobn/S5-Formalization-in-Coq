
From Coq Require Export Relations.

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
  unfold not. intros H0. apply H0. right. intros H1. apply H0. left. assumption.
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
  | mp G (x y : Form) : ax_s5 G (Impl x y) -> ax_s5 G x -> ax_s5 G y
  | nec (G : Form -> Prop) (x : Form) : ax_s5 emptyG x -> ax_s5 G (Box x).

Theorem ax_s5_soundness (G : Form -> Prop) (f : Form) :
  ax_s5 G f ->
  forall m w, (forall y, G y -> interpret y m w) -> interpret f m w.
Proof.
  intros H M. induction H; intros W1 HW.
  - specialize (HW x H). assumption.
  - intros X Y. assumption.
  - intros XYZ XY X. simpl in XYZ, XY. apply XYZ.
    + assumption.
    + apply XY, X.
  - simpl. intros XFYF Y. assert (H: interpret x M W1 \/ (interpret x M W1 -> False)).
    + apply excluded_middle.
    + destruct H.
      * assumption.
      * apply XFYF in Y. 
        -- destruct Y.
        -- assumption.  
  - intros XY X W2 R. simpl in XY, X. specialize (XY W2). specialize (X W2). apply XY.
    + assumption.
    + apply X, R.
  - intros X. simpl in X. specialize (X W1). apply X, reflex.
  - intros X W2 R1 W3 R2. apply X. assert (H: rel W1 W2 -> rel W2 W3 -> rel W1 W3).
    + apply trans.
    + apply H; assumption.
  - intros X W2 R NX. simpl. simpl in NX. specialize (NX W1). apply NX.
    + apply sym, R.
    + assumption.
  - simpl in IHax_s5_1. apply IHax_s5_1.
    + apply HW.
    + apply IHax_s5_2. apply HW.
  - intros W2 R. specialize (IHax_s5 W2). apply IHax_s5.
    intros y EG. unfold emptyG in EG. destruct EG.
Qed.

Definition subset (F G : Form -> Prop) : Prop :=
  forall x, F x -> G x.

Definition consistent (G : Form -> Prop) : Prop :=
  ~ (ax_s5 G F_).

Lemma deduce_subset (F G : Form -> Prop) :
  forall x, ax_s5 F x /\ subset F G -> ax_s5 G x.
Proof.
  intros f [Hf HG].
  induction Hf.
  - apply a_0, HG. assumption.
  - apply a_1.
  - apply a_2.
  - apply a_3.
  - apply a_k.
  - apply a_t.
  - apply a_4.
  - apply a_b.
  - eapply mp.
    + apply IHHf1. assumption.
    + apply IHHf2. assumption.
  - apply nec. assumption.
Qed.

Lemma consistent_subset (F G : Form -> Prop) :
  subset F G /\ consistent G -> consistent F.
Proof.
  intros [Hs Hcon] Hf. unfold consistent, not in Hcon. apply Hcon. 
  assert (D: ax_s5 F F_ /\ subset F G -> ax_s5 G F_). 
  - apply deduce_subset.
  - apply D. split; assumption. 
Qed.

Definition singleton (f : Form) : Form -> Prop :=
  fun x => x = f.

Definition add_singleton (G : Form -> Prop) (f : Form) : Form -> Prop :=
  fun x => x = f \/ G x.

Lemma deduction_theorem G p q :
  ax_s5 G (Impl p q) <-> ax_s5 (add_singleton G p) q.
Proof.
  split.
  - intros H1. eapply mp.
    + eapply deduce_subset. split. 
      * apply H1. 
      * unfold subset. intros r H2. unfold add_singleton. right. assumption.
    + apply a_0. unfold add_singleton. left. reflexivity.
  - intros H1. 
Admitted.

Definition decode : nat -> Form.
Admitted.

Definition encode : Form -> nat.
Admitted.

Lemma decode_encode n :
  encode (decode n) = n.
Admitted.


Definition is_consistent_choose (G : Form -> Prop) : bool. (*:=
  let H := consistent G \/ ~consistent G in
  match H with 
  | or_introl H => true
  | or_intror H => false
  end. *)
  Admitted.

Lemma is_consistent_choose_correct G :
  is_consistent_choose G = true <-> consistent G.
Proof.
  split.
  - intros H1 H2.
Admitted.

Lemma is_consistent_choose_correct_F G :
  is_consistent_choose G = false <-> ~consistent G.
Proof.
  split.
  - intros H1 H2. apply H2.
Admitted.

Definition insert (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  let f := decode n in
  match is_consistent_choose (add_singleton G f) with
  | true => add_singleton G f
  | false => add_singleton G (Neg f)
  end.

Lemma insert_correct G n :
  consistent G -> consistent (insert G n).
Proof.
  intros H0.
  unfold insert. case_eq (is_consistent_choose (add_singleton G (decode n))); intros H1.
  + apply is_consistent_choose_correct in H1. apply H1.
  + apply is_consistent_choose_correct_F in H1. unfold consistent, add_singleton, not.
    intros H2. apply H1. unfold consistent, add_singleton, not. intros H3. apply H0.
    destruct H3.
Admitted.

Fixpoint step (G : Form -> Prop) (n : nat) : (Form -> Prop) :=
  match n with
  | 0 => G
  | S n => insert (step G n) n
  end.

Lemma step_subset n : 
  forall G, subset G (insert G n).
Proof.
  intros G. unfold insert.
  case_eq (is_consistent_choose (add_singleton G (decode n))); intros H0;
  unfold subset; intros x H1; unfold add_singleton; right; assumption.
Qed.

Lemma step_correct G n :
  consistent G -> consistent (step G n).
Proof.
  induction n; intros H.
  - assumption.
  - simpl. apply insert_correct, IHn, H.
Qed.




Definition max_consistent_set (G : Form -> Prop) : Prop :=
  consistent G /\ forall x, G x \/ G (Neg x).

Definition big_union (F : nat -> (Form -> Prop)) (x : Form) : Prop :=
  exists i, F i x.

Definition max_consistent_compl (X : Form -> Prop) : Form -> Prop :=
  big_union (step X).

Lemma max_consistent_compl_maximal G f :
  consistent G -> max_consistent_compl G f \/ max_consistent_compl G (Neg f).
Proof.
  intros H0. unfold max_consistent_compl, big_union.
  (* assume f does not belong to G *)
  pose (n := encode f).
  case_eq (is_consistent_choose (add_singleton (step G n) f)); intros H1.
  - left. apply is_consistent_choose_correct in H1. exists n. induction n. unfold step.
Admitted.

Lemma max_consistent_compl_consistent G :
  consistent G -> consistent (max_consistent_compl G).
Proof.
  intros H0. unfold max_consistent_compl, big_union.
Admitted.

Lemma max_consistent_set_correct G :
  consistent G -> max_consistent_set G.


