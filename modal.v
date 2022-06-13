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

Lemma excluded_middle_double_negation (f : Form) (m : model) (w : m) :
  ~~(interpret f m w \/ not (interpret f m w)).
Proof.
  unfold not. intros H. apply H. right. intros X. destruct H. left. apply X.
Qed.

Lemma excluded_middle (f : Form) (m : model) (w : m) :
  (interpret f m w \/ not (interpret f m w)).
Proof.
Admitted.

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

Theorem ax_s5_soundness (f : Form) :
  ax_s5 f -> forall m w, interpret f m w.
Proof.
  intros H M. induction H.
  - intros W X Y. apply X.
  - intros W Z Y X. simpl in Z, Y. apply Z.
    + apply X.
    + apply Y, X.
  - simpl. intros W A B. assert (H: interpret x M W \/ (interpret x M W -> False)).
    + apply excluded_middle.
    + destruct H.
      * apply H.
      * apply A in B. 
        -- destruct B.
        -- apply H.  
  - intros W A B X R. simpl in A, B. specialize (A X). specialize (B X). apply A.
    + apply R.
    + apply B, R.
  - intros W A. simpl in A. specialize (A W). apply A. apply reflex.
  - intros W A X1 R1 X2 R2. apply A. assert (H: rel W X1 -> rel X1 X2 -> rel W X2).
    + apply trans.
    + apply H.
      * apply R1.
      * apply R2.
  - intros W A X R B. simpl. simpl in B. specialize (B W). apply B.
    + apply sym, R.
    + apply A.
  - intros W. simpl in IHax_s5_1. apply IHax_s5_1. apply IHax_s5_2.
  - intros W X R. specialize (IHax_s5 X) as Y. apply Y.
Qed.



(*
f : X -> bool
x : X
g y = if x = y then true else f y
*)

Definition bigUnion (X : nat -> (Form -> Prop)) (x : Form) : Prop := exists i, X i x.

End Modal.



