Module Propositional.

Inductive bool : Type :=
  | true
  | false.

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
  or (and b1 b2) (and (neg b1) (neg b1)).

Declare Scope bool_scope.
Delimit Scope bool_scope with B.

Notation "~ x" := (neg x).
Notation "x && y" := (and x y).
Notation "x || y" := (or x y).
Notation "x → y" := (implies x y) (at level 50, left associativity) : bool_scope.
Notation "x ↔ y" := (ifonlyif x y) (at level 50, left associativity).

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

Fixpoint interpretP (f:Form) (i : var -> bool) : Prop :=
  match f with
  | Const true => True
  | Const false => False
  | Var x => if i x then True else False
  | Neg f1 => interpretP f1 i -> False
  | Conj f1 f2 => if and (interpret f1 i) (interpret f2 i) then True else False
  | Disj f1 f2 => if or (interpret f1 i) (interpret f2 i) then True else False
  | Impl f1 f2 => if implies (interpret f1 i) (interpret f2 i) then True else False
  | Bi f1 f2 => if ifonlyif (interpret f1 i) (interpret f2 i) then True else False
  end.

(** You can match two expressions at once by putting a comma between them. *)
(*  | a_3 : forall (x:Form) (y:Form) (z:Form), f (Impl x (Impl y z)) -> f (Impl (Impl x y) (Impl x z)) *)

Inductive f : Form -> Prop :=
  | a_1 : forall x : Form, f (Impl x x)
  | a_2 : forall x y : Form, f (Impl x (Impl y x))
  | a_3 : forall x y z : Form, f (Impl (Impl x (Impl y z)) (Impl (Impl x y) (Impl x z)))
  | a_4 : forall x y : Form, f (Impl (Impl (Neg x) (Neg y)) (Impl y x)).

Check f.
Check f_ind.
Check f_sind.

Lemma f_correct (x : Form) :
  f x -> forall i, interpretP x i = True.
Proof.
  intros Hf. induction Hf.
  - intros i. simpl.
    destruct (interpret x i). simpl. reflexivity. simpl. reflexivity. reflexivity.
  - intros i. simpl.
    destruct (interpret x i). destruct (interpret y i). simpl. reflexivity. simpl. reflexivity.
    destruct (interpret y i). simpl. reflexivity. simpl. reflexivity.
  - intros i. simpl.
    destruct (interpret x i). destruct (interpret y i). destruct (interpret z i). simpl. reflexivity. simpl. reflexivity.
    destruct (interpret z i). simpl. reflexivity. simpl. reflexivity.  
    destruct (interpret y i). destruct (interpret z i). simpl. reflexivity. simpl. reflexivity. 
    destruct (interpret z i). simpl. reflexivity. simpl. reflexivity.
  - intros i. simpl.
    destruct (interpret x i). destruct (interpret y i). simpl. reflexivity. simpl. reflexivity.
    destruct (interpret y i). simpl. reflexivity. simpl. reflexivity.
Qed.

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
