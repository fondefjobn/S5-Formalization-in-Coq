
From S5 Require Export model.

Inductive Form : Type :=
  | F_
  | Var (v : var)
  | Impl (f1 : Form) (f2 : Form)
  | Box (f : Form).

Definition Neg (f : Form) := Impl f F_.

Definition T_ := Neg F_.

Definition Disj (f1 f2 : Form) := Impl (Neg f1) f2.

Definition Conj (f1 f2 : Form) := Neg (Disj (Neg f1) (Neg f2)).

Definition BiImpl (f1 f2 : Form) := Conj (Impl f1 f2) (Impl f2 f1).

Definition Diamond (f : Form) := Neg (Box (Neg f)).

Fixpoint interpret (f : Form) (m : model) (w : m) : Prop :=
  match f with
  | F_ => False
  | Var x => val w x
  | Impl f1 f2 => interpret f1 m w -> interpret f2 m w
  | Box f => forall (y : m), rel w y -> interpret f m y
  end.
