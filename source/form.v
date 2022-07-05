
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
