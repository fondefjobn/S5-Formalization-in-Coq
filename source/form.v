
From S5 Require Export model.

Inductive form : Type :=
  | F_
  | Var (v : var)
  | Impl (f1 : form) (f2 : form)
  | Box (f : form).

Definition Neg (f : form) := Impl f F_.

Definition T_ := Neg F_.

Definition Disj (f1 f2 : form) := Impl (Neg f1) f2.

Definition Conj (f1 f2 : form) := Neg (Disj (Neg f1) (Neg f2)).

Definition BiImpl (f1 f2 : form) := Conj (Impl f1 f2) (Impl f2 f1).

Definition Diamond (f : form) := Neg (Box (Neg f)).
