(* Chapter 5: Untyped Lambda Calculus *)
Require Import String.

Definition name := string.

Inductive term : Type :=
| tvar : name -> term
| tabs : name -> term -> term
| tapp : term -> term -> term
.

Fixpoint size t :=
  match t with
  | tvar _ => 1
  | tabs x t' => 1 + size t'
  | tapp t1 t2 => size t1 + size t2
  end.
