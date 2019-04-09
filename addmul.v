Require Extraction.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.
Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
               end.

Definition three := S (S (S O)).
Definition nine := S (S (S (S (S (S (S (S (S O)))))))).

Fixpoint is_power_of_three n :=
match n with
| O => true
| S (S (S p)) => is_power_of_three p
| _ => false
end.

Example tmp: is_power_of_three nine = true.
Proof.
  simpl. trivial.
Qed.

Definition tst := binopDenote Times three three.

Extraction Language CPP.
Recursive Extraction is_power_of_three.
