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

Definition tst := binopDenote Times three three.

Extraction Language CPP.
Recursive Extraction tst.
