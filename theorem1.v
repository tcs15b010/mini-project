(* First theorem proved in coq *)

Section PropositionalLogic.
Variables P Q R : Prop.
Theorem hilbert axiom S : (P → Q → R) → (P → Q) → P → R.

Proof:
P : Prop
Q : Prop
R : Prop
(P → Q → R) → (P → Q) → P → R
