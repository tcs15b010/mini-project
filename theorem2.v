(* Proving Propositional Logic in Coq*)

Section PropositionalLogic.
Variables P Q R : Prop.
Theorem or_logic : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R).
intros H.
destruct H as [H1 | H2 ].
split.
destruct H1 as [HP HQ].
exact HP.
destruct H1 as [HP HQ].
left.
exact HQ.
destruct H2 as [HP HR].
auto.
Qed.
Theorem noncontradiction : not (P ∧ not P).
unfold not.
intros H.
destruct H as [H1 H2 ].
auto.
Qed.

End PropositionalLogic.
