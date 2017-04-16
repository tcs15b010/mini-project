(* Proving Predicate Logic *)

Section PredicateLogic.
Variable D : Set.
Variable R : D → D → Prop.
Theorem refl_if : (∀ x y : D, R x y → R y x ) →
(∀ x y z : D, R x y → R y z → R x z) →
(∀ x : D, (∃ y : D, R x y) → R x x ).
intros Rsym.
intros Rtrans.
intros x.
intros xR_.
destruct xR as [y xRy].
apply Rtrans with (y := y).
assumption.
apply Rsym.
assumption.
Qed.
Variables f g : D → D.
Variable d : D.

Theorem example pred theorem : (∀ x : D, ∃ y : D, f x = g y) ->(∃ c : D, ∀ x : D, f x = c) ->
(∃ y : D, ∀ x : D, f x = g y).
intros H1 H2.
destruct H2 as [c H2'].
cut (∃ y : D, c = g y).
intros H3.
destruct H3 as [yc H3'].
rewrite ← H3'.
assumption.
rewrite ← H2' with (x := d).
apply H1.
Qed.
End PredicateLogic.




