Require Import Ensembles.
Require Import Relations_1.
Require Import podefs.
Require Import podefs_1.
Require Import ps.

Section Lemmas_on_partial_orders.
   Variable U : Type.
   Variable B : Ensemble U.
   Variable D : PO U.
   
     Theorem Rel_of_reflexive : forall x : U, Rel_of U D x x.
   elim D; simpl in |- *; auto with v62.
   intros C R H' H'0; elim H'0; auto 10 with v62.
   Qed.
   Hint Resolve Rel_of_reflexive.

   Theorem Rel_of_antisymmetric : Antisymmetric U (Rel_of U D).
   elim D; simpl in |- *; auto with v62.
   intros C R H' H'0; elim H'0; auto 10 with v62.
   Qed.
   Hint Resolve Rel_of_antisymmetric.
   
    Theorem Rel_of_transitive : Transitive U (Rel_of U D).
   elim D; simpl in |- *; auto with v62.
   intros C R H' H'0; elim H'0; auto 10 with v62.
   Qed.
   Hint Resolve Rel_of_transitive.
   End Lemmas_on_partial_orders.
