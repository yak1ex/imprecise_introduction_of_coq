Require Import classical.

Definition LIN := forall P Q: Prop, (P -> Q) \/ (Q -> P).

Theorem LEM_implies_LIN : LEM -> LIN.
Proof.
    unfold LEM, LIN, not.
    intros.
    destruct (H P) as [HL|HR].
    - right. intros. assumption.
    - left. intros. destruct (HR H0).
Qed.

Require Import Coq.Sets.Ensembles.

Section MySet.

Variable U : Type.
Variable A B C : (Ensemble U).