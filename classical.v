(* 論理記号の表示 *)
Require Import Unicode.Utf8.

(* 古典命題論理の命題 *)
Definition LEM := forall P, P \/ ~P. (* 排中律 Law of Excluded Middle *)
Print LEM.
Definition DNE := forall P, ~~P -> P. (* 二重否定除去 Double Negation Elimination *)
(* P,Q が Type として推論されるのでProp(Proposition)として型を明示 *)
Definition PEIRCE := forall P Q: Prop, ((P -> Q) -> P) -> P. (* Peirceの法則 *)
Definition IMPNOTOR := forall P Q: Prop, (P -> Q) -> ~P \/ Q. (* 含意＝否定と論理和 *)
Definition DMGNAND := forall P Q, ~(~P /\ ~Q) -> P \/ Q. (* ド・モルガンの法則 *)

(* 行->列で"*"は排中律経由した証明 *)
(*           LEM    DNE    PEIRCE  IMPNOTOR  DMGNAND
  LEM         -      o       o        o         o
  DNE         o      -       o        o         o
  PEIRCE      o      o       -        o         o
  IMPNOTOR    o      *       *        -         *
  DMGNAND     o      o       o        o         -
*)

(* unfold, intros, destruct disj, assumption, apply, exfalso *)
Theorem LEM_implies_DNE : LEM -> DNE.
Proof.
    unfold LEM, DNE. unfold not. (* ~P は P -> False の略記 *)
    intros H P1 H1.
    (*
    assert (HPNP: P1 \/ (P1 -> False)).
    apply H.
    destruct HPNP as [HL|HR]. assumption.
    exfalso. apply H1. assumption.
    *)
    destruct (H P1) as [HL|HR].
    - (* HL: P1 *) assumption. (* apply HL. *)
    - (* HR: P1 -> False *) exfalso. apply H1, HR.
      (* destruct (H1 HR). とか *) (* apply (H1 HR). も可 *)
Qed.
(* 証明＝プログラム *)
Print LEM_implies_DNE.

Theorem LEM_implies_PEIRCE : LEM -> PEIRCE.
Proof.
    unfold LEM, PEIRCE, not. intros.
    destruct (H P) as [HL|HR].
    - assumption.
    - apply H0. intros. destruct (HR H1).
Qed.

(* left/right *)
Theorem LEM_implies_IMPNOTOR : LEM -> IMPNOTOR.
Proof.
    unfold LEM, IMPNOTOR. unfold not. intros.
    destruct (H P) as [HL|HR].
    - (* HL: P *) right. apply H0, HL.
    - (* HR: P -> False *) left. assumption.
Qed.

(* split *)
Theorem LEM_implies_DMGNAND : LEM -> DMGNAND.
Proof.
    unfold LEM, DMGNAND, not. intros.
    destruct (H P) as [HPL|HPR].
    - (* HPL: P *) left. assumption.
    - (* HPR: P -> False *) destruct (H Q) as [HQL|HQR].
        + (* HQL: Q *) right. assumption.
        + (* HQR: Q -> False *) exfalso. apply H0.
          (* split. assumption. assumption. *)
          split; assumption.
Qed.

Theorem DNE_implies_LEM : DNE -> LEM.
Proof.
    unfold DNE, LEM, not. intros.
    apply H. intros.
    apply H0. left. apply H. intros.
    apply H0. right. assumption.
Qed.

(* apply *)
Theorem DNE_implies_PEIRCE : DNE -> PEIRCE.
Proof.
    unfold DNE, PEIRCE, not.
    intros H P1 Q1 H1.
    apply (H P1). intros NP1.
    apply NP1. apply H1. intros HP1.
    exfalso. apply NP1, HP1.
Qed.

Theorem DNE_implies_IMPNOTOR : DNE -> IMPNOTOR.
Proof.
    unfold DNE, IMPNOTOR, not. intros.
    apply H. intros.
    apply H1. right. apply H0, H. intros.
    apply H1. left. apply H2.
Qed.

Theorem DNE_implies_DMGNAND : DNE -> DMGNAND.
Proof.
    unfold DNE, DMGNAND, not. intros.
    apply H. intros.
    apply H0. split.
    - intros. apply H1. left. assumption.
    - intros. apply H1. right. assumption.
Qed.

(* apply with *)
Theorem PEIRCE_implies_LEM : PEIRCE -> LEM.
Proof.
    unfold PEIRCE, LEM, not. intros.
    (* apply H with (Q := False). *)
    apply H with False. intros.
    right. intros. apply H0. left. assumption.
Qed.

Theorem PEIRCE_implies_DNE : PEIRCE -> DNE.
Proof.
    unfold PEIRCE, DNE, not. intros H P1 H1.
    apply (H P1 False). intros HPF. exfalso. apply H1, HPF.
Qed.

Theorem PEIRCE_implies_IMPNOTOR : PEIRCE -> IMPNOTOR.
Proof.
    unfold PEIRCE, IMPNOTOR, not. intros.
    apply H with False. intros.
    right. apply H0. apply H with False. intros.
    exfalso. apply H1. left. assumption.
Qed.

Theorem PEIRCE_implies_DMGNAND : PEIRCE -> DMGNAND.
Proof.
    unfold PEIRCE, DMGNAND, not. intros.
    apply H with False. intros.
    left. apply H with False. intros.
    exfalso. apply H1. right. apply H with False. intros.
    exfalso. apply H0. split; assumption.
Qed.

(* apply theorem *)
Theorem IMPNOTOR_implies_LEM : IMPNOTOR -> LEM.
Proof.
    unfold IMPNOTOR, LEM, not. intros.
    apply or_comm, H. intros. assumption.
Qed.
Locate or_comm.
Check or_comm.
Search (?a \/ ?b <-> ?b \/ ?a).
Search "comm".

(* assert *)
Theorem IMPNOTOR_implies_DNE : IMPNOTOR -> DNE.
Proof.
    unfold IMPNOTOR, DNE, not. intros.
    assert (HPP: P -> P) by (intros;assumption).
    apply H in HPP. (* LEM *)
    destruct HPP as [HPPL|HPPR].
    - destruct (H0 HPPL).
    - assumption.
Qed.

Theorem IMPNOTOR_implies_PEIRCE : IMPNOTOR -> PEIRCE.
Proof.
    unfold IMPNOTOR, PEIRCE, not. intros.
    assert (HPP: P -> P) by (intros;assumption).
    apply H in HPP. (* LEM *)
    destruct HPP as [HPPL|HPPR].
    - apply H0. intros. destruct (HPPL H1).
    - assumption.
Qed.

Theorem IMPNOTOR_implies_DMGNAND : IMPNOTOR -> DMGNAND.
Proof.
    unfold IMPNOTOR, DMGNAND, not. intros.
    assert (HPP: P -> P) by (intros;assumption).
    apply H in HPP. (* LEM *)
    assert (HQQ: Q -> Q) by (intros;assumption).
    apply H in HQQ. (* LEM *)
    destruct HPP as [HPPL|HPPR].
    - destruct HQQ as [HQQL|HQQR].
      + exfalso. apply H0. split; assumption.
      + right. assumption.
    - left. assumption.
Qed.

(* destruct conj *)
Theorem DMGNAND_implies_LEM : DMGNAND -> LEM.
Proof.
    unfold DMGNAND, LEM, not. intros.
    apply H. intros Hcon. destruct Hcon as [HconL HconR].
    destruct (HconR HconL).
Qed.

Theorem DMGNAND_implies_DNE : DMGNAND -> DNE.
Proof.
    unfold DMGNAND, DNE, not. intros.
    assert (HP: P \/ False -> P).
    {
        intros. destruct H1 as [H1L|H1R].
        - assumption.
        - destruct H1R.  
    }
    apply HP, H. intros.
    destruct H1 as [H1L H1R].
    apply H0, H1L.
Qed.

Theorem DMGNAND_implies_PEIRCE : DMGNAND -> PEIRCE.
Proof.
    unfold DMGNAND, PEIRCE, not. intros.
    assert (HPP: P \/ P -> P).
    {
        intros. destruct H1; assumption.
    }
    apply HPP, H. intros.
    destruct H1 as [H1L H1R].
    apply H1L, H0. intros.
    destruct (H1L H1).
Qed.

Theorem DMGNAND_implies_IMPNOTOR : DMGNAND -> IMPNOTOR.
Proof.
    unfold DMGNAND, IMPNOTOR, not. intros.
    apply H. intros.
    destruct H1 as [H1L H1R].
    apply H1L. intros.
    apply H1R, H0, H1.
Qed.