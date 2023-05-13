From Trakt Require Import Trakt.
From Coq Require Import ZArith.
Local Open Scope Z_scope.


(* Embedding for positive *)

Require Import PArith.

Section Relations_positive.

  (* Embedding *)
  Lemma positive_Z_FBInverseProof : forall (n : positive), n = Z.to_pos (Z.pos n).
  Proof.
    intros n. reflexivity.
  Qed.

  Lemma positive_Z_BFPartialInverseProof_bool : forall (z : Z), (0 <? z)%Z = true ->
                                                           Z.pos (Z.to_pos z) = z.
  Proof.
    intros z.
    destruct z eqn: E.
    - discriminate.
    - reflexivity.
    - discriminate.
  Qed.

  Lemma positive_Z_ConditionProof_bool : forall (n : positive), (0 <? Z.pos n)%Z = true.
  Proof.
    intros n. reflexivity.
  Qed.

  (* Addition *)
  Lemma Positiveadd_Zadd_embedding_equality : forall (n m : positive),
      Z.pos (n + m)%positive = ((Z.pos n) + (Z.pos m))%Z.
  Proof.
    intros n m. reflexivity.
  Qed.

  (* Multiplication *)
  Lemma Positivemul_Zmul_embedding_equality : forall (n m : positive),
      Z.pos (n * m)%positive = ((Z.pos n) * (Z.pos m))%Z.
  Proof.
    intros n m. reflexivity.
  Qed.

  (* Equality *)
  Lemma Positiveeq_Zeqb_embedding : forall (n m : positive),
      n = m <-> (Z.eqb (Z.pos n) (Z.pos m)) = true.

  Proof.
    intros n m .
    simpl.
    symmetry.
    apply Pos.eqb_eq.
  Qed.

  Lemma Positiveeqb_Zeqb_embedding_equality : forall (n m : positive),
      Pos.eqb n m = (Z.eqb (Z.pos n) (Z.pos m)).
  Proof.
    intros n m. simpl. reflexivity.
  Qed.

  (* Less or equal *)
  Lemma Positivele_Zleb_embedding : forall (n m : positive),
      (n <= m)%positive <-> (Z.leb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m .
    simpl.
    symmetry.
    apply Pos.leb_le.
  Qed.

  Lemma Positiveleb_Zleb_embedding_equality : forall (n m : positive),
      (n <=? m)%positive = (Z.leb (Z.pos n) (Z.pos m)).
  Proof.
    intros n m.
    unfold Z.leb. reflexivity.
  Qed.

  (* Less than *)
  Lemma Positivelt_Zltb_embedding : forall (n m : positive),
      (n < m)%positive <-> (Z.ltb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m .
    simpl.
    symmetry.
    apply Pos.ltb_lt.

  Qed.

  Lemma Positiveltb_Zltb_embedding_equality : forall (n m : positive),
      (n <? m)%positive = (Z.ltb (Z.pos n) (Z.pos m)).
  Proof.
    intros n m.
    reflexivity.
  Qed.

  (* Greater or equal *)
  Lemma Positivege_Zgeb_embedding : forall (n m : positive),
      (n >= m)%positive <-> (Z.geb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m.
    unfold Z.geb. simpl.
    rewrite Pos.ge_le_iff.
    rewrite <- Pos.compare_ge_iff.
    split; destruct (n ?= m)%positive eqn:E; congruence.
  Qed.

  (* Greater than *)
  Lemma Positivegt_Zgtb_embedding : forall (n m : positive),
      (n > m)%positive <-> (Z.gtb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m.
    unfold Z.gtb. simpl.
    rewrite Pos.gt_lt_iff.
    rewrite <- Pos.compare_gt_iff.
    split; destruct (n ?= m)%positive eqn:E; try reflexivity; discriminate.
  Qed.

End Relations_positive.

Trakt Add Embedding
      (positive) (Z) (Z.pos) (Z.to_pos) (positive_Z_FBInverseProof) (positive_Z_BFPartialInverseProof_bool)
      (positive_Z_ConditionProof_bool).

Trakt Add Symbol (Pos.add) (Z.add) (Positiveadd_Zadd_embedding_equality).
Trakt Add Symbol (Pos.mul) (Z.mul) (Positivemul_Zmul_embedding_equality).
Trakt Add Symbol (Pos.eqb) (Z.eqb) (Positiveeqb_Zeqb_embedding_equality).
Trakt Add Symbol (Pos.leb) (Z.leb) (Positiveleb_Zleb_embedding_equality).
Trakt Add Symbol (Pos.ltb) (Z.ltb) (Positiveltb_Zltb_embedding_equality).

Trakt Add Relation 2 (@eq positive) (Z.eqb) (Positiveeq_Zeqb_embedding).
Trakt Add Relation 2 (Pos.le) (Z.leb) (Positivele_Zleb_embedding).
Trakt Add Relation 2 (Pos.lt) (Z.ltb) (Positivelt_Zltb_embedding).
Trakt Add Relation 2 (Pos.ge) (Z.geb) (Positivege_Zgeb_embedding).
Trakt Add Relation 2 (Pos.gt) (Z.gtb) (Positivegt_Zgtb_embedding).


(* Goals with positives are well transformed... *)
Goal forall (x y:positive), (x <=? y)%positive = true.
Proof.
  trakt Z bool.
Abort.


(* ... but goals with constants in Z are obfuscated, because Z is built
   upon positive *)

Goal forall (x y z:Z), x <=? 3 = true.
Proof.
  trakt Z bool.
Abort.
