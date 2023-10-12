(* This file checks that `trakt`'s failures can be handled in Ltac *)


From Trakt Require Import Trakt.
From Coq Require Import ZArith.


(* Embedding for N *)

Section Relations_N.

  (* Embedding *)
  Lemma N_Z_FBInverseProof : forall (n : N), n = Z.to_N (Z.of_N n).
  Proof. intros n ; symmetry ; apply N2Z.id. Qed.

  Lemma N_Z_BFPartialInverseProof_bool : forall (z : Z), (0 <=? z)%Z = true ->
                                                           Z.of_N (Z.to_N z) = z.
  Proof. intros z H. induction z.
  - reflexivity.
  - reflexivity.
  - assert (H1 : forall p : positive, (Z.neg p < 0)%Z) by apply Pos2Z.neg_is_neg.
    specialize (H1 p). apply Zle_bool_imp_le in H. apply Zle_not_lt in H.
    unfold not in H1. apply H in H1. elim H1. Qed.

  Lemma N_Z_ConditionProof_bool : forall (n : N), (0 <=? Z.of_N n)%Z = true.
  Proof. intros n. apply Zle_imp_le_bool. apply N2Z.is_nonneg. Qed.

End Relations_N.

Trakt Add Embedding
      (N) (Z) (Z.of_N) (Z.to_N) (N_Z_FBInverseProof) (N_Z_BFPartialInverseProof_bool)
      (N_Z_ConditionProof_bool).


(* Equality for bit vectors *)

Parameter bitvector : N -> Type.
Parameter bv_eq :
  forall n, bitvector n -> bitvector n -> bool.

Lemma bv_eq_P2B (n:N) (a b:bitvector n) :
  a = b <-> bv_eq n a b = true.
Admitted.

Trakt Add Relation 2
  (fun n => @eq (bitvector n))
  (fun n => bv_eq n)
  (fun n a b => bv_eq_P2B n a b).


(* This one goes through... *)

Goal forall (a b : bitvector 42),
    a = b.
Proof.
  intros. trakt Z bool.
Abort.


(* ... but this one fails. It does not fail if there is not embedding on
   N. *)

Parameter land : forall n, bitvector n -> bitvector n -> bitvector n.

Goal forall (a : bitvector 4),
    land 4 a a = a.
Proof.
  intro a. try trakt Z bool.
Abort.
