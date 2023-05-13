From Trakt Require Import Trakt.
Require Import List.

Section list.

  Variables
    (A:Type)
    (eqA : A -> A -> bool)
    (eq_eqA : forall (a b:A), a = b <-> eqA a b = true).

  Fixpoint eqlist (l1 l2:list A) {struct l1} : bool :=
    match l1, l2 with
    | nil, nil => true
    | x::xs, y::ys => (eqA x y) && (eqlist xs ys)
    | _, _ => false
    end.

  Lemma eq_eqlist (l1 l2:list A):
    l1 = l2 <-> eqlist l1 l2 = true.
  Admitted.

End list.

Trakt Add Relation 2
  (fun (A:Type) (eqA : A -> A -> bool) (eq_eqA : forall (a b:A), a = b <-> eqA a b = true) => @eq (list A))
  (fun (A:Type) (eqA : A -> A -> bool) (eq_eqA : forall (a b:A), a = b <-> eqA a b = true) => eqlist A eqA)
  (fun (A:Type) (eqA : A -> A -> bool) (eq_eqA : forall (a b:A), a = b <-> eqA a b = true) => eq_eqlist A eqA eq_eqA).
