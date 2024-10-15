From Trakt Require Import Trakt.


Section Issue11.

  Variable P : nat -> Prop.
  Variable P' : nat -> bool.
  Hypothesis P_P' : forall x, P x <-> P' x = true.
  Trakt Add Relation 1 P P' P_P'.

  Goal forall f : nat -> Prop, (forall r : nat, f r = P r) -> True.
  Proof.
    trakt bool.
  Abort.

End Issue11.





CoqProof =
fun
  (H : forall f : nat -> Prop,
       (forall r : nat, f r = (P' r = true)) -> true = true) (x : nat -> Prop)
=>
InternalProofs.impl_morph_impl
  (fun (H0 : forall r : nat, x r = P r) (x0 : nat) =>
   InternalProofs.iffLR (P_P' x0) (H0 x0)) InternalProofs.refl_true_impl
  (H x)



CleanCoqProof =
fun
  (H : forall f : nat -> Prop,
       (forall r : nat, f r = (P' r = true)) -> true = true) (x : nat -> Prop)
=>
InternalProofs.impl_morph_impl
  (fun (H0 : forall r : nat, x r = P r) (x0 : nat) =>
   InternalProofs.iffLR (P_P' x0) (H0 x0)) InternalProofs.refl_true_impl
  (H x)
Error:
In environment
P : nat -> Prop
P' : nat -> bool
P_P' : forall x : nat, P x <-> P' x = true
H :
forall f : nat -> Prop, (forall r : nat, f r = (P' r = true)) -> true = true
x : nat -> Prop
H0 : forall r : nat, x r = P r
x0 : nat
The term "H0 x0" has type "x x0 = P x0" while it is expected to have type
 "P x0".


Lemma impl_morph_impl : forall {A B A' B' : Prop},
  (A -> A') -> (B' -> B) -> ((A' -> B') -> (A -> B)).

Lemma iffLR : forall {P Q : Prop}, P <-> Q -> (P -> Q).
