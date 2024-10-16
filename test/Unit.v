From Trakt Require Import Trakt.


Require Import Setoid.

Lemma prop_ext : forall {P Q : Prop}, (forall (C : Prop -> Prop), C P -> C Q) -> P = Q.
Proof.
  intros P Q HPQ.
  apply (HPQ (fun y => P = y)).
  reflexivity.
Qed.



(* Lemma iffLRCon : forall {P Q : Prop}, P <-> Q -> (forall (C : Prop -> Prop), C P -> C Q). *)
(* Proof. *)
(*   intros P Q HPQ C. rewrite HPQ. *)




Trakt Set Verbosity 2.

Section Issue11.

  Variable P : nat -> Prop.
  Variable P' : nat -> bool.
  Hypothesis P_P' : forall x, P x <-> P' x = true.
  Trakt Add Relation 1 P P' P_P'.


  Lemma test1 :
    (forall f : nat -> Prop, (forall r : nat, f r = (P' r = true)) -> True) ->
    (forall f : nat -> Prop, (forall r : nat, f r = P r) -> True).
  Proof.
    intros H f Hf. apply (H f). intro r. (* Unprovable *)
  Abort.


  Lemma test2 :
    (forall f : nat -> Prop, (forall r : nat, f r <-> (P' r = true)) -> True) ->
    (forall f : nat -> Prop, (forall r : nat, f r <-> P r) -> True).
  Proof.
    intros H f Hf. apply (H f). intro r. rewrite Hf. apply P_P'.
  Qed.


  (* In this example, it is incorrect to replace P with P' *)
  Goal forall f : nat -> Prop, (forall r : nat, f r = P r) -> True.
  Proof.
    trakt bool.
  Abort.

  (* When the context around P is an equivalence, it may be provable,
     but we do not handle it yet. *)
  Goal forall f : nat -> Prop, (forall r : nat, f r <-> P r) -> True.
  Proof.
    trakt bool.
  Abort.

End Issue11.







Set verbosity level to 2
Added relation mapping between P and P' with no target (inferred)
Cas 01
Cas 02
Cas 03
Cas 04
preprocess-extra 01
preprocess-extra 02
generalise-free-variables []
preprocess-extra 03
after bool to Prop (raw):
prod `f` (prod `_` (global (indt «nat»)) c0 \ sort prop) c0 \
 prod `_`
  (prod `r` (global (indt «nat»)) c1 \
    app
     [global (indt «eq»), sort prop, app [c0, c1],
      app [global (const «P»), c1]]) c1 \ global (indt «True»)
after bool to Prop:
forall f : nat -> Prop, (forall r : nat, f r = P r) -> True
preprocess-extra 04
preprocess forall nat -> Prop
preprocess ->
preprocess forall nat
preprocess function application (no target) @eq
preprocess none Prop
preprocess function application (no target) elpi_ctx_entry_0_
preprocess none elpi_ctx_entry_1_
preprocess relation (with target) P
ICI 2
preprocess none elpi_ctx_entry_1_
preprocess True
after preprocess (raw):
prod2 `f` (prod `_` (global (indt «nat»)) c0 \ sort prop)
 (prod `_` (global (indt «nat»)) c0 \ sort prop) c0 \
 prod `_`
  (prod2 `r` (global (indt «nat»)) (global (indt «nat»)) c1 \
    app
     [global (indt «eq»), sort prop, app [c0, c1],
      app
       [global (indt «eq»), global (indt «bool»),
        app [global (const «P'»), c1], global (indc «true»)]]) c1 \
  app
   [global (indt «eq»), global (indt «bool»), global (indc «true»),
    global (indc «true»)]
preprocess-extra 05a
preprocess-extra 05b



after preprocess:
forall f : nat -> Prop, (forall r : nat, f r = (P' r = true)) -> true = true



preprocess-extra 05c



preprocess proof (raw):
proof.forall (prod `_` (global (indt «nat»)) c0 \ sort prop) (c0 \
 proof.lift-logic
  (app
    [global (const «InternalProofs.impl_morph_impl»),
     prod `r` (global (indt «nat»)) c1 \
      app
       [global (indt «eq»), sort prop, app [c0, c1],
        app [global (const «P»), c1]], global (indt «True»),
     prod `r` (global (indt «nat»)) c1 \
      app
       [global (indt «eq»), sort prop, app [c0, c1],
        app
         [global (indt «eq»), global (indt «bool»),
          app [global (const «P'»), c1], global (indc «true»)]],
     app
      [global (indt «eq»), global (indt «bool»), global (indc «true»),
       global (indc «true»)]])
  [proof.forall (global (indt «nat»)) (c1 \
    proof.trans contravariant
     [proof.none
       (app
         [global (indt «eq»), sort prop, app [c0, c1],
          app [global (const «P»), c1]]),
      proof.trans contravariant
       [proof.none
         (app
           [global (indt «eq»), sort prop, app [c0, c1],
            app [global (const «P»), c1]])],
      proof.trans contravariant
       [proof.of-term
         (app
           [global (const «InternalProofs.iffLR»),
            app [global (const «P»), c1],
            app
             [global (indt «eq»), global (indt «bool»),
              app [global (const «P'»), c1], global (indc «true»)],
            app [global (const «P_P'»), c1]]),
        proof.none
         (app
           [global (indt «eq»), sort prop, app [c0, c1],
            app
             [global (indt «eq»), global (indt «bool»),
              app [global (const «P'»), c1], global (indc «true»)]])]])
    c1 \
    fun `H`
     (prod `r` (global (indt «nat»)) c2 \
       app
        [global (indt «eq»), sort prop, app [c0, c2],
         app [global (const «P»), c2]]) c2 \
     fun `x` (global (indt «nat»)) c3 \ app [c1 c3, app [c2, c3]],
   proof.of-term
    (app
      [global (const «InternalProofs.refl_true_impl»),
       global (indt «bool»), global (indc «true»)])]) c0 \
 fun `H`
  (prod `f` (prod `_` (global (indt «nat»)) c1 \ sort prop) c1 \
    prod `_`
     (prod `r` (global (indt «nat»)) c2 \
       app
        [global (indt «eq»), sort prop, app [c1, c2],
         app
          [global (indt «eq»), global (indt «bool»),
           app [global (const «P'»), c2], global (indc «true»)]]) c2 \
     app
      [global (indt «eq»), global (indt «bool»), global (indc «true»),
       global (indc «true»)]) c1 \
  fun `x` (prod `_` (global (indt «nat»)) c2 \ sort prop) c2 \
   app [c0 c2, app [c1, c2]]
preprocess-extra 05d



preprocess proof:
fun
  (H : forall f : nat -> Prop,
       (forall r : nat, f r = (P' r = true)) -> true = true) (x : nat -> Prop)
=>
InternalProofs.impl_morph_impl
  (fun (H0 : forall r : nat, x r = P r) (x0 : nat) =>
   InternalProofs.iffLR (P_P' x0) (H0 x0)) InternalProofs.refl_true_impl
  (H x)



preprocess-extra 05d2
preprocess-extra branch 01



CoqProof =
fun
  (H : forall f : nat -> Prop,
       (forall r : nat, f r = (P' r = true)) -> true = true) (x : nat -> Prop)
=>
InternalProofs.impl_morph_impl
  (fun (H0 : forall r : nat, x r = P r) (x0 : nat) =>
   InternalProofs.iffLR (P_P' x0) (H0 x0)) InternalProofs.refl_true_impl
  (H x)



preprocess-extra branch 02



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
