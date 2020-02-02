Require Import Coq.Logic.FinFun List.

Class is_dec_eq (A : Set) :=
  {
    dec_eq: forall (a b : A), { a = b } + { a <> b }
  }.

Lemma dec_eq_refl {A : Set} `{is_dec_eq A}:
  forall (x : A) (B : Type) (P Q : B),
    (if (dec_eq x x) then P else Q) = P.
Proof.
  intros.
  destruct (dec_eq x x).
  - reflexivity.
  - congruence.
Qed.

Lemma dec_eq_neq {A : Set} `{is_dec_eq A}:
  forall (x y : A) (B : Type) (P Q : B),
    x <> y ->
    (if (dec_eq x y) then P else Q) = Q.
Proof.
  intros.
  destruct (dec_eq x y).
  - congruence.
  - reflexivity.
Qed.

Class is_dec_rel {A B : Set} (f : A -> B -> Prop) :=
  {
    dec_rel: forall a b, { f a b } + { ~ f a b }
  }.

Class is_dec_pred {A : Set} (f : A -> Prop) :=
  {
    dec_pred: forall (a : A), { f a } + { ~ f a }
  }.

Instance dec_eq_pair (A B : Set) `{is_dec_eq A} `{is_dec_eq B} : is_dec_eq (A * B).
Proof.
  constructor.
  intros [a1 b1] [a2 b2].
  destruct (dec_eq a1 a2); subst.
  - destruct (dec_eq b1 b2); subst.
    + eauto.
    + right.
      intro.
      inversion H1; subst.
      eauto.
  - right.
    intro.
    inversion H1; subst.
    eauto.
Defined.
Hint Resolve dec_eq_pair : typeclass_instances.

Instance in_dec {A : Set} `{is_dec_eq A} {xs : list A} : is_dec_pred (fun a => In a xs).
Proof.
  constructor.
  intros.
  eapply Lists.List.in_dec.
  firstorder 2.
Defined.
Hint Resolve in_dec : typeclass_instances.

