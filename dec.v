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

Class Finite (A : Set) := {
                           l : list A;
                           is_listing : @Listing A l
                         }.

Definition Full' {A:Set} (l1 l2:list A) := NoDup l1 /\ NoDup l2 /\ forall a:A, In a l1 <-> ~ In a l2.

Lemma about_Full' {A : Set} `{is_dec_eq A}:
  forall (a : A) xs ys,
    ~ In a ys ->
    Full' ys (a :: xs) ->
    Full' (a :: ys) xs.
Proof.
  intros.
  destruct H1 as [H_ys [H_xs H2]].
  split; intros.
  - constructor; assumption.
  - split.
    + inversion H_xs; assumption.
    + intros.
      split; intros.
      * destruct H1.
        -- subst.
           inversion H_xs; subst.
           assumption.
        -- firstorder.
      * firstorder 1.
Qed.

Lemma listing_implies_full' {A : Set}:
  forall xs,
    Listing xs -> @Full' A nil xs.
Proof.
  intros.
  firstorder.
  constructor.
Qed.
Hint Resolve listing_implies_full'.

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

Lemma full'_nil_implies_listing {A : Set} `{is_dec_eq A}:
  forall xs, Full' nil xs -> @Listing A xs.
Proof.
  intros xs [? [? ?]].
  unfold Listing.
  split; eauto.
  unfold Full.
  intro.
  specialize (H2 a).
  assert (Decidable.decidable (In a xs)).
  {
    unfold Decidable.decidable.
    edestruct In_dec.
    - eapply H.
    - eauto.
    - eauto.
  }
  firstorder.
Qed.

Lemma full'_symm {A : Set} `{is_dec_eq A}:
  forall xs ys, Full' xs ys -> @Full' A ys xs.
Proof.
  intros xs ys [? [? ?]].
  do 2 (split; eauto).
  intros.
  split; intros.
  - intro.
    eapply H2; eassumption.
  - cut (forall x y : A, {x = y} + {x <> y}).
    {
      intros H_dec.
      destruct (In_dec H_dec a ys).
      - assumption.
      - firstorder.
    }
    eapply H.
Qed.

Instance iff_dec {A : Set} {P Q : A -> Prop}
         `{@is_dec_pred A P} `{@is_dec_pred A Q}: @is_dec_pred A (fun a => P a <-> Q a).
Proof.
  constructor.
  intros.
  destruct (@dec_pred _ P _ a); destruct (@dec_pred _ Q _ a); firstorder.
Defined.    
Hint Resolve iff_dec : typeclass_instances.

Instance forall_dec {A B : Set} `{Finite B} `{is_dec_eq B} {P : A -> B -> Prop}
         `{@is_dec_rel A B P} : @is_dec_pred A (fun a => forall (b : B), P a b).
Proof.
  constructor.
  destruct H as [lB ?H].
  intros.
  cut ({forall b : B, In b lB -> P a b} + {~ (forall b : B, P a b)}).
  {
    intros.
    destruct H as [? ?].
    destruct H2; eauto.
  }
  {
    eapply listing_implies_full' in H.
    revert H.
    generalize (nil : list B).
    induction lB.
    - firstorder.
    - rename a0 into b.
      intros lB' ?.
      assert (Full' (b :: lB') lB).
      {
        eapply about_Full'; eauto.
        firstorder.
      }
      destruct (@dec_rel A B P _ a b).
      + destruct (IHlB (b :: lB') H2).
        * left.
          intros ? [? | ?]; subst; eauto.
        * right.
          assumption.
      + right.
        firstorder.
  }
Defined.
Hint Resolve forall_dec : typeclass_instances.

Instance exist_dec {A B : Set} `{Finite B} `{is_dec_eq B} {P : A -> B -> Prop}
         `{@is_dec_rel A B P} : @is_dec_pred A (fun a => exists (b : B), P a b).
Proof.
  constructor.
  destruct H as [lB ?H].
  intros.
  cut ({ exists b : B, P a b} + {~ (exists b : B, In b lB /\ P a b)}).
  {
    firstorder.
  }
  {
    eapply listing_implies_full' in H.
    revert H.
    generalize (nil : list B).
    induction lB.
    - firstorder 2.
    - intros lB' ?.
      rename a0 into b.
      assert (Full' (b :: lB') lB).
      {
        eapply about_Full'; eauto.
        firstorder.
      }
      destruct (@dec_rel A B P _ a b).
      + firstorder 2.
      + destruct (IHlB (b :: lB') H2) as [? | ?].
        * firstorder 2.
        * right.
          intros [b' [? ?]].
          eapply n0.
          exists b'.
          split; eauto.
          destruct H3; subst; firstorder.
  }
Defined.    
Hint Resolve exist_dec : typeclass_instances.

Instance in_dec {A : Set} `{is_dec_eq A} {xs : list A} : is_dec_pred (fun a => In a xs).
Proof.
  constructor.
  intros.
  eapply Lists.List.in_dec.
  firstorder 2.
Defined.
Hint Resolve in_dec : typeclass_instances.

