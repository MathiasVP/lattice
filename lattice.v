Require Import Setoid.

Module Type Lattice.

Parameter lattice : Set.
Parameter join: lattice -> lattice -> lattice.
Parameter meet: lattice -> lattice -> lattice.
Parameter top: lattice.
Parameter bot: lattice.
Parameter eq: lattice -> lattice -> Prop. 

Axiom eq_equiv: equivalence _ eq.

Instance eq_equiv_inst : Equivalence eq.
constructor; eapply eq_equiv.
Qed.

Notation " x '===' y " := (eq x y) (at level 70, no associativity) : equiv_scope.
Notation " x '=/=' y " := (complement eq x y) (at level 70, no associativity) : equiv_scope.
Local Open Scope equiv_scope.

Notation "X '⊔' Y" := (join X Y) (at level 41, left associativity).
Notation "X '⊓' Y" := (meet X Y) (at level 40, left associativity).
Notation "X '⊑' Y" := (X ⊔ Y === Y) (at level 70, no associativity).
Notation "⊥" := bot.
Notation "⊤" := top.

Axiom meet_symmetry: forall a b   : lattice,  meet a b === meet b a.
Axiom join_symmetry: forall a b   : lattice,  join a b === join b a.
Axiom join_assoc   : forall a b c : lattice,  join a (join b c) === join (join a b) c.
Axiom join_distrib : forall a b   : lattice,  join a (meet a b) === a.
Axiom meet_assoc   : forall a b c : lattice,  meet a (meet b c) === meet (meet a b) c.
Axiom meet_distrib : forall a b   : lattice,  meet a (join a b) === a.
Axiom eq_dec  : forall a b   : lattice,  { a === b} + { a =/= b }.
Axiom join_bot: forall a     : lattice, join ⊥ a === a.
Axiom join_top: forall a     : lattice, join ⊤ a === ⊤.
Axiom meet_bot: forall a     : lattice, meet ⊥ a === ⊥.
Axiom meet_top: forall a     : lattice, meet ⊤ a === a.

Axiom join_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊔ y1 === x2 ⊔ y2.
Axiom meet_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊓ y1 === x2 ⊓ y2.
Axiom flowsto_compat_right: forall x y z, x === y -> z ⊑ y -> z ⊑ x.
Axiom flowsto_compat_left: forall x y z, x === y -> y ⊑ z -> x ⊑ z.

Hint Resolve meet_symmetry join_symmetry join_assoc meet_assoc meet_distrib join_distrib
eq_dec join_top join_bot meet_top meet_bot.

End Lattice.

(* General lattice properties derivable from the axioms *)
Module LatticeProperties (L: Lattice).
Import L.

Local Open Scope equiv_scope.

Lemma lat_eq_refl:
  forall x : lattice, x === x.
Proof. eapply eq_equiv. Qed.

Lemma lat_eq_sym:
  forall x y : lattice, x === y -> y === x.
Proof. eapply eq_equiv. Qed.

Lemma lat_eq_trans:
  forall x y z : lattice, x === y -> y === z -> x === z.
Proof. eapply eq_equiv. Qed.

Add Parametric Relation : lattice eq
    reflexivity proved by lat_eq_refl
    symmetry proved by lat_eq_sym
    transitivity proved by lat_eq_trans
      as eq_rel.

Class Morphism2 (f : lattice -> lattice -> lattice) := {
  compat2: forall (x1 y1 x2 y2 : lattice), x1 === x2 -> y1 === y2 -> f x1 y1 === f x2 y2 }.

Class MorphismR (f : lattice -> lattice -> Prop) := {
  compatR: forall (x1 y1 x2 y2 : lattice), x1 === x2 -> y1 === y2 -> f x1 y1 <-> f x2 y2 }.

Add Parametric Morphism {f : lattice -> lattice -> lattice} `{Morphism2 f}:
  f with signature eq ==> eq ==> eq as eq_rewrite2.
Proof.
  intros.
  eapply compat2; eauto.
Qed.

Add Parametric Morphism {f : lattice -> lattice -> Prop} `{MorphismR f}:
  f with signature eq ==> eq ==> Basics.flip Basics.impl as eq_rewrite3.
Proof.
  intros.
  unfold Basics.impl.
  intros.
  eapply compatR; eauto.
Qed.
  
Instance join_inst: Morphism2 join := { compat2 := join_compat }.
Instance meet_inst: Morphism2 meet := { compat2 := meet_compat }.

Lemma idem_join:
    forall a : lattice,
      join a a === a.
Proof.
  intros.
  rewrite <- (meet_distrib a a) at 2.
  eauto.
Qed.
Local Hint Resolve idem_join.
  
Lemma idem_meet:
    forall a, meet a a === a.
Proof.
  intros.
  rewrite <- (join_distrib a a) at 2.
  eauto.
Qed.
Local Hint Resolve idem_meet.

Lemma flowsto_refl: forall a, a ⊑ a.
Proof. eauto. Qed.
Local Hint Resolve flowsto_refl.

Lemma flowsto_trans: 
  forall a b c, a ⊑ b -> b ⊑ c -> a ⊑ c.
Proof.
  intros.
  rewrite <- H0.
  setoid_replace (join a (join b c)) with (join (join a b) c) by eauto.
  rewrite -> H.
  reflexivity.
Qed.

Definition flowsto a b := a ⊔ b === b.
Hint Unfold flowsto.

Instance flowsto_preorder_inst : PreOrder flowsto.
constructor.
- eauto.
- unfold Transitive.
  intros.
  eauto using flowsto_trans.
Defined.

Add Parametric Relation : lattice flowsto
    reflexivity proved by flowsto_refl
    transitivity proved by flowsto_trans
      as flowsto_rel.

Hint Extern 1 (?a ⊑ ?c) =>
match goal with
| [H: a ⊑ ?b |- _] => apply (flowsto_trans a b c)
| [H: ?b ⊑ c |- _] => apply (flowsto_trans a b c)
end.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" "*" :=
  match goal with
    [H: _ |- _] => setoid_replace x with y in H
  end.

Tactic Notation "setoid_replace" constr(x) "with" constr(y) "in" "*" "by" tactic(t) :=
  match goal with
    [H: _ |- _] => setoid_replace x with y in H by t
  end.

Lemma anti_sym:
  forall a b,
    a ⊑ b ->
    b ⊑ a ->
    a === b.
Proof.
  intros a b H1 H2.
  setoid_replace (join b a) with (join a b) in * by eauto.
  rewrite <- H1.
  rewrite -> H2.
  reflexivity.
Qed.
Local Hint Resolve anti_sym.

Lemma flowsto_not:
  forall ℓ₁ ℓ₂ ℓ₃,
    ℓ₁ ⊑ ℓ₂ ->
    not (ℓ₁ ⊑ ℓ₃) ->
    not (ℓ₂ ⊑ ℓ₃).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ H1 H2.
  intro H_absurd.
  contradiction (flowsto_trans _ _ _ H1 H_absurd).
Qed.
Hint Resolve flowsto_not.

Lemma flowsto_join:
  forall a b,
    a ⊑ join a b.
Proof.
  intros.
  rewrite -> join_assoc.
  rewrite -> idem_join.
  reflexivity.
Qed.
Hint Resolve flowsto_join.

Lemma meet_join_consistent:
  forall a b,
    a ⊓ b === a <-> a ⊔ b === b.
Proof.
  intros.
  split; intros.
  - assert (b === b ⊔ (b ⊓ a)).
    {
      rewrite -> (join_distrib b a).
      reflexivity.
    }
    assert (b ⊔ (b ⊓ a) === b ⊔ a).
    {
      rewrite -> meet_symmetry.
      rewrite -> H.
      reflexivity.
    }
    rewrite -> join_symmetry.
    rewrite <- H1.
    rewrite <- H0.
    reflexivity.
  - assert (a === a ⊓ (a ⊔ b)).
    {
      rewrite -> (meet_distrib a b).
      reflexivity.
    }
    assert (a ⊓ (a ⊔ b) === a ⊓ b).
    {
      rewrite -> H.
      reflexivity.
    }
    rewrite <- H1.
    symmetry.
    assumption.
Qed.

Lemma flowsto_meet:
  forall a b,
    meet a b ⊑ a.
Proof.
  intros.
  rewrite -> meet_symmetry.
  rewrite <- meet_join_consistent.
  rewrite <- meet_assoc.
  rewrite -> idem_meet.
  reflexivity.
Qed.
Hint Resolve flowsto_meet.

Class MorphismUR (f : lattice -> Prop) := {
  compatUR: forall (x y : lattice), x === y -> f y <-> f x }.

Add Parametric Morphism {f : lattice -> Prop} `{MorphismUR f}:
  f with signature eq ==> Basics.flip Basics.impl as eq_rewrite4.
Proof.
  intros.
  unfold Basics.impl.
  intros.
  symmetry in H0.
  eapply (compatUR y x); assumption.
Qed.

Instance flowsto_inst : MorphismR (fun a b => a ⊔ b === b).
Proof.
  constructor.
  intros.
  split; intros.
  - symmetry in H0.
    eapply (flowsto_compat_right y2 y1 x2); eauto.
    symmetry in H.
    eapply (flowsto_compat_left x2 x1 y1); eauto.
  - symmetry in H0.
    eapply (flowsto_compat_left x1 x2 y1); eauto.
    symmetry in H0.
    eapply (flowsto_compat_right y1 y2 x2); eauto.
Qed.

Lemma join_flowsto_implies_flowsto:
  forall ℓ₁ ℓ₂ ℓ₃,
    join ℓ₁ ℓ₂ ⊑ ℓ₃ -> ℓ₁ ⊑ ℓ₃ /\ ℓ₂ ⊑ ℓ₃.
Proof.
  intros.
  assert (ℓ₁ ⊑ join ℓ₁ ℓ₂) by apply flowsto_join.
  assert (ℓ₂ ⊑ join ℓ₁ ℓ₂).
  {
    rewrite -> (join_symmetry ℓ₁ ℓ₂).
    eapply flowsto_join.
  }
  split; eapply flowsto_trans; eauto.
Qed.

Lemma meet_flowsto_implies_flowsto:
  forall ℓ₁ ℓ₂ ℓ₃,
    ℓ₁ ⊑ meet ℓ₂ ℓ₃ -> ℓ₁ ⊑ ℓ₂ /\ ℓ₁ ⊑ ℓ₃.
Proof.
  intros.
  assert (meet ℓ₂ ℓ₃ ⊑ ℓ₂) by eauto.
  assert (meet ℓ₂ ℓ₃ ⊑ ℓ₃) by (rewrite -> meet_symmetry; apply flowsto_meet).
  split; eapply flowsto_trans; eauto.
Qed.

Ltac destruct_join_flowsto :=
  match goal with
    [H: join ?a ?b ⊑ ?c |- _] => destruct (join_flowsto_implies_flowsto a b c H); clear H
  end.

Lemma not_flowsto_implies_not_join_flowsto:
  forall a b c,
    ~ a ⊑ c ->
    ~ b ⊑ c ->
    ~ join a b ⊑ c.
Proof.
  intros.
  intro.
  rewrite <- H1 in *.
  rewrite <- join_assoc in *.
  contradiction H.
  eapply flowsto_join.
Qed.

Lemma implies_join_flowsto:
  forall a b c,
    a ⊑ c ->
    b ⊑ c ->
    a ⊔ b ⊑ c.
Proof.
  intros.
  rewrite <- join_assoc.
  rewrite -> H0.
  assumption.
Qed.
Hint Resolve implies_join_flowsto.

Lemma implies_meet_flowsto:
  forall c a b,
    c ⊑ a ->
    c ⊑ b ->
    c ⊑ a ⊓ b.
Proof.
  intros.
  eapply meet_join_consistent in H.
  eapply meet_join_consistent in H0.
  rewrite <- H.
  rewrite <- H0.
  eapply meet_join_consistent.
  rewrite -> meet_assoc.
  repeat rewrite <- meet_assoc.
  rewrite -> (meet_assoc a a b).
  rewrite -> idem_meet.
  rewrite -> (meet_symmetry a b).
  rewrite -> (meet_assoc b b a).
  rewrite -> idem_meet.
  reflexivity.
Qed.
Hint Resolve implies_meet_flowsto.

Lemma join_is_increasing:
  forall a b c,
    a ⊑ b ->
    a ⊑ (b ⊔ c).
Proof.
  intros.
  rewrite -> join_assoc.
  rewrite -> H.
  reflexivity.
Qed.
Hint Resolve join_is_increasing.

Lemma meet_is_decreasing:
  forall a b c,
    a ⊑ b ->
    a ⊓ c ⊑ b.
Proof.
  intros.
  eapply meet_join_consistent.
  eapply meet_join_consistent in H.
  rewrite <- meet_assoc.
  rewrite -> (meet_symmetry c b).
  rewrite -> meet_assoc.
  rewrite -> H.
  reflexivity.
Qed.
Hint Resolve meet_is_decreasing.

Lemma top_is_top:
  forall a,
    a ⊑ top.
Proof.
  intros.
  rewrite <- join_symmetry.
  eauto.
Qed.
Hint Resolve top_is_top.

Lemma flowsto_top_is_top:
  forall a, ⊤ ⊑ a -> a === ⊤.
Proof.
  intros a H.
  rewrite -> join_top in H.
  symmetry.
  assumption.
Qed.
Hint Resolve flowsto_top_is_top.

Lemma bot_flowsto_is_bot:
  forall a, a ⊑ ⊥ -> a === ⊥.
Proof.
  intros a H.
  rewrite -> join_symmetry in H.
  rewrite -> join_bot in H.
  assumption.
Qed.
Hint Resolve bot_flowsto_is_bot.

Lemma flowsto_dec:
  forall a b, { a ⊑ b } + { ~ (a ⊑ b) }.
Proof.
  intros.
  eapply eq_dec.
Qed.

End LatticeProperties.

(* The product of two bounded lattices form another bounded lattice *)
Module ProductLattice (A B : Lattice) <: Lattice.
  Definition lattice := prod A.lattice B.lattice.  
  Module Import LA := LatticeProperties(A).
  Module Import LB := LatticeProperties(B).
  
  Definition eq (ab1 ab2 : prod A.lattice B.lattice) : Prop :=
    match ab1, ab2 with
      (a1, b1), (a2, b2) => A.eq a1 a2 /\ B.eq b1 b2
    end.
  Hint Unfold eq.
  
  Lemma eq_equiv:
    equivalence _ eq.
  Proof.
    unfold equiv.
    constructor.
    - unfold reflexive.
      intros.
      destruct x as [a b].
      unfold eq.
      split; reflexivity.
    - unfold transitive.
      intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4]. 
      split.
      + rewrite -> H1; assumption.
      + rewrite -> H2; assumption.
    - unfold symmetric.
      intros [a1 b1] [a2 b2].
      unfold eq.
      intros [H1 H2].
      symmetry in H1.
      symmetry in H2.
      split; assumption.
  Qed.

  Instance eq_equiv_inst : Equivalence eq.
  constructor; eapply eq_equiv.
  Qed.

  Notation " x === y " := (eq x y) (at level 70, no associativity) : equiv_scope.
  Notation " x =/= y " := (complement eq x y) (at level 70, no associativity) : equiv_scope.
  Local Open Scope equiv_scope.

  Definition meet (x y : lattice) :=
    match x, y with
      (a1, b1), (a2, b2) => (A.meet a1 a2, B.meet b1 b2)
    end.

  Definition join (x y : lattice) :=
    match x, y with
      (a1, b1), (a2, b2) => (A.join a1 a2, B.join b1 b2)
    end.
  
  Notation "X ⊑ Y" := (join X Y === Y) (at level 70, no associativity).
  Notation "X ⊔ Y" := (join X Y) (at level 40, left associativity).
  Notation "X ⊓ Y" := (meet X Y) (at level 40, left associativity).
  
  Lemma join_compat: forall x1 y1 x2 y2 : lattice, x1 === x2 -> y1 === y2 -> x1 ⊔ y1 === x2 ⊔ y2.
  Proof.
    intros [a1 b1] [a2 b2] [a3 b3] [a4 b4] [H1 H2] [H3 H4].
    unfold eq.
    simpl.
    rewrite -> H1.
    rewrite -> H3.
    rewrite -> H2.
    rewrite -> H4.
    split; reflexivity.
  Qed.
  
  Lemma meet_compat: forall x1 y1 x2 y2 : lattice, x1 === x2 -> y1 === y2 -> x1 ⊓ y1 === x2 ⊓ y2.
  Proof.
    intros [a1 b1] [a2 b2] [a3 b3] [a4 b4] [H1 H2] [H3 H4].
    unfold eq.
    simpl.
    rewrite -> H1.
    rewrite -> H3.
    rewrite -> H2.
    rewrite -> H4.
    split; reflexivity.
  Qed.
  
  Lemma meet_symmetry: forall a b : lattice, meet a b === meet b a.
  Proof.
    intros.
    unfold meet.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    unfold eq.
    rewrite -> A.meet_symmetry.
    rewrite -> B.meet_symmetry.
    split; reflexivity.
  Qed.

  Lemma join_symmetry: forall a b : lattice, join a b === join b a.
  Proof.
    intros.
    unfold join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    unfold eq.
    rewrite -> A.join_symmetry.
    rewrite -> B.join_symmetry.
    split; reflexivity.
  Qed.

  Lemma join_assoc: forall a b c : lattice, join a (join b c) === join (join a b) c.
  Proof.
    intros.
    unfold join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    destruct c as [a3 b3].
    unfold eq.
    rewrite -> A.join_assoc.
    rewrite -> B.join_assoc.
    split; reflexivity.
  Qed.

  Lemma meet_assoc: forall a b c : lattice, meet a (meet b c) === meet (meet a b) c.
  Proof.
    intros.
    unfold meet.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    destruct c as [a3 b3].
    unfold eq.
    rewrite -> A.meet_assoc.
    rewrite -> B.meet_assoc.
    split; reflexivity.
  Qed.

  Lemma meet_distrib: forall a b : lattice, meet a (join a b) === a.
  Proof.
    intros.
    unfold meet, join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    unfold eq.
    rewrite -> A.meet_distrib.
    rewrite -> B.meet_distrib.
    split; reflexivity.
  Qed.
  Hint Resolve meet_distrib.
  
  Lemma join_distrib: forall a b : lattice, join a (meet a b) === a.
  Proof.
    intros.
    unfold meet, join.
    destruct a as [a1 b1].
    destruct b as [a2 b2].
    unfold eq.
    rewrite -> A.join_distrib.
    rewrite -> B.join_distrib.
    split; reflexivity.
  Qed.
  Hint Resolve join_distrib.
    
  Lemma flowsto_compat_right: forall x y z : lattice, x === y -> z ⊑ y -> z ⊑ x.
  Proof.
    intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4].
    unfold eq.
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    rewrite -> H3.
    rewrite -> H4.
    split; reflexivity.
  Qed.

  Lemma flowsto_compat_left: forall x y z : lattice, x === y -> y ⊑ z -> x ⊑ z.
  Proof.
    intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4].
    unfold eq.
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    rewrite -> H3.
    rewrite -> H4.
    split; reflexivity.
  Qed.
  
  Lemma flowsto_pointwise_proj1:
    forall (a1 a2 : A.lattice)
      (b1 b2 : B.lattice),
      (a1, b1) ⊑ (a2, b2) ->
      LA.flowsto a1 a2.
  Proof.
    intros.
    unfold eq in *.
    simpl in *.
    destruct H as [H1 H2].
    assumption.
  Qed.
  Hint Resolve flowsto_pointwise_proj1.

  Lemma flowsto_pointwise_proj2:
    forall (a1 a2 : A.lattice)
      (b1 b2 : B.lattice),
      (a1, b1) ⊑ (a2, b2) ->
      LB.flowsto b1 b2.
  Proof.
    intros.
    unfold eq in *.
    simpl in *.
    destruct H as [H1 H2].
    assumption.
  Qed.
  Hint Resolve flowsto_pointwise_proj2.      

  Lemma join_is_pairwise:
    forall (a1 a2 : A.lattice)
      (b1 b2 : B.lattice),
      join (a1, b1) (a2, b2) ===
      (A.join a1 a2, B.join b1 b2).
  Proof.
    reflexivity.
  Qed.

Lemma eq_dec: forall a b : lattice, {a === b} + {a =/= b}.
Proof.
  intros.
  destruct a as [a1 b1].
  destruct b as [a2 b2].
  unfold eq.
  destruct (A.eq_dec a1 a2); destruct (B.eq_dec b1 b2).
  - left.
    split; assumption.
  - right.
    intro.
    destruct H.
    contradiction.
  - right.
    intro.
    destruct H.
    contradiction.
  - right.
    intro.
    destruct H.
    contradiction.
Qed.

Definition bot := (A.bot, B.bot).
Definition top := (A.top, B.top).
Hint Unfold bot top.

Lemma join_bot:
  forall a,
    join bot a === a.
Proof.
  intros.
  destruct a as [a b].
  unfold join.
  unfold bot.
  unfold eq.
  rewrite -> A.join_bot.
  split; eauto || reflexivity.
Qed.
Hint Resolve join_bot.

Lemma join_top:
  forall a, join top a === top.
Proof.
  intros.
  destruct a as [a b].
  unfold join, bot, eq.
  simpl.
  rewrite -> A.join_top.
  split; eauto || reflexivity.
Qed.
Hint Resolve join_top.

Lemma meet_bot:
  forall a,
    meet bot a === bot.
Proof.
  intros.
  destruct a as [a b].
  unfold meet.
  unfold bot.
  unfold eq.
  rewrite -> A.meet_bot.
  split; eauto || reflexivity.
Qed.
Hint Resolve meet_bot.

Lemma meet_top:
  forall a, meet top a === a.
Proof.
  intros.
  destruct a as [a b].
  unfold meet, bot, eq.
  simpl.
  rewrite -> A.meet_top.
  split; eauto || reflexivity.
Qed.

Lemma implies_flowsto:
  forall a1 a2 b1 b2,
    LA.flowsto a1 a2 ->
    LB.flowsto b1 b2 ->
    (a1, b1) ⊑ (a2, b2).
Proof.
  intros.
  unfold flowsto.
  rewrite -> join_is_pairwise.
  eauto.
Qed.
Hint Resolve implies_flowsto.

Notation "⊥" := bot.
Notation "⊤" := top.

End ProductLattice.

(* An example lattice consisting of two points: L ⊑ H *)
Module LH <: Lattice.

Inductive LH :=
| L: LH
| H: LH.

Definition lattice := LH.

Definition eq := @eq lattice.

Lemma eq_equiv:
  equivalence _ eq.
Proof.
  constructor.
  - unfold reflexive, eq.
    intros; reflexivity.
  - unfold transitive, eq.
    intros; congruence.
  - unfold symmetric, eq.
    intros; symmetry; assumption.
Qed.

Instance eq_equiv_inst : Equivalence eq.
constructor; eapply eq_equiv.
Qed.

Definition meet (a b : LH) :=
  match a with
    | L => L
    | H => b
  end.

Definition join (a b : LH) :=
  match a with
  | L => b
  | H => H
  end.

Lemma meet_symmetry: forall a b : LH, meet a b = meet b a.
Proof.
  intros.
  unfold meet.
  case a; case b; auto.
Qed.

Lemma join_symmetry :forall a b : LH, join a b = join b a.
Proof.
  intros; unfold join. case a; case b; auto.
Qed.

Lemma join_assoc: forall a b c :LH , join a (join b c) = join ( join a b) c.
Proof.
  intros.
  unfold join.
  case a; case b; case c; auto.
Qed.

Lemma meet_assoc: forall a b c: LH, meet a (meet b c) = meet (meet a b) c.
Proof.
  intros.
  unfold join.
  case a; case b; case c; auto.
Qed.

Lemma meet_distrib: forall a b : LH, meet a (join a b) = a.
Proof.
  intros; case a; case b; auto.
Qed.

Lemma join_distrib: forall a b : LH, join a (meet a b) = a.
Proof.
  intros; case a; case b; auto.
Qed.

Definition flowsto a b := join a b = b.
Local Hint Unfold flowsto.
  
Notation "X ⊑ Y" := (flowsto X Y) (at level 70, no associativity).
Notation "X ⊔ Y" := (join X Y) (at level 20, left associativity).
Notation "X ⊓ Y" := (meet X Y) (at level 40, left associativity).

Lemma eq_dec: forall a b : LH, {a = b } + {a <> b}.
Proof.
  intros.
  destruct a; destruct b; eauto; right; congruence.
Qed.

Definition bot := L.
Definition top := H.

Lemma join_bot:
  forall a, join bot a = a.
Proof. reflexivity. Qed.
Hint Resolve join_bot.

Lemma join_top:
  forall a, join top a = top.
Proof. reflexivity. Qed.
Hint Resolve join_top.

Lemma meet_bot:
  forall a, meet bot a = bot.
Proof. reflexivity. Qed.
Hint Resolve meet_bot.

Lemma meet_top:
  forall a, meet top a = a.
Proof. reflexivity. Qed.
Hint Resolve meet_top.

Notation " x === y " := (eq x y) (at level 70, no associativity) : equiv_scope.
Notation " x =/= y " := (complement eq x y) (at level 70, no associativity) : equiv_scope.
Local Open Scope equiv_scope.

Lemma join_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊔ y1 === x2 ⊔ y2.
Proof. congruence. Qed.
  
Lemma meet_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊓ y1 === x2 ⊓ y2.
Proof. congruence. Qed.
  
Lemma flowsto_compat_right: forall x y z, x === y -> z ⊑ y -> z ⊑ x.
Proof. congruence. Qed.

Lemma flowsto_compat_left: forall x y z, x === y -> y ⊑ z -> x ⊑ z.
Proof. congruence. Qed.

Notation "⊥" := bot.
Notation "⊤" := top.

End LH.