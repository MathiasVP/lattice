Require Import Setoid Coq.Classes.Morphisms Basics List PeanoNat Coq.Logic.FinFun Coq.omega.Omega Psatz Coq.Sorting.Mergesort Coq.Structures.Orders Coq.Logic.FinFun Coq.Program.Equality dec.

Reserved Notation "X '⊓' Y" (at level 39, left associativity).
Reserved Notation "X '⊔' Y" (at level 40, left associativity).
Reserved Notation " x '===' y " (at level 70, no associativity).
Reserved Notation " x '=/=' y " (at level 70, no associativity).
Reserved Notation "⊤".
Reserved Notation "⊥".
Reserved Notation "X '⊑' Y" (at level 70, no associativity).

Class lattice (A : Set) :=
  Lattice {
      join: A -> A -> A where "X '⊔' Y" := (join X Y);
      meet: A -> A -> A where "X '⊓' Y" := (meet X Y);
      top: A where "⊤" := @top;
      bot: A where "⊥" := @bot;
      eq: A -> A -> Prop where "x '===' y" := (eq x y)
        and "x '=/=' y" := (complement eq x y)
        and "X '⊑' Y" := (X ⊔ Y === Y);
      eq_equiv :> Equivalence eq;
      meet_symmetry: forall a b : A, a ⊓ b === b ⊓ a;
      join_symmetry: forall a b   : A,  a ⊔ b === b ⊔ a;
      join_assoc   : forall a b c : A,  a ⊔ (b ⊔ c) === (a ⊔ b) ⊔ c;
      join_absorp : forall a b   : A,  a ⊔ (a ⊓ b) === a;
      meet_assoc   : forall a b c : A,  a ⊓ (b ⊓ c) === (a ⊓ b) ⊓ c;
      meet_absorp : forall a b   : A,  a ⊓ (a ⊔ b) === a;
      join_bot: forall a     : A, bot ⊔ a === a;
      join_top: forall a     : A, ⊤ ⊔ a === ⊤;
                               meet_bot: forall a     : A, bot ⊓ a === bot;
      meet_top: forall a     : A, ⊤ ⊓ a === a;
      join_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊔ y1 === x2 ⊔ y2;
      meet_compat: forall x1 y1 x2 y2, x1 === x2 -> y1 === y2 -> x1 ⊓ y1 === x2 ⊓ y2;
      flowsto_compat_right: forall x y z, x === y -> z ⊑ y -> z ⊑ x;
      flowsto_compat_left: forall x y z, x === y -> y ⊑ z -> x ⊑ z
    }.

Notation "X '⊓' Y" := (meet X Y)(at level 39, left associativity).
Notation "X '⊔' Y" := (join X Y) (at level 40, left associativity).
Notation "x '===' y" := (eq x y) (at level 70, no associativity).
Notation "x '=/=' y" := (complement eq x y) (at level 70, no associativity).
Notation "⊤" := top.
Notation "⊥" := bot.

Definition flowsto {A : Set} `{lattice A} (a b : A) := a ⊔ b === b.
Notation "X '⊑' Y" := (flowsto X Y) (at level 70, no associativity).

Arguments flowsto _ _ : simpl nomatch.
Arguments join _ _ : simpl nomatch.
Arguments meet _ _ : simpl nomatch.

Hint Resolve meet_symmetry join_symmetry join_assoc meet_assoc meet_absorp join_absorp join_top join_bot meet_top meet_bot eq_equiv.

Section LatticeProperties.
  Context {A : Set} `{lattice A}.

  Global Add Parametric Relation : A eq
      reflexivity proved by (@Equivalence_Reflexive A eq eq_equiv)
      symmetry proved by (@Equivalence_Symmetric A eq eq_equiv)
      transitivity proved by (@Equivalence_Transitive A eq eq_equiv)
        as eq_rel.
  Hint Resolve eq_rel : typeclass_instances.

  Class Morphism2 (f : A -> A -> A) :=
    {
      compat2: forall (x1 y1 x2 y2 : A), x1 === x2 -> y1 === y2 -> f x1 y1 === f x2 y2
    }.
  
  Class MorphismR (f : A -> A -> Prop) :=
    {
      compatR: forall (x1 y1 x2 y2 : A), x1 === x2 -> y1 === y2 -> f x1 y1 <-> f x2 y2
    }.
  
  Global Instance eq_rewrite2_Proper (f : A -> A -> A) `{Morphism2 f}:
    Proper (eq ==> eq ==> eq) f.
  Proof.
    intros x1 y1 H_eq1 x2 y2 H_eq2.
    eapply compat2; eassumption.
  Qed.
  Hint Resolve eq_rewrite2_Proper : typeclass_instances.

  Global Instance eq_rewrite3_Proper (f : A -> A -> Prop) `{MorphismR f}:
    Proper (eq ==> eq ==> flip impl) f.
  Proof.
    intros x1 y1 H_eq1 x2 y2 H_eq2.
    unfold flip.
    intro.
    eapply compatR; eassumption.
  Qed.
  Hint Resolve eq_rewrite3_Proper : typeclass_instances.

  Global Instance join_inst: Morphism2 join := { compat2 := join_compat }.
  Global Instance meet_inst: Morphism2 meet := { compat2 := meet_compat }.
  Hint Resolve join_inst : typeclass_instances.
  Hint Resolve meet_inst : typeclass_instances.

  Lemma idem_join:
    forall a, a ⊔ a === a.
  Proof.
    intros.
    rewrite <- (meet_absorp a a) at 2.
    eauto.
  Qed.
  Hint Resolve idem_join.
  
  Lemma idem_meet:
    forall a, a ⊓ a === a.
  Proof.
    intros.
    rewrite <- (join_absorp a a) at 2.
    eauto.
  Qed.
  Hint Resolve idem_meet.

  Lemma flowsto_refl: forall a, a ⊑ a.
  Proof. unfold flowsto. eauto. Qed.
  Hint Resolve flowsto_refl.

  Global Instance flowsto_Proper: forall (a : A), Proper (flowsto --> flip impl) (flowsto a).
  Proof.
    intros.
    intros x y ? ?.
    unfold flowsto in *.
    unfold flip in *.
    rewrite <- H0.
    rewrite -> join_assoc.
    rewrite -> H1.
    reflexivity.
  Qed.

  Lemma flowsto_trans:
    forall a b c, a ⊑ b -> b ⊑ c -> a ⊑ c.
  Proof.
    intros.
    rewrite <- H1.
    assumption.
  Qed.

  Global Instance flowsto_preorder_inst: PreOrder flowsto.
  constructor.
  - eauto.
  - unfold Transitive.
    intros.
    eauto using flowsto_trans.
  Defined.
  Hint Resolve flowsto_preorder_inst : typeclass_instances.
  
  Add Parametric Relation: A flowsto
      reflexivity proved by flowsto_refl
      transitivity proved by flowsto_trans
        as flowsto_rel.

  Hint Extern 1 (?a ⊑ ?c) =>
  match goal with
  | [H: a ⊑ ?b |- _] => apply (flowsto_trans a b c)
  | [H: ?b ⊑ c |- _] => apply (flowsto_trans a b c)
  end.

  Lemma anti_sym:
    forall a b, a ⊑ b -> b ⊑ a -> a === b.
  Proof.
    intros a b H1 H2.
    unfold flowsto in *.
    rewrite <- H1.
    rewrite -> join_symmetry.
    rewrite -> H2.
    reflexivity.
  Qed.

  Lemma flowsto_not:
    forall ℓ₁ ℓ₂ ℓ₃, ℓ₁ ⊑ ℓ₂ -> not (ℓ₁ ⊑ ℓ₃) -> not (ℓ₂ ⊑ ℓ₃).
  Proof.
    intros ℓ₁ ℓ₂ ℓ₃ H1 H2.
    intro H_absurd.
    contradiction (flowsto_trans _ _ _ H1 H_absurd).
  Qed.
  Hint Resolve flowsto_not.

  Lemma flowsto_join:
    forall a b, a ⊑ a ⊔ b.
  Proof.
    intros.
    unfold flowsto.
    rewrite -> join_assoc.
    rewrite -> idem_join.
    reflexivity.
  Qed.
  Hint Resolve flowsto_join.

  Lemma meet_join_consistent:
    forall a b, a ⊓ b === a <-> a ⊔ b === b.
  Proof.
    intros.
    split; intros.
    - assert (b === b ⊔ (b ⊓ a)).
      {
        rewrite -> (join_absorp b a).
        reflexivity.
      }
      assert (b ⊔ (b ⊓ a) === b ⊔ a).
      {
        rewrite -> meet_symmetry.
        rewrite -> H0.
        reflexivity.
      }
      rewrite -> join_symmetry.
      rewrite <- H2.
      rewrite <- H1.
      reflexivity.
    - assert (a === a ⊓ (a ⊔ b)).
      {
        rewrite -> (meet_absorp a b).
        reflexivity.
      }
      assert (a ⊓ (a ⊔ b) === a ⊓ b).
      {
        rewrite -> H0.
        reflexivity.
      }
      rewrite <- H2.
      symmetry.
      assumption.
  Qed.

  Global Instance flowsto_proper_join: Proper (flowsto ==> flowsto ==> flowsto) join.
  Proof.
    intros x y ? z ? ?.
    unfold flowsto in *.
    rewrite -> join_assoc.
    rewrite <- (join_symmetry z x).
    rewrite <- (join_assoc z x y).
    rewrite -> H0.
    rewrite -> (join_symmetry z y).
    rewrite <- join_assoc.
    rewrite -> H1.
    reflexivity.
  Qed.  
  Hint Resolve flowsto_proper_join : typeclass_instances.

  Global Instance flowsto_proper_meet: Proper (flowsto ==> flowsto ==> flowsto) meet.
  Proof.
    intros x y ? z ? ?.
    unfold flowsto in *.
    rewrite <- meet_join_consistent in *.
    rewrite -> meet_assoc.
    rewrite <- (meet_symmetry z x).
    rewrite <- (meet_assoc z x y).
    rewrite -> H0.
    rewrite -> (meet_symmetry z x).
    rewrite <- meet_assoc.
    rewrite -> H1.
    reflexivity.
  Qed.  
  Hint Resolve flowsto_proper_meet : typeclass_instances.

  Lemma flowsto_meet:
    forall a b, a ⊓ b ⊑ a.
  Proof.
    intros.
    unfold flowsto.
    rewrite -> meet_symmetry.
    rewrite <- meet_join_consistent.
    rewrite <- meet_assoc.
    rewrite -> idem_meet.
    reflexivity.
  Qed.
  Hint Resolve flowsto_meet.

  Class MorphismUR (f : A -> Prop) :=
    {
      compatUR: forall (x y : A), x === y -> f y <-> f x
    }.
  
  Global Instance eq_rewrite4_Proper (f : A -> Prop) `{MorphismUR f}:
    Proper (eq ==> flip impl) f.
  Proof.
    firstorder.
  Qed.
  Hint Resolve eq_rewrite4_Proper : typeclass_instances.

  Global Instance flowsto_inst: MorphismR (fun a b => a ⊔ b === b).
  Proof.
    constructor.
    intros.
    split; intros.
    - symmetry in H0.
      eapply (flowsto_compat_right y2 y1 x2); eauto.
      firstorder.
      symmetry in H1.
      eapply (flowsto_compat_left x2 x1 y1); eauto.
    - symmetry in H1.
      eapply (flowsto_compat_left x1 x2 y1); eauto.
      symmetry in H1.
      eapply (flowsto_compat_right y1 y2 x2); eauto.
  Qed.
  Hint Resolve flowsto_inst : typeclass_instances.

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
      ℓ₁ ⊑ ℓ₂ ⊓ ℓ₃ -> ℓ₁ ⊑ ℓ₂ /\ ℓ₁ ⊑ ℓ₃.
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
    forall a b c, ~ a ⊑ c -> ~ b ⊑ c -> ~ a ⊔ b ⊑ c.
  Proof.
    intros.
    intro.
    rewrite <- H2 in *.
    contradiction H0.
    eauto.
  Qed.

  Lemma implies_join_flowsto:
    forall a b c, a ⊑ c -> b ⊑ c -> a ⊔ b ⊑ c.
  Proof.
    intros.
    unfold flowsto in *.
    rewrite <- join_assoc.
    rewrite -> H1.
    assumption.
  Qed.
  Hint Resolve implies_join_flowsto.

  Lemma implies_meet_flowsto:
    forall c a b, c ⊑ a -> c ⊑ b -> c ⊑ a ⊓ b.
  Proof.
    intros.
    eapply meet_join_consistent in H0.
    eapply meet_join_consistent in H1.
    rewrite <- H0.
    rewrite <- H1.
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
    forall a b c, a ⊑ b -> a ⊑ b ⊔ c.
  Proof.
    intros.
    unfold flowsto in *.
    rewrite -> join_assoc.
    rewrite -> H0.
    reflexivity.
  Qed.
  Hint Resolve join_is_increasing.

  Lemma meet_is_decreasing:
    forall a b c, a ⊑ b -> a ⊓ c ⊑ b.
  Proof.
    intros.
    eapply meet_join_consistent.
    eapply meet_join_consistent in H0.
    rewrite <- meet_assoc.
    rewrite -> (meet_symmetry c b).
    rewrite -> meet_assoc.
    rewrite -> H0.
    reflexivity.
  Qed.
  Hint Resolve meet_is_decreasing.

  Lemma top_is_top:
    forall a, a ⊑ ⊤.
  Proof.
    intros.
    unfold flowsto in *.
    rewrite <- join_symmetry.
    eauto.
  Qed.
  Hint Resolve top_is_top.

  Lemma flowsto_top_is_top:
    forall a, ⊤ ⊑ a -> a === ⊤.
  Proof.
    intros a H_flows.
    unfold flowsto in *.
    rewrite -> join_top in H_flows.
    symmetry.
    assumption.
  Qed.
  Hint Resolve flowsto_top_is_top.

  Lemma bot_flowsto_is_bot:
    forall a, a ⊑ ⊥ -> a === ⊥.
  Proof.
    intros a H_flows.
    unfold flowsto in *.
    rewrite -> join_symmetry in H_flows.
    rewrite -> join_bot in H_flows.
    assumption.
  Qed.
  Hint Resolve bot_flowsto_is_bot.

  Lemma flowsto_dec:
    is_dec_rel eq -> forall a b, { a ⊑ b } + { ~ (a ⊑ b) }.
  Proof.
    intros.
    eapply H0.
  Qed.

End LatticeProperties.

Section ProductLattice.

  Context {A B : Set} `{lattice A} `{lattice B}.
  
  Definition eq_prod (ab1 ab2 : A * B) : Prop :=
    match ab1, ab2 with
      (a1, b1), (a2, b2) => a1 === a2 /\ b1 === b2
    end.
  Local Hint Unfold eq_prod.
  
  Lemma eq_prod_equiv:
    @Equivalence (A * B) eq_prod.
  Proof.
    unfold equiv.
    constructor.
    - unfold Reflexive.
      intros.
      destruct x as [a b].
      unfold eq.
      split; reflexivity.
    - unfold symmetric.
      intros [a1 b1] [a2 b2].
      intros [H1 H2].
      symmetry in H1.
      symmetry in H2.
      split; assumption.
    - intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4]. 
      split.
      + rewrite -> H1; assumption.
      + rewrite -> H2; assumption.
  Qed.

  Definition meet_prod (x y : A * B) :=
    match x, y with
      (a1, b1), (a2, b2) => (a1 ⊓ a2, b1 ⊓ b2)
    end.

  Definition join_prod (x y : A * B) :=
    match x, y with
      (a1, b1), (a2, b2) => (a1 ⊔ a2, b1 ⊔ b2)
    end.
  Local Hint Unfold meet_prod join_prod.
  
  Global Instance product_lattice: lattice (A * B).
  eapply (Lattice _ join_prod meet_prod (⊤, ⊤) (⊥, ⊥) eq_prod).
  - eapply eq_prod_equiv.
  - intros [a1 b1] [a2 b2].
    simpl.
    split; eauto.
  - intros [a1 b1] [a2 b2].
    simpl.
    split; eauto.
  - intros [a1 b1] [a2 b2] [a3 b3].
    split; eauto.
  - intros [a1 b1] [a2 b2].
    split; eauto.
  - intros [a1 b1] [a2 b2] [a3 b3].
    split; eauto.
  - intros [a1 b1] [a2 b2].
    split; eauto.
  - intros [a b].
    split; eauto.
  - intros [a b].
    split; eauto.
  - intros [a b].
    split; eauto.
  - intros [a b].
    split; eauto.
  - intros [a1 b1] [a2 b2] [a3 b3] [a4 b4] [H1 H2] [H3 H4].
    unfold eq_prod, join_prod.
    rewrite -> H1.
    rewrite -> H3.
    rewrite -> H2.
    rewrite -> H4.
    split; reflexivity.
  - intros [a1 b1] [a2 b2] [a3 b3] [a4 b4] [H1 H2] [H3 H4].
    simpl.
    rewrite -> H1.
    rewrite -> H3.
    rewrite -> H2.
    rewrite -> H4.
    split; reflexivity.
  - intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4].
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    rewrite -> H3.
    rewrite -> H4.
    split; reflexivity.
  - intros [a1 b1] [a2 b2] [a3 b3] [H1 H2] [H3 H4].
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    rewrite -> H3.
    rewrite -> H4.
    split; reflexivity.
  Defined.
  Hint Resolve product_lattice : typeclass_instances.

End ProductLattice.

(* An example lattice consisting of two points: L ⊑ H *)
Section LHLattice.

  Inductive LH :=
  | L: LH
  | H: LH.

  Definition meet_LH (a b : LH) :=
    match a with
    | L => L
    | H => b
    end.

  Definition join_LH (a b : LH) :=
    match a with
    | L => b
    | H => H
    end.

  Global Instance LH_lattice : lattice LH.
  Proof.
    eapply (Lattice LH join_LH meet_LH H L Logic.eq).
    - eapply eq_equivalence.
    - intros. destruct a; destruct b; reflexivity.
    - intros. destruct a; destruct b; reflexivity.
    - intros. destruct a; destruct b; destruct c; reflexivity.
    - intros a b; destruct a; destruct b; reflexivity.
    - intros a b c. destruct a; destruct b; destruct c; reflexivity.
    - intros a b. destruct a; destruct b; reflexivity.
    - constructor.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
  Defined.
  Hint Resolve LH_lattice : typeclass_instances.

End LHLattice.

Section FunLattice.

  Context {A B : Set} `{lattice B}.

  Definition fun_lattice_eq (f g : A -> B) :=
    forall (x : A), f x === g x.
  Local Hint Unfold fun_lattice_eq.

  Definition fun_lattice_join (f g : A -> B): A -> B :=
    fun x => f x ⊔ g x.
  Local Hint Unfold fun_lattice_join.

  Definition fun_lattice_meet (f g : A -> B): A -> B :=
    fun x => f x ⊓ g x.
  Local Hint Unfold fun_lattice_meet.

  Global Instance fun_lattice: lattice (A -> B).
  intros.
  eapply (Lattice (A -> B) fun_lattice_join fun_lattice_meet (fun _ => ⊤) (fun _ => ⊥) fun_lattice_eq).
  - constructor.
    + intros f x.
      reflexivity.
    + intros f g H.
      intro x.
      symmetry.
      eauto.
    + intros f g h ? ? x.
      transitivity (g x); eauto.
  - intros.
    intro x.
    unfold fun_lattice_meet.
    eauto.
  - intros f g x.
    unfold fun_lattice_join.
    eauto.
  - intros f g h.
    unfold fun_lattice_join.
    eauto.
  - intros f g h.
    unfold fun_lattice_join, fun_lattice_meet.
    eauto.
  - intros f g h.
    unfold fun_lattice_meet.
    eauto.
  - intros f g h.
    unfold fun_lattice_join, fun_lattice_meet.
    eauto.
  - intros.
    unfold fun_lattice_join.
    eauto.
  - intros.
    unfold fun_lattice_join.
    eauto.
  - intros.
    unfold fun_lattice_meet.
    eauto.
  - intros.
    unfold fun_lattice_meet.
    eauto.
  - intros.
    intros.
    unfold fun_lattice_join.
    intro.
    rewrite -> join_compat by eauto.
    reflexivity.
  - intros.
    intros.
    unfold fun_lattice_meet.
    intro.
    rewrite -> meet_compat by eauto.
    reflexivity.
  - intros.
    unfold fun_lattice_join.
    intro.
    rewrite -> flowsto_compat_right by eauto.
    reflexivity.
  - intros.
    unfold fun_lattice_join.
    intro.
    rewrite -> flowsto_compat_left by eauto.
    reflexivity.
  Defined.
  Hint Resolve fun_lattice : typeclass_instances.

End FunLattice.

Section DistributiveLattice.

  Context {A : Set}.

  Class distr_lattice (A : Set) :=
    DistrLattice {
        is_lattice :> lattice A;
        distr_meet_join: forall a b c, a ⊓ (b ⊔ c) === (a ⊓ b) ⊔ (a ⊓ c)
      }.

  Context `{distr_lattice A}.

  Lemma distr_join_meet:
    forall (a b c : A),
      a ⊔ (b ⊓ c) === (a ⊔ b) ⊓ (a ⊔ c).
  Proof.
    intros.
    rewrite -> distr_meet_join.
    rewrite -> (meet_symmetry _ a).
    rewrite -> meet_absorp.
    rewrite -> (meet_symmetry (a ⊔ b)).
    rewrite -> distr_meet_join.
    rewrite -> join_assoc.
    rewrite -> (meet_symmetry c).
    rewrite -> join_absorp.
    rewrite -> meet_symmetry.
    reflexivity.
  Qed.
  
  Lemma distr_meet_join_right:
    forall (a b c : A), (b ⊔ c) ⊓ a === (b ⊓ a) ⊔ (c ⊓ a).
  Proof.
    intros.
    rewrite -> meet_symmetry.
    rewrite -> (meet_symmetry b).
    rewrite -> (meet_symmetry c).
    eapply distr_meet_join.
  Qed.

  Lemma distr_join_meet_right:
    forall (a b c : A),
      (b ⊓ c) ⊔ a === (b ⊔ a) ⊓ (c ⊔ a).
  Proof.
    intros.
    rewrite -> join_symmetry.
    rewrite -> (join_symmetry b).
    rewrite -> (join_symmetry c).
    eapply distr_join_meet.
  Qed.

  Global Instance LH_distr_lattice : distr_lattice LH.
  Proof.
    econstructor.
    intros.
    destruct a; destruct b; destruct c; reflexivity.
  Qed.

  Lemma modular:
    forall (a b x : A),
      a ⊑ b -> a ⊔ (x ⊓ b) === (a ⊔ x) ⊓ b.
  Proof.
    intros.
    rewrite -> distr_meet_join_right.
    unfold flowsto in H1.
    eapply meet_join_consistent in H1.
    rewrite -> H1.
    reflexivity.
  Qed.

End DistributiveLattice.

Section WordLattice.
  Context {A D : Set}.
  
  Inductive Word :=
    Var: D -> Word
  | Lit: A -> Word
  | Join: Word -> Word -> Word
  | Meet: Word -> Word -> Word.
  Hint Constructors Word.

  Reserved Notation "'〚' x '〛' f" (at level 30, f at next level).

  Fixpoint eval `{lattice A} (f : D -> A) (x : Word) : A :=
    match x with
      Var n => f n
    | Lit a => a
    | Join x y => 〚x〛f ⊔ 〚y〛f
    | Meet x y => 〚x〛f ⊓ 〚y〛f
    end
  where "'〚' x '〛' f" := (eval f x).

  Definition eq_word `{lattice A} (x y : Word) :=
    forall (f : D -> A), 〚x〛f === 〚y〛f.
  Local Hint Unfold eq_word.

  Infix "≡" := eq_word (at level 70, no associativity).

  Definition join_word (x y : Word) := Join x y.
  Definition meet_word (x y : Word) := Meet x y.

  Infix "∪" := Join (at level 40, left associativity).
  Infix "∩" := Meet (at level 40, left associativity).

  Definition flowsto_word `{lattice A} (x y : Word) :=
    x ∪ y ≡ y.
  Hint Unfold flowsto_word.

  Infix "⊆" := (flowsto_word) (at level 70, no associativity).

  Lemma monotonicity `{lattice A}:
    forall (f1 f2 : D -> A) w,
      f1 ⊑ f2 ->
      〚w〛f1 ⊑ 〚w〛f2.
  Proof.
    intros.
    induction w.
    - simpl.
      eapply H1.
    - reflexivity.
    - simpl.
      rewrite -> IHw1.
      rewrite -> IHw2.
      reflexivity.
    - simpl.
      rewrite -> IHw1.
      rewrite -> IHw2.
      reflexivity.
  Qed.

  Lemma join_monotonicity `{distr_lattice A}:
    forall (f1 f2 : D -> A) w,
      〚w〛f1 ⊔〚w〛f2 ⊑ 〚w〛(f1 ⊔ f2).
  Proof.
    intros.  
    induction w.
    - simpl.
      unfold fun_lattice_join.
      reflexivity.
    - simpl.
      rewrite -> idem_join.
      reflexivity.
    - simpl.
      rewrite <- IHw1.
      rewrite <- IHw2.
      rewrite -> (join_symmetry (〚 w1 〛 f2) (〚 w2 〛 f2)).
      rewrite <- join_assoc.
      rewrite -> (join_assoc (〚 w2 〛 f1) (〚 w2 〛 f2) (〚 w1 〛 f2)).
      rewrite -> (join_symmetry (〚 w2 〛 f1 ⊔ 〚 w2 〛 f2) (〚 w1 〛 f2)).
      rewrite -> join_assoc.
      reflexivity.
    - simpl.
      rewrite <- IHw1.
      rewrite <- IHw2.
      rewrite -> distr_meet_join, distr_meet_join_right, distr_meet_join_right.
      repeat rewrite <- join_assoc.
      rewrite -> (join_symmetry (〚 w1 〛 f1 ⊓ 〚 w2 〛 f2)).
      rewrite -> (join_symmetry (〚 w1 〛 f2 ⊓ 〚 w2 〛 f1)).
      repeat rewrite -> join_assoc.
      do 2 eapply join_is_increasing.
      reflexivity.
  Qed.

  Lemma meet_monotonicity `{distr_lattice A}:
    forall (f1 f2 : D -> A) w,
      〚w〛(f1 ⊓ f2) ⊑ 〚w〛f1 ⊓〚w〛f2.
  Proof.
    intros.  
    induction w.
    - simpl.
      unfold fun_lattice_meet.
      reflexivity.
    - simpl.
      rewrite -> idem_meet.
      reflexivity.
    - simpl.
      replace fun_lattice_meet with (@meet (D -> A) _) by reflexivity.
      rewrite -> distr_meet_join, distr_meet_join_right, distr_meet_join_right.    
      rewrite -> IHw1.
      rewrite <- IHw2.
      repeat rewrite <- join_assoc.
      rewrite -> (join_symmetry (〚 w1 〛 f1 ⊓ 〚 w2 〛 f2)).
      rewrite -> (join_assoc (〚 w2 〛 f1 ⊓ 〚 w1 〛 f2)).
      rewrite -> (join_symmetry (〚 w2 〛 f1 ⊓ 〚 w1 〛 f2)).
      repeat rewrite -> join_assoc.
      do 2 eapply join_is_increasing.
      reflexivity.
    - simpl.
      replace fun_lattice_meet with (@meet (D -> A) _) by reflexivity.
      rewrite -> IHw1.
      rewrite -> IHw2.
      repeat rewrite <- meet_assoc.
      rewrite -> (meet_assoc (〚 w2 〛 f1)).
      rewrite -> (meet_symmetry (〚 w2 〛 f1) (〚 w1 〛 f2)).
      repeat rewrite -> meet_assoc.
      reflexivity.
  Qed.

  Global Instance eq_words_eq `{lattice A}: Equivalence eq_word.
  Proof.
    constructor.
    - intros x f.
      reflexivity.
    - intros x y ? f.
      symmetry.
      eauto.
    - intros x y z ? ? f.
      transitivity (〚y〛f); eauto.
  Qed.

  Global Instance flowsto_word_preorder `{lattice A}: PreOrder flowsto_word.
  Proof.
    constructor.
    - intro.
      intro f.
      simpl.
      rewrite -> idem_join.
      reflexivity.
    - intros x y z ? ? f.
      specialize (H1 f).
      specialize (H2 f).
      simpl in *.
      rewrite <- H2.
      rewrite -> join_assoc.
      rewrite -> H1.
      reflexivity.
  Qed.

  Lemma meet_flowsto_word `{lattice A}:
    forall (w1 w2 : Word),
      w1 ∩ w2 ⊆ w1.
  Proof.
    intros.
    intros ?.
    simpl in *.
    rewrite -> join_symmetry.
    rewrite -> join_absorp.
    reflexivity.
  Qed.
  Hint Resolve meet_flowsto_word.

  Lemma join_flowsto_word `{lattice A}:
    forall (w1 w2 : Word),
      w1 ⊆ w1 ∪ w2.
  Proof.
    intros.
    intros ?.
    simpl in *.
    rewrite -> join_assoc.
    rewrite -> idem_join.
    reflexivity.
  Qed.
  Hint Resolve join_flowsto_word.

  Lemma meet_symmetry_word `{lattice A}:
    forall (w1 w2 : Word),
      w1 ∩ w2 ≡ w2 ∩ w1.
  Proof.
    intros.
    intro f.
    simpl.
    eauto.
  Qed.

  Lemma join_symmetry_word `{lattice A}:
    forall (w1 w2 : Word),
      w1 ∪ w2 ≡ w2 ∪ w1.
  Proof.
    intros.
    intro f.
    simpl.
    eauto.
  Qed.

  Global Instance proper_eq_word_flowsto `{lattice A}:
    Proper (eq_word ==> eq_word ==> flip impl) flowsto_word.
  Proof.
    intros x y ? z w ? ?.  
    intro.
    specialize (H1 f).
    specialize (H2 f).
    specialize (H3 f).
    simpl in *.
    rewrite -> H1.
    rewrite -> H2.
    assumption.
  Qed.
  Hint Resolve proper_eq_word_flowsto : typeclass_instances.

  Global Instance eval_preserves_eq_proper `{lattice A} (f: D -> A):
    Proper (eq_word ==> eq) (eval f).
  Proof.
    intros x y ?.
    eapply H1.
  Defined.
  Hint Resolve eval_preserves_eq_proper : typeclass_instances.

  Global Instance join_preserves_eq_word `{lattice A}:
    Proper (eq_word ==> eq_word ==> eq_word) Join.
  Proof.
    intros x1 x2 ? y1 y2 ? f.
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
  Defined.

  Global Instance meet_preserves_eq_word `{lattice A}:
    Proper (eq_word ==> eq_word ==> eq_word) Meet.
  Proof.
    intros x1 x2 ? y1 y2 ? f.
    simpl.
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
  Defined.

  Hint Resolve join_preserves_eq_word meet_preserves_eq_word : typeclass_instances.

  Instance word_lattice `{lattice A} : lattice Word.
  Proof.
    econstructor.
    - eapply eq_words_eq.
    - eapply meet_symmetry_word.
    - eapply join_symmetry_word.
    - intros.
      intro.
      simpl.    
      eapply join_assoc.
    - intros.
      intro.
      simpl.
      eapply join_absorp.
    - intros.
      intro.
      simpl.
      eapply meet_assoc.
    - intros.
      intro.
      eapply meet_absorp.
    - intros.
      instantiate (1 := Lit bot).
      intro.
      simpl.
      eapply join_bot.
    - intros.
      instantiate (1 := Lit top).
      intro.
      simpl.
      eapply join_top.
    - intros.
      intro.
      simpl.
      eapply meet_bot.
    - intros.
      intro.
      simpl.
      eapply meet_top.
    - intros.
      intro.
      simpl.
      rewrite -> H1.
      rewrite -> H2.
      reflexivity.
    - intros.
      intro.
      simpl.
      rewrite -> H1.
      rewrite -> H2.
      reflexivity.
    - intros.
      rewrite -> H1.
      assumption.
    - intros.
      rewrite -> H1.
      assumption.
  Qed.    

End WordLattice.