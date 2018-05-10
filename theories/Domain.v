Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega.

Require Import GrappaCoq.Set GrappaCoq.Topology.
Open Scope set_scope.

(** Domain theory *)


(** Partial orders. We don't require antisymmetry wrt definitional
    equality, only equivalence. But we define the equivalence relation
    as the symmetric closure of the order relation, so we have our
    antisymmetry for free. *)
Section poset.
  Context {X : Type}.

  Class PosetOrder : Type :=
    le : X -> X -> Prop.

  Notation "a '⊑' b" := (le a b) (at level 65) : domain_scope.
  Open Scope domain_scope.

  Definition equiv {P : PosetOrder} (x y : X) :=
    x ⊑ y /\ y ⊑ x.

  Notation "a '~~' b" := (equiv a b) (at level 65) : domain_scope.

  Class Poset (order : PosetOrder) : Prop :=
    { reflAxiom : forall x, x ⊑ x;
      transAxiom : forall x y z, x ⊑ y -> y ⊑ z -> x ⊑ z }.

  Class Bottom : Type :=
    bot : X.

  Notation "⊥" := bot : domain_scope.

  Definition bottomAxiom {P : PosetOrder} {B : Bottom} := 
    forall x, ⊥ ⊑ x.

  Class PointedPoset `(P : Poset) (bot : Bottom) : Prop :=
    botAxiom : bottomAxiom.
End poset.

Notation "a '⊑' b" := (le a b) (at level 65) : domain_scope.
Notation "a '~~' b" := (equiv a b) (at level 65) : domain_scope.
Notation "⊥" := bot : domain_scope.
Open Scope domain_scope.


Section posetDefinitions.
  Context {X : Type} `{P : Poset X}.

  Definition lt (x y : X) :=
    ~ (x ~~ y) /\ x ⊑ y.
  Notation "a '⊏' b" := (lt a b) (at level 65) : domain_scope.

  Definition upper_set (A : set X) :=
    fun y => exists x, x ∈ A /\ x ⊑ y.

  Definition lower_set (A : set X) :=
    fun x => exists y, y ∈ A /\ x ⊑ y.

  Definition is_upper_set (A : set X) :=
    forall x y, x ⊑ y -> x ∈ A -> y ∈ A.

  Definition is_lower_set (A : set X) :=
    forall x y, x ⊑ y -> y ∈ A -> x ∈ A.

  Definition upper_set_single (x : X) :=
    upper_set (singleton x).

  Definition lower_set_single (x : X) :=
    lower_set (singleton x).

  Definition upper_bound (x : X) (A : set X) :=
    forall y, y ∈ A -> y ⊑ x.

  Definition lower_bound (x : X) (A : set X) :=
    forall y, y ∈ A -> x ⊑ y.

  (* The set of all upper bounds of A *)
  Definition ub (A : set X) :=
    fun x => upper_bound x A.

  (* The set of all lower bounds of A *)
  Definition lb (A : set X) :=
    fun x => lower_bound x A.

  Definition maximal (x : X) (A : set X) :=
    x ∈ A /\ ~ exists y, x <> y /\ y ∈ A /\ x ⊑ y.

  Definition minimal (x : X) (A : set X) :=
    x ∈ A /\ ~ exists y, x <> y /\ y ∈ A /\ y ⊑ x.

  Definition minimal_upper_bound (x : X) (A : set X) :=
    minimal x (ub A).

  Definition maximal_lower_bound (x : X) (A : set X) :=
    maximal x (lb A).

  Definition mub (x : X) (A : set X) :=
    fun x => minimal_upper_bound x A.

  Definition mlb (x : X) (A : set X) :=
    fun x => maximal_lower_bound x A.

  Definition largest (x : X) (A : set X) :=
    x ∈ A /\ forall y, y ∈ A -> y ⊑ x.

  Definition least (x : X) (A : set X) :=
    x ∈ A /\ forall y, y ∈ A -> x ⊑ y.

  Definition no_least (A : set X) :=
    forall x, x ∈ A -> exists y, y ∈ A /\ y ⊏ x.

  Definition is_supremum (x : X) (A : set X) :=
    least x (ub A).
  Notation is_join := is_supremum.

  Definition is_infimum (x : X) (A : set X) :=
    largest x (lb A).
  Notation is_meet := is_infimum.

  Definition is_complete_lattice :=
    forall A : set X, exists sup inf, is_supremum sup A /\ is_infimum inf A.

  Definition without_least (A : set X) :=
    fun x => x ∈ A /\ exists y, y ∈ A /\ y ⊏ x.
End posetDefinitions.

Notation "a '⊏' b" := (lt a b) (at level 65) : domain_scope.


Section posetLemmas.
  Context {X : Type} `{P : Poset X}.

  Lemma is_upper_set_upper_set (A : set X) :
    is_upper_set (upper_set A).
  Proof. firstorder. Qed.

  Lemma is_lower_set_lower_set (A : set X) :
    is_lower_set (lower_set A).
  Proof. firstorder. Qed.

  Lemma subset_sup_le (A B : set X) (supA supB : X) :
    is_supremum supA A ->
    is_supremum supB B ->
    A ⊆ B ->
    supA ⊑ supB.
  Proof.
    intros H0 H1 H2.
    destruct H0 as [H0 H0']; destruct H1 as [H1 H1'].
    apply H0'; firstorder.
  Qed.

  Lemma subset_inf_le (A B : set X) (infA infB : X) :
    is_infimum infA A ->
    is_infimum infB B ->
    A ⊆ B ->
    infB ⊑ infA.
  Proof.
    intros H0 H1 H2.
    destruct H0 as [H0 H0']; destruct H1 as [H1 H1'].
    apply H0'; firstorder.
  Qed.

  Lemma supremum_lower (A : set X) (x : X) :
    is_supremum x A <-> is_supremum x (lower_set A).
  Proof.
    split; intros [? H0]; split;
      try (intros ? ?; apply H0; firstorder); firstorder.
  Qed.

  Lemma supremum_lower' (A : set X) (x y : X) :
    is_supremum x A ->
    is_supremum y (lower_set A) ->
    x ~~ y.
  Proof. intros H ?; apply supremum_lower in H; firstorder. Qed.

  Lemma infimum_upper (A : set X) (x : X) :
    is_infimum x A <-> is_infimum x (upper_set A).
  Proof.
    split; intros [? H0]; split;
      try (intros ? ?; apply H0; firstorder); firstorder.
  Qed.

  Lemma not_least_no_least (A : set X) :
    no_least A -> (~ exists x, least x A).
  Proof. firstorder. Qed.

  Lemma least_not_no_least (A : set X) :
    (exists x, least x A) -> ~ no_least A.
  Proof. firstorder. Qed.

  Lemma no_least_without_least (A : set X) :
    (forall a b, a ∈ A -> b ∈ A -> a ⊏ b -> exists c, c ∈ A /\ a ⊏ c /\ c ⊏ b) ->
    no_least (without_least A).
  Proof.
    intros H0 x [H1 (y & H2 & H3)].
    specialize (H0 y x H2 H1 H3).
    destruct H0 as (c & H4 & H5 & H6).
    exists c; split; auto; split; auto.
    exists y; split; auto.
  Qed.

  Lemma nonempty_upper_supremum_in_set (A : set X) :
    nonempty A ->
    is_upper_set A ->
    forall a, is_supremum a A -> a ∈ A.
  Proof.
    intros Hne Hupper a [H0 H1].
    destruct Hne as [x Hne].
    apply Hupper with x; firstorder.
  Qed.
End posetLemmas.


Section pointedPosetLemmas.
  Context {X : Type} `{P : PointedPoset X}.

  Lemma bot_least : least ⊥ (@full X).
  Proof. firstorder. Qed.
End pointedPosetLemmas.


Notation "'val' x" := (proj1_sig x) (at level 10).


Section directed.
  Context {X : Type} `{P : Poset X}.

  Definition directed (A : set X) :=
    nonempty A /\
    forall x y, x ∈ A -> y ∈ A -> exists a, a ∈ A /\ upper_bound a (doubleton x y).
  Definition directed_set := { A : set X | directed A }.
End directed.


Section monotone.
  Context {X Y : Type} `{P : Poset X} `{Q : Poset Y}.
  Variable f : X -> Y.

  Definition monotone := forall x y, x ⊑ y -> f x ⊑ f y.
  Definition image (A : set X) :=
    fun y => exists x, x ∈ A /\ f x ~~ y.
End monotone.


Section continuous.
  Context {X Y : Type} `{P : Poset X} `{Q : Poset Y}.
  Variable f : X -> Y.

  Definition scott_continuous :=
    forall A x, directed A -> is_supremum x A -> is_supremum (f x) (image f A).
End continuous.


Section monotoneLemmas.
  Context {X Y : Type} `{P : Poset X} `{Q : Poset Y}.
  Variable f : X -> Y.
  Lemma monotone_upper_preimage (V : set Y) :
    monotone f -> is_upper_set V -> is_upper_set (preimage f V).
  Proof. firstorder. Qed.

  Lemma monotone_directed_image (A : set X) :
    monotone f -> directed A -> directed (image f A).
  Proof.
    intros Hmono [H0 H1].
    unfold directed in *. split.
    - destruct H0 as [x Hx]; exists (f x); firstorder.
    - intros x y (x0 & Hx0 & Hx1) (y0 & Hy0 & Hy1).
      specialize (H1 x0 y0 Hx0 Hy0).
      destruct H1 as (a & H1 & H2).
      exists (f a). split.
      + firstorder.
      + destruct Q as [_ transAx].
        intros b [? | ?]; subst.
        destruct Hx1 as [_ ?]; eapply transAx; eauto; firstorder.
        destruct Hy1 as [_ ?]; eapply transAx; eauto; firstorder.
  Qed.
End monotoneLemmas.


Section continuousLemmas.
  Context {X Y : Type} `{P : Poset X} `{Q : Poset Y}.
  Variable f : X -> Y.

  Lemma scott_continuous_monotone :
    scott_continuous f -> monotone f.
  Proof.
    intros H0 x y H1.
    specialize (H0 (doubleton x y) y).
    assert (H2: forall y0 : X, doubleton x y y0 -> y0 ⊑ y).
    { intros z Hz; destruct Hz; subst; firstorder. }
    assert (H3: forall y0 : X, (forall y1 : X, doubleton x y y1 -> y1 ⊑ y0) ->
                          y ⊑ y0) by firstorder.
    assert (H4: directed (doubleton x y)).
    { split.
      - exists x. firstorder.
      - intros ? ? [? | ?] [? | ?]; subst;
          exists y; split; try right; firstorder. }
    specialize (H0 H4 (conj H2 H3)); destruct H0 as [H0 _].
    apply H0; exists x; firstorder.
  Qed.
End continuousLemmas.


Section wayBelow.
  Context {X : Type} `{P : Poset X}.

  Definition way_below x y :=
    forall D, directed D ->
         forall z, is_supremum z D ->
              y ⊑ z ->
              exists d, d ∈ D /\ x ⊑ d.

  Notation "a '<<' b" := (way_below a b) (at level 65) : domain_scope.

  Definition compact x := x << x.

  Lemma way_below_le x y :
    x << y -> x ⊑ y.
  Proof.
    intros H0; assert (H1: directed (singleton y)).
    { split.
      - exists y; firstorder.
      - intros x0 y0 H1 H2;
          unfold in_set, singleton in *; subst.
        exists y0; split. firstorder.
        intros y [H1 | H1]; subst; firstorder. }
    assert (H2: is_supremum y (singleton y)).
    { split.
      - unfold ub, singleton, upper_bound, in_set.
        intros y0 H2; subst; firstorder.
      - firstorder. }
    assert (H3: y ⊑ y) by firstorder.
    specialize (H0 _ H1 y H2 H3); firstorder.
  Qed.
End wayBelow.

Notation "a '<<' b" := (way_below a b) (at level 65) : domain_scope.

(** ω-chains are subsets of a poset that are isomorphic to the natural
    numbers with their natural order. *)
Section omegaChain.
  Context {X : Type} `{P : Poset X}.

  Definition omegaAx (g : nat -> X) := forall j, (g j) ⊑ (g (S j)).
  Definition omegaChain := { g : nat -> X | omegaAx g }.

  Definition omega_upper_bound (x : X) (A : omegaChain) :=
    forall j, (val A j) ⊑ x.

  (* x is the supremum of ω-chain A (up to equiv). *)
  Definition omega_is_supremum (x : X) (A : omegaChain) :=
    omega_upper_bound x A /\
    forall b, omega_upper_bound b A -> x ⊑ b.

  Lemma omegaAx_trans (A : omegaChain) n m :
    n <= m -> val A n ⊑ val A m.
  Proof.
    intros H0. induction m.
    - assert (n = 0) by omega; subst; firstorder.
    - destruct (PeanoNat.Nat.eqb_spec n (S m)).
      + subst; firstorder.
      + assert (n <= m) by omega.
        destruct P as [_ transAx].
        eapply transAx. apply IHm; assumption.
        destruct A; auto.
  Qed.

  Definition set_of_omegaChain (A : omegaChain) :=
    fun x => exists j, val A j = x.

  Definition omegaChain_function {Y : Type} (f : set X -> Y) : omegaChain -> Y :=
    fun A => f (set_of_omegaChain A).

  Lemma omega_upper_bound_upper_bound (x : X) (A : omegaChain) :
    omega_upper_bound x A <-> upper_bound x (set_of_omegaChain A).
  Proof.
    split.
    - intros H0 y Hy; destruct Hy as [j ?]; subst; auto.
    - intros H0 j; apply H0; exists j; auto.
  Qed.

  Lemma omega_is_supremum_is_supremum (x : X) (A : omegaChain) :
    omega_is_supremum x A <-> is_supremum x (set_of_omegaChain A).
  Proof.
    split; intros H0; split;
      try (intros ? ?; destruct H0 as [_ H0]; apply H0);
      apply omega_upper_bound_upper_bound; firstorder.
  Qed.
End omegaChain.

Notation "ω-chain" := omegaChain.


(** ω-DCPOs: every ω-chain has a supremum. *)
Section omegaDCPO.
  Class OmegaSupremum `(P : Poset) : Type :=
    omegaSupremum : omegaChain -> X.

  Class OmegaDCPO `(P : Poset) (S : OmegaSupremum P) : Prop :=
    omegaSupremumAx :
      forall A : omegaChain, omega_is_supremum (omegaSupremum A) A.

  Class PointedOmegaDCPO `(D : OmegaDCPO) (bot : Bottom) : Prop :=
    omegaBotAx : bottomAxiom.
End omegaDCPO.


(** Complete lattices. *)
Section lattice.
  Class Supremum `(P : Poset) : Type :=
    supremum : set X -> X.

  Class Infimum `(P : Poset) : Type :=
    infimum : set X -> X.

  (* TODO: is it possible to define the infimum in terms of the
     supremum? *)
  Class CompleteLattice `(P : Poset) (S : Supremum P) (I : Infimum P)
    : Prop :=
    { completeJoinAx : forall A, is_supremum (supremum A) A;
      completeMeetAx : forall A, is_infimum (infimum A) A }.

  Class PointedCompleteLattice `(L : CompleteLattice) (bot : Bottom)
    : Prop :=
    completeBotAxiom : bottomAxiom.
End lattice.

Notation "'⊔' x" := (supremum x) (at level 65).
Notation "'⊓' x" := (infimum x) (at level 65).


(** ω-DCPO structure for Scott continuous function spaces. *)
Section functionSpace.
  Context {X Y : Type} `{P : OmegaDCPO X} `{Q : OmegaDCPO Y}.

  Definition scottFunction := { f : X -> Y | scott_continuous f }.

  Instance functionOrder : PosetOrder :=
    fun (f g : scottFunction) => forall x, val f x ⊑ val g x.

  Lemma functionOrderRefl (f : scottFunction) :
    f ⊑ f.
  Proof. intros x; destruct P1 as [reflAx ?]; apply reflAx. Qed.

  Lemma functionOrderTrans (f g h : scottFunction) :
    f ⊑ g -> g ⊑ h -> f ⊑ h.
  Proof.
    intros H0 H1 x; specialize (H0 x); specialize (H1 x).
    destruct P1 as [? transAx]; eapply transAx; eauto.
  Qed.

  Program Instance functionPoset : Poset functionOrder.
  Next Obligation. apply functionOrderRefl. Qed.
  Next Obligation. eapply functionOrderTrans; eauto. Qed.

  Program Definition apply_chain (A : omegaChain) (x : X)
    : @omegaChain Y _ :=
    fun n => val A n x.
  Next Obligation. intros j; destruct A as [A ax]; apply ax. Qed.

  Program Definition functionSupremum (A : omegaChain) : scottFunction :=
    fun x => omegaSupremum (apply_chain A x).
  Next Obligation.
    intros B x Hd Hx; split.
    - intros y (z & H0 & ?).
      assert (forall i, val (apply_chain A z) i ⊑
                       omegaSupremum (apply_chain A x)).
      { intros i.
        assert (H1: is_supremum (val (val A i) x)
                                (image (val (val A i)) B)).
        { destruct (val A i) as [? pf]; simpl in *.
          specialize (pf _ _ Hd Hx); split; firstorder. }
        destruct H1 as [H1 H2].
        assert ((val ((val A) i)) x ⊑ omegaSupremum (apply_chain A x)).
        { specialize (Q (apply_chain A x)); firstorder. }
        destruct P1 as [? transAx]; eapply transAx.
        - apply H1; firstorder.
        - assumption. }
      destruct H; destruct P1 as [? transAx].
      eapply transAx. apply H2. firstorder.
    - intros y Hy.
      assert (H0: upper_bound y (fun x => exists j y, y ∈ B /\
                                              x ~~ val (val A j) y)).
      { intros z (j & w & Hz & ?); subst.
        assert (val (val A j) w ⊑ omegaSupremum (apply_chain A w)).
        { specialize (Q (apply_chain A w)).
          destruct Q; destruct H; firstorder. }
        destruct P1 as [? transAx].
        assert ((val ((val A) j)) w ⊑ y).
        { eapply transAx. apply H0. apply Hy; firstorder. }
        eapply transAx. apply H. assumption. }
      specialize (Q (apply_chain A x)).
      destruct Q as [_ supAx].
      apply supAx; clear supAx; intros j.
      assert (H1: is_supremum ((val (apply_chain A x)) j)
                              (image (val (val A j)) B)).
      { split.
        - intros z (w & H1 & H2); destruct P1 as [? transAx].
          unfold apply_chain; simpl; eapply transAx. apply H2.
          destruct (val A j) as [f pf]; simpl in *.
          specialize (pf B x Hd Hx); destruct pf as [pf _].
          apply pf; exists w; split; firstorder.
        - intros z Hz; unfold apply_chain; simpl.
          destruct (val A j) as [f pf]; simpl in *.
          specialize (pf B x Hd Hx).
          destruct pf as [_ pf]; apply pf; assumption. }
      destruct H1; apply H1; intros z (w & H2 & H3).
      apply H0; exists j, w; split; firstorder.
  Qed.

  Notation "'⊔' x" := (functionSupremum x) (at level 65) : domain_scope.
  Open Scope domain_scope.

  Lemma functionSupremum_is_supremum (A : omegaChain) :
    omega_is_supremum (⊔ A) A.
  Proof.
    split.
    - intros n x; pose proof Q as supAx;
        specialize (supAx (apply_chain A x)); firstorder.
    - intros f Hf x; pose proof Q as supAx;
        specialize (supAx (apply_chain A x));
        destruct supAx; apply H0; firstorder.
  Qed.

  Instance functionOmegaSupremum : OmegaSupremum functionPoset :=
    functionSupremum.

  Program Instance functionOmegaDCPO : OmegaDCPO functionOmegaSupremum.
  Next Obligation. apply functionSupremum_is_supremum. Qed.
End functionSpace.


Section scottTopology.
  Context {X : Type} `{P : Poset X}.

  Definition inaccessible_by_directed_joins (A : set X) :=
    forall D, directed D ->
         (exists x, is_supremum x D /\ x ∈ A) ->
         nonempty (D ∩ A).

  Definition closed_under_directed_joins (A : set X) :=
    forall B, B ⊆ A /\ directed B ->
         forall b, is_supremum b B ->
              b ∈ A.

  Definition scott_open (A : set X) :=
    is_upper_set A /\ inaccessible_by_directed_joins A.

  Definition scott_closed (A : set X) :=
    is_lower_set A /\ closed_under_directed_joins A.

  Instance scottOpens : Opens X :=
    fun A => scott_open A.

  Lemma empty_scott_open :
    open (@empty X).
  Proof. firstorder. Qed.

  Lemma full_scott_open :
    open (@full X).
  Proof. firstorder. Qed.

  Lemma union_scott_open (C : pow X) :
    (forall A : set X, C A -> open A) ->
    open (⋃ C).
  Proof.
    intros H0; split.
    - intros x y H1 (A & H2 & H3); exists A; firstorder.
    - intros D HD (x & H1 & (A & H2 & H3)).
      specialize (H0 A H2); destruct H0.
      assert (H4: exists x : X, is_supremum x D /\ x ∈ A) by firstorder.
      specialize (H0 D HD H4); destruct H0; exists x0.
      split; try exists A; firstorder.
  Qed.

  Lemma intersection_scott_open (A B : set X) :
    open A -> open B -> open (A ∩ B).
  Proof.
    intros [H0 H1] [H2 H3].
    split.
    - firstorder.
    - intros D HD (x & H4 & H5).
      assert (H6: exists x : X, is_supremum x D /\ x ∈ A) by firstorder.
      assert (H7: exists x : X, is_supremum x D /\ x ∈ B) by firstorder.
      specialize (H1 D HD H6); specialize (H3 D HD H7).
      clear H6 H7.
      destruct H1 as (y & H1 & H1'); destruct H3 as (z & H3 & H3').
      destruct HD as [HD HD']; specialize (HD' y z H1 H3).
      destruct HD' as (a & HD' & HD''); exists a.
      split; auto. split.
      + apply H0 with y; firstorder.
      + apply H2 with z; firstorder.
  Qed.

  Instance scottTopology : Topology scottOpens.
  Proof.
    constructor.
    - apply empty_scott_open.
    - apply full_scott_open.
    - apply union_scott_open.
    - apply intersection_scott_open.
  Qed.
End scottTopology.


Section scottTopologyLemmas.
  Context {X Y : Type} `{P : Poset X} `{Q : Poset Y}.
  Variable f : X -> Y.

  Existing Instance scottOpens.

  (* Seems unprovable without LEM. *)
  (* Lemma jdfg (A : set X) : *)
  (*   scott_closed A <-> closed A. *)
  (* Proof. *)
  (*   split; intros H0. *)
  (*   - unfold scott_closed in H0. unfold closed. unfold open, scottOpens, scott_open. *)
  (*     destruct H0 as [H0 H1]. *)
  (*     split. *)
  (*     + firstorder. *)
  (*     + unfold inaccessible_by_directed_joins. *)
  (*       unfold closed_under_directed_joins in H1. *)
  (*       intros D HD (x & H2 & H3). unfold nonempty. *)
  (*       assert (H4: D ⊆ A \/ ~ D ⊆ A). *)
  (*       { admit. } *)
  (*       (* destruct H4 as [H4 | H4]. *) *)
  (*       (* * specialize (H1 D (conj H4 HD) x H2). firstorder. *) *)
  (*       (* * exists d *) *)
  (*       (* unfold intersection. *) *)
  (*       (* exists x. split; auto. *) *)

  (* Lemma continuous_monotone : *)
  (*   continuous f -> monotone f. *)
  (* Proof. *)
  (*   intros Hcont. unfold continuous in Hcont. *)
  (*   intros x y H0. *)
  (*   unfold scottOpens, scott_open in Hcont. *)
  (*   (* Not sure if this can be proven constructively.. *) *)
  (* Admitted. *)

  (* Is the converse provable? *)
  Lemma scott_continuous_continuous :
    scott_continuous f -> continuous f.
  Proof.
    intros H0.
    generalize (scott_continuous_monotone H0). intros Hmono.
    intros V [H1 H2].
    split.
    - apply monotone_upper_preimage; auto.
    - intros D HD (x & H3 & H4).
      assert (H5 : directed (image f D)).
      { apply monotone_directed_image; auto. }
      assert (H6: exists x : Y, is_supremum x (image f D) /\ x ∈ V).
      { exists (f x); split.
        - apply H0; auto.
        - firstorder. }
      specialize (H2 (image f D) H5 H6).
      destruct H2 as (y & (x0 & H2 & H2') & H2'').
      exists x0; split; auto.
      specialize (H1 y (f x0)); firstorder.
  Qed.
End scottTopologyLemmas.
