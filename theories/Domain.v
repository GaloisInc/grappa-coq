Set Implicit Arguments.
Unset Strict Implicit.
Require Import Omega.

Require Import GrappaCoq.Set.
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

  Class Poset (order : PosetOrder) : Type :=
    { reflAxiom : forall x, x ⊑ x;
      transAxiom : forall x y z, x ⊑ y -> y ⊑ z -> x ⊑ z }.

  Class Bottom : Type :=
    bot : X.

  Notation "⊥" := bot : domain_scope.

  Definition bottomAxiom {P : PosetOrder} {B : Bottom} := 
    forall x, ⊥ ⊑ x.

  Class PointedPoset `(P : Poset) (bot : Bottom) : Type :=
    { botAxiom : bottomAxiom }.

  (* Coercions *)
  Definition Poset_of_PointedPoset `(P : PointedPoset) : Poset _ := _.
  Coercion Poset_of_PointedPoset : PointedPoset >-> Poset.
End poset.

Notation "a '⊑' b" := (le a b) (at level 65) : domain_scope.
Notation "a '~~' b" := (equiv a b) (at level 65) : domain_scope.
Notation "⊥" := bot : domain_scope.
Open Scope domain_scope.


Section posetDefinitions.
  Context {X : Type} `{P : Poset X}.

  Definition lt (x y : X) :=
    ~ (x ~~ y) /\ x ⊑ y.

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
    forall x, x ∈ A -> exists y, y ∈ A /\ lt y x.

  Definition is_supremum (x : X) (A : set X) :=
    least x (ub A).
  Notation is_join := is_supremum.

  Definition is_infimum (x : X) (A : set X) :=
    largest x (lb A).
  Notation is_meet := is_infimum.

  Definition is_join_semilattice :=
    forall x y, exists sup, is_supremum sup (doubleton x y).

  Definition is_meet_semilattice :=
    forall x y, exists inf, is_infimum inf (doubleton x y).

  Definition is_lattice :=
    is_join_semilattice /\ is_meet_semilattice.

  Definition is_complete_lattice :=
    forall A : set X, exists sup inf, is_supremum sup A /\ is_infimum inf A.
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
  Proof.
    intros H ?; apply supremum_lower in H; firstorder.
  Qed.

  Lemma infimum_upper (A : set X) (x : X) :
    is_infimum x A <-> is_infimum x (upper_set A).
  Proof.
    split; intros [? H0]; split;
      try (intros ? ?; apply H0; firstorder); firstorder.
  Qed.

  Lemma asdf1 (C : pow X) (A : set X) (x y : X) :
    A = ⋃ C ->
    (forall B, B ∈ C -> exists z, is_supremum z B) ->
    is_supremum x A -> is_supremum y (fun z => exists B, B ∈ C /\ is_supremum z B) ->
    x ~~ y.
  Proof.
    set (Z := fun x0 : X => exists B : set X, B ∈ C /\ is_supremum x0 B).
    intros H0 He H1 H2. subst.
    assert (H0: forall x, is_supremum x (⋃ C) ->
                     forall B y, B ∈ C -> is_supremum y B -> y ⊑ x).
    { intros; eapply subset_sup_le; eauto; firstorder. }
    assert (H3: upper_bound x Z).
    { intros z H3.
      destruct H3 as (B & H3 & H4).
      eapply H0; eauto. }
    assert (y ⊑ x) by firstorder.
    assert (x ⊑ y).
    { assert (forall a, a ∈ ⋃ C -> exists A, A ∈ C /\ a ∈ A) by firstorder.
      assert (forall a, a ∈ ⋃ C -> exists z, z ∈ Z /\ a ⊑ z).
      { intros a Ha. specialize (H4 a Ha).
        destruct H4 as (A & H4 & H5).
        specialize (He A H4).
        destruct He as [z He].
        exists z; firstorder. }
      assert (forall a, a ∈ ⋃ C -> a ⊑ y).
      { intros a Ha. specialize (H4 a Ha).
        destruct H4 as (A & H4 & H6).
        destruct H2 as [H2 H2'].
        specialize (H5 a Ha). destruct H5 as (z & H5 & H7).
        destruct P as [_ transAx]. eapply transAx; eauto. }
    firstorder. }
    firstorder.
  Qed.

  Lemma asdf2 (C : pow X) (A : set X) (x y : X) :
    A = ⋃ C ->
    (forall B, B ∈ C -> exists z, is_infimum z B) ->
    is_infimum x A -> is_infimum y (fun z => exists B, B ∈ C /\ is_infimum z B) ->
    x ~~ y.
  Admitted.

  Lemma not_least_no_least (A : set X) :
    no_least A -> (~ exists x, least x A).
  Proof. firstorder. Qed.

  Lemma least_not_no_least (A : set X) :
    (exists x, least x A) -> ~ no_least A.
  Proof. firstorder. Qed.
End posetLemmas.


Section pointedPosetLemmas.
  Context {X : Type} `{P : PointedPoset X}.

  Lemma bot_least : least ⊥ (@full X).
  Proof. firstorder. Qed.
End pointedPosetLemmas.


Notation "'val' x" := (proj1_sig x) (at level 10).


Section monotone.
  Context {X Y : Type} `{P : Poset X} `{Q : Poset Y}.
  Variable f : X -> Y.
  Definition monotone := forall x y, x ⊑ y -> (f x) ⊑ (f y).
End monotone.


Section directedSet.
  Context {X : Type} `{P : Poset X}.

  Definition directed (A : set X) :=
    nonempty A /\
    forall x y, x ∈ A -> y ∈ A -> exists a, upper_bound a (doubleton x y).

  Definition directed_set := { A : set X | directed A }.

  Definition ideal (A : set X) :=
    directed A /\ is_lower_set A.

  Definition filtered_set (A : set X) :=
    directed A /\ is_upper_set A.

  Definition totally_ordered (A : set X) :=
    forall x y, x ∈ A -> y ∈ A -> x ⊑ y \/ y ⊑ x.

  Definition is_chain (A : set X) :=
    directed A /\ totally_ordered A.

  Definition chain := { A : set X | is_chain A }.

  (* A is cofinal in B *)
  Definition cofinal (A B : set X) :=
    forall b, b ∈ B -> exists a, a ∈ A /\ b ⊑ a.
End directedSet.


(* ω-chains are subsets of a poset that are isomorphic to the natural
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
    forall s, omega_upper_bound s A -> x ⊑ s.

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

  Definition omega_is_directed (A : omegaChain) :
    directed (fun x => exists n, val A n = x).
  Proof.
    split.
    - exists (val A 0), 0; auto.
    - intros x y Hx Hy.
      destruct Hx as [nx Hx]; destruct Hy as [ny Hy].
      subst; destruct (Compare_dec.dec_le nx ny).
      + exists (val A ny). intros y Hy.
        destruct Hy; subst.
        * apply omegaAx_trans; assumption.
        * firstorder.
      + exists (val A nx). intros y Hy.
        assert (ny <= nx) by omega.
        destruct Hy; subst.
        * firstorder.
        * apply omegaAx_trans; assumption.
  Qed.

  Program Definition directed_set_of_omega_chain (A : omegaChain)
    : directed_set :=
    fun x => exists n, A n = x.
  Next Obligation. apply omega_is_directed. Qed.

  (* A function on directed sets can also take ω-chains since they are
     directed. *)
  Definition omega_f_of_directed_f {A : Type} (f : directed_set -> A)
    : omegaChain -> A :=
    fun x => f (directed_set_of_omega_chain x).
End omegaChain.

Notation "ω-chain" := omegaChain.


(** ω-DCPOs: every ω-chain has a supremum. *)
Section omegadcpo.
  Class OmegaSupremum `(P : Poset) : Type :=
    omegaSupremum : omegaChain -> X.

  Class OmegaDCPO `(P : Poset) (S : OmegaSupremum P) : Type :=
    { omegaSupremumAx :
        forall A : omegaChain, omega_is_supremum (omegaSupremum A) A }.

  Class PointedOmegaDCPO `(D : OmegaDCPO) (bot : Bottom) : Type :=
    { omegaBotAx : bottomAxiom }.

  (* Coercions *)
  Definition OmegaDCPO_of_PointedOmegaDCPO `(D : PointedOmegaDCPO)
    : OmegaDCPO _ := _.
  Coercion OmegaDCPO_of_PointedOmegaDCPO : PointedOmegaDCPO >-> OmegaDCPO.

  Definition PointedPoset_of_PointedOmegaDCPO `(D : PointedOmegaDCPO)
    : PointedPoset _ _ :=
    {| botAxiom := match D with Build_PointedOmegaDCPO _ pf => pf end |}.
  Coercion PointedPoset_of_PointedOmegaDCPO :
    PointedOmegaDCPO >-> PointedPoset.

  Definition Poset_of_OmegaDCPO `(D : OmegaDCPO) : Poset _ := _.
  Coercion Poset_of_OmegaDCPO : OmegaDCPO >-> Poset.
End omegadcpo.


(** DCPOs: every directed set has a supremum. *)
Section dcpo.
  Class DirectedSupremum `(P : Poset) : Type :=
    dSupremum : directed_set -> X.

  Class DCPO `(P : Poset) (S : DirectedSupremum P) : Type :=
    { dcpoSupremumAx :
        forall A : directed_set, is_supremum (dSupremum A) (val A) }.

  Class PointedDCPO `(D : DCPO) (bot : Bottom) : Type :=
    { dcpoBotAx : bottomAxiom }.

  (* Coercions *)
  Program Definition OmegaDCPO_of_DCPO `(D : DCPO) : OmegaDCPO _ :=
    @Build_OmegaDCPO _ _ _ (omega_f_of_directed_f S0) _.
  Next Obligation.
    destruct D as [supAx].
    split.
    - intros j. specialize (supAx (directed_set_of_omega_chain A)).
      unfold is_supremum in supAx. destruct supAx.
      unfold omegaSupremum, omega_f_of_directed_f.
  Admitted.
  Coercion OmegaDCPO_of_DCPO : DCPO >-> OmegaDCPO.

  Definition DCPO_of_PointedDCPO `(D : PointedDCPO) : DCPO _ := _.
  Coercion DCPO_of_PointedDCPO : PointedDCPO >-> DCPO.

  Definition PointedPoset_of_PointedDCPO `(D : PointedDCPO)
    : PointedPoset _ _ :=
    {| botAxiom := match D with Build_PointedDCPO _ pf => pf end |}.
  Coercion PointedPoset_of_PointedDCPO : PointedDCPO >-> PointedPoset.

  Definition Poset_of_DCPO `(D : DCPO) : Poset _ := _.
  Coercion Poset_of_DCPO : DCPO >-> Poset.
End dcpo.


(** Semilattices, lattices, and complete lattices. *)
Section lattice.
  Class JoinSemilattice `(P : Poset) : Type :=
    joinSemiAx : is_join_semilattice.

  Class MeetSemilattice `(P : Poset) : Type :=
    meetSemiAx : is_meet_semilattice.

  Class Lattice `(P : Poset) : Type :=
    { joinAx : is_join_semilattice;
      meetAx : is_meet_semilattice }.

  Class PointedLattice `(L : Lattice) (bot : Bottom) : Type :=
    { latticeBotAxiom : bottomAxiom }.

  Class Supremum `(P : Poset) : Type :=
    supremum : set X -> X.

  Class Infimum `(P : Poset) : Type :=
    infimum : set X -> X.

  Class CompleteLattice `(P : Poset) (S : Supremum P) (I : Infimum P)
    : Type :=
    { completeJoinAx : forall A, is_supremum (supremum A) A;
      completeMeetAx : forall A, is_infimum (infimum A) A }.

  Class PointedCompleteLattice `(L : CompleteLattice) (bot : Bottom)
    : Type :=
    { completeBotAxiom : bottomAxiom }.

  (* Coercions *)
  Definition Lattice_of_PointedLattice `(P : PointedLattice)
    : Lattice _ := _.
  Coercion Lattice_of_PointedLattice : PointedLattice >-> Lattice.

  Definition CompleteLattice_of_PointedCompleteLattice
             `(L : PointedCompleteLattice)
    : CompleteLattice _ _ := _.
  Coercion CompleteLattice_of_PointedCompleteLattice
    : PointedCompleteLattice >-> CompleteLattice.

  (* TODO: coercion to DCPO *)
End lattice.

Notation "'⊔' x" := (supremum x) (at level 65).
Notation "'⊓' x" := (infimum x) (at level 65).
