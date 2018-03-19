(*
 * Formalizing Concepts from Topology
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import Coq.Logic.Classical_Prop.

Require Import GrappaCoq.Set.


Section topology.
  Variable X : Type. (* The carrier set *)

  Class TopologyOpens : Type :=
    open : set (set X).

  Class TopologyEmptyAxiom (T : TopologyOpens) : Prop :=
    emptyAxiom : open (@empty_set X).

  Class TopologyFullAxiom (T : TopologyOpens) : Prop :=
    fullAxiom : open (@full_set X).

  Class TopologyUnionAxiom (T : TopologyOpens) : Prop :=
    unionAxiom: forall (C : P X),
      (forall A : set X, C A -> open A) ->
      open (big_union C).

  Class TopologyIntersectionAxiom (T : TopologyOpens) : Prop :=
    intersectionAxiom : forall A B : set X,
      open A -> open B -> open (intersection A B).

  Class Topology (opens : TopologyOpens)
        (emptyAx : TopologyEmptyAxiom opens)
        (fullAx : TopologyFullAxiom opens)
        (unionAx : TopologyUnionAxiom opens)
        (intersectionAx : TopologyIntersectionAxiom opens)
    : Type := {}.


  Definition finer (A B : TopologyOpens) := subset B A.
  Definition larger (A B : TopologyOpens) := finer A B.
  Definition strictly_finer (A B : TopologyOpens) := proper_subset B A.
  Definition coarser (A B : TopologyOpens) := finer B A.
  Definition smaller (A B : TopologyOpens) := coarser A B.
  Definition strictly_coarser (A B : TopologyOpens) := strictly_finer B A.
  Definition comparable (A B : TopologyOpens) := finer A B \/ finer B A.

  Lemma comparable_comm (A B : TopologyOpens) :
    comparable A B <-> comparable B A.
  Proof. firstorder. Qed.

  Lemma strictly_finer_implies_finer (A B : TopologyOpens) :
    strictly_finer A B -> finer A B.
  Proof. firstorder. Qed.

  Lemma strictly_coarser_implies_coarser (A B : TopologyOpens) :
    strictly_coarser A B -> coarser A B.
  Proof. firstorder. Qed.
End topology.

Section basis.
  Variable X : Type.
  (** Basis of a topology *)

  Class BasisSet : Type :=
    basis : set (set X).

  Class BasisAxiom1 (BSet : BasisSet) : Prop :=
    basisAxiom1 : forall x : X, exists b, BSet b /\ b x.

  Class BasisAxiom2 (BSet : BasisSet) : Prop :=
    basisAxiom2 : forall x b1 b2,
      BSet b1 -> BSet b2 -> (intersection b1 b2) x ->
      exists b3, BSet b3 /\ b3 x /\ subset b3 (intersection b1 b2).

  Class Basis (BSet : BasisSet) (ax1 : BasisAxiom1 BSet) (ax2 : BasisAxiom2 BSet)
    : Type := {}.

  (* Basis B generates the open sets O. *)
  Definition generates `(B : Basis) (O : TopologyOpens X) :=
    forall (U : set X), (forall x, U x -> exists b, basis b /\ b x /\ subset b U) <-> open U.

  (* Given a basis B, a topology O, and a proof of [generates B O], we
     show that the four topology axioms are satisfied by O. Note that
     O and open are synonyms.*)
  Lemma basis_topology_axiom1 `(B : Basis) (O : TopologyOpens X) :
    generates B O ->
    O (@empty_set X).
  Proof.
    unfold generates. intro Hgen.
    apply Hgen; intros x Hempty; inversion Hempty.
  Qed.

  Lemma basis_topology_axiom2 `(B : Basis) (O : TopologyOpens X) :
    generates B O ->
    O (@full_set X).
  Proof.
    unfold generates. intro Hgen.
    apply Hgen; intros x Hfull.
    unfold BasisAxiom1 in ax1.
    destruct (ax1 x) as [b [Hb0 Hb1]].
    exists b; split; auto; split; auto; apply all_subset_full.
  Qed.

  Lemma basis_topology_axiom3 `(B : Basis) (O : TopologyOpens X) :
    generates B O ->
    forall (C : P X),
      (forall A : set X, C A -> open A) ->
      O (big_union C).
  Proof.
    intros Hgen C Hopen. unfold generates in Hgen.
    apply Hgen. intros x Hunion.
    destruct Hunion as [A [H1 H2]].
    specialize (Hopen A H1).
    rewrite <- (Hgen A) in Hopen.
    specialize (Hopen x H2).
    destruct Hopen as [b [Hb0 [Hb1 Hb2]]].
    exists b; split; auto; split; auto.
    eapply subset_trans; eauto.
    apply subset_big_union; assumption.
  Qed.

  Lemma basis_topology_axiom4 `(basis : Basis) (O : TopologyOpens X) :
    generates basis O ->
    forall A B : set X,
      O A -> O B -> O (intersection A B).
  Proof.
    intros Hgen A B HopenA HopenB. 
    apply Hgen. intros x [H0 H1].
    rewrite <- (Hgen A) in HopenA. rewrite <- (Hgen B) in HopenB.
    specialize (HopenA x H0). specialize (HopenB x H1).
    destruct HopenA as [b [Hb0 [Hb1 Hb2]]].
    destruct HopenB as [b' [Hb0' [Hb1' Hb2']]].
    pose proof ax2 as Hax2.
    assert (Hint: intersection b b' x) by (split; auto).
    specialize (Hax2 x b b' Hb0 Hb0' Hint).
    destruct Hax2 as [b'' [H2 [H3 H4]]].
    exists b''; split; auto; split; auto.
    eapply subset_trans; eauto.
    apply subset_intersection; auto.
  Qed.

  (* From a basis and a set of opens it generates, we can construct a
     Topology instance. *)
  Program Instance BasisTopologyEmptyAxiomInstance `(basis : Basis)
          (O : TopologyOpens X) (pf : generates basis O) :
    TopologyEmptyAxiom O.
  Next Obligation. eapply basis_topology_axiom1; auto. Qed.
  Program Instance BasisTopologyFullAxiomInstance `(basis : Basis)
          (O : TopologyOpens X) (pf : generates basis O) :
    TopologyFullAxiom O.
  Next Obligation. eapply basis_topology_axiom2; auto. Qed.
  Program Instance BasisTopologyUnionAxiomInstance `(basis : Basis)
          (O : TopologyOpens X) (pf : generates basis O) :
    TopologyUnionAxiom O.
  Next Obligation. eapply basis_topology_axiom3; auto. Qed.
  Program Instance BasisTopologyIntersectionAxiomInstance `(basis : Basis)
          (O : TopologyOpens X) (pf : generates basis O) : 
    TopologyIntersectionAxiom O.
  Next Obligation. eapply basis_topology_axiom4; auto. Qed.
  Program Instance BasisTopologyInstance `(basis : Basis)
          (O : TopologyOpens X) (pf : generates basis O) :
    Topology (BasisTopologyEmptyAxiomInstance basis O pf)
              (BasisTopologyFullAxiomInstance basis O pf)
              (BasisTopologyUnionAxiomInstance basis O pf)
              (BasisTopologyIntersectionAxiomInstance basis O pf).

  (* Any basis element is open. *)
  Lemma basis_set_open `(B : Basis) (O : TopologyOpens X) A :
    generates B O ->
    basis A -> open A.
  Proof. firstorder. Qed.

  Lemma open_union_subset_basis `(B : Basis) (O : TopologyOpens X) A :
    generates B O ->
    open A ->
    exists C, subset C basis /\ A = big_union C.
  Proof.
    intros Hgen HOA. unfold generates in Hgen.
    pose proof HOA as H0. rewrite <- Hgen in H0.
    exists (fun B => basis B /\ subset B A).
    split; firstorder.
    (* firstorder solves this but the resulting proof term is large *)
    (* apply extensionality. split; intros x H1; firstorder. *)
    apply extensionality. split; intros x H1.
    - unfold big_union. destruct (H0 x H1) as [b H2].
      exists b;  intuition.
    - destruct H1 as [b [[H1 H2] H3]]; apply H2; assumption.
  Qed.

 Lemma subset_basis_union_open `(B : Basis) (O : TopologyOpens X) C :
    generates B O ->
    subset C basis ->
    open (big_union C).
  Proof.
    intros Hgen Hsubset.
    assert (H0: forall A, C A -> open A).
    { intros x HCx; eapply basis_set_open; auto. }
    generalize (BasisTopologyUnionAxiomInstance B O Hgen).
    intro H1; apply Hgen; firstorder.
  Qed.

  (** Lemma 13.1: Let B be a basis for a topology O on X. Then O
      equals the collection of all unions of elements of B. *)
  Lemma opens_equal_all_basis_unions `(B : Basis) (O : TopologyOpens X) :
    generates B O ->
    O = all_unions basis.
  Proof.
    intro Hgen.
    apply extensionality; split; intros A H0.
    - eapply open_union_subset_basis in H0; eauto.
    - destruct H0 as [C [Hsubset Hunion]].
      rewrite Hunion; eapply subset_basis_union_open; eauto.
  Qed.

  Definition all_open (O : TopologyOpens X) (C : P X) := forall A, C A -> open A.

  (** Lemma 13.2 : Let X be a topological space. Suppose that C is a
      collection of open sets of X such that for each open set U of X
      and each x in U, there is an element b of C such that x \in b
      and b \subset U. Then, C is a basis for the topology of X.  *)
  Section lemma_13_2.
    Context `(T : Topology X) (C : P X).
    Variable H0 : all_open _ C.
    Variable H1: forall U, open U ->
                      forall x, U x ->
                           exists b, C b /\ b x /\ subset b U.

    (* First, we show that C satisfies the basis axioms. *)
    Lemma l_13_2_axiom1 : BasisAxiom1 C.
    Proof.
      intro x; specialize (@H1 (@full_set X) fullAx x I); firstorder.
    Qed.

    Lemma l_13_2_axiom2 : BasisAxiom2 C.
      intros x b1 b2 HCb1 HCb2 Hint.
      assert (Hopen: open (intersection b1 b2)).
      { apply intersectionAx; auto. }
      specialize (H1 Hopen Hint); firstorder.
    Qed.

    (* Construct a Basis instance for C. *)
    Instance lemma_13_2_Basis : @Basis C l_13_2_axiom1 l_13_2_axiom2.

    (* From here on in this section, C and basis are synonyms for the
       same collection of sets (the basis elements), since by this
       point we have proven that C forms a basis. *)

    Lemma l_13_2_1 (U : set X) :
      (forall x : X, U x -> exists b : set X, C b /\ b x /\ subset b U) ->
      exists D, subset D C /\ U = big_union D.
    Proof.
      intro H2. exists (fun A => C A /\ subset A U).
      split; firstorder; apply extensionality; firstorder.
    Qed.

    (* C generates the topology. *)
    Lemma l_13_2_generates : generates lemma_13_2_Basis opens.
    Proof.
      unfold generates.
      intro U; split.
      - intro H2; apply l_13_2_1 in H2; destruct H2 as [D [H2 H3]].
        subst; firstorder.
      - firstorder.
    Qed.

    (* The union of all basis elements equals the union of all opens. *)
    Lemma l_13_2_unions_equal : big_union C = big_union opens.
    Proof.
      generalize l_13_2_generates. intro Hgen.
      apply opens_equal_all_basis_unions in Hgen.
      rewrite Hgen, big_union_all_unions; reflexivity.
    Qed.
  End lemma_13_2.

  (** Lemma 13.3: Let B and B' be bases for the topologies O and O',
      respectively, on X. Then the following are equivalent:
      1) O' is finer than O
      2) For each x \in X and each basis element b \in B containing x,
         there is a basis element b' \in B' such that x \in B' and B'
         \subset B.  *)
  Section lemma_13_3.
    Variable basis basis' : P X.
    Context ax1 ax2 (B : @Basis basis ax1 ax2).
    Context ax1' ax2' (B' : @Basis basis' ax1' ax2').
    Context (O : TopologyOpens X) (O' : TopologyOpens X).
    Variable Hgen : generates B O.
    Variable Hgen' : generates B' O'.

    Lemma l_13_3 :
      finer O' O <->
      forall x b,
        basis b -> b x ->
        exists b', basis' b' /\ b' x /\ subset b' b.
    Proof.
      split.
      - intros Hfiner x b Hbasis Hbx.
        assert (Hopen: O b) by firstorder; firstorder.
      - intros H0 U Hopen; apply Hgen'; intros x HUx.
        unfold generates in Hgen. rewrite <- Hgen in Hopen.
        specialize (Hopen x HUx).
        destruct Hopen as [b [Hb0 [Hb1 Hb2]]].
        specialize (H0 x b Hb0 Hb1); firstorder.
    Qed.
  End lemma_13_3.
End basis.
