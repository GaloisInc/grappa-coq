(*
 * Formalizing Concepts from Topology
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import GrappaCoq.Set.


Section topology.
  Variable X : Type. (* The domain *)

  (* Collection of open sets *)
  Class Opens : Type :=
    open : set (set X).

  (* The collection of open sets satisfies the topology axioms. *)
  Class Topology (opens : Opens)
    : Type :=
    { emptyAxiom : open (@empty X);
      fullAxiom  : open (@full X);
      unionAxiom : forall (C : pow X),
          (forall A : set X, C A -> open A) ->
          open (big_union C);
      intersectionAxiom : forall A B : set X,
          open A -> open B -> open (intersection A B) }.

  Definition all_open (O : Opens) (C : pow X) := forall A, C A -> O A.

  Definition finer (A B : Opens) := subset B A.
  Definition larger (A B : Opens) := finer A B.
  Definition strictly_finer (A B : Opens) := proper_subset B A.
  Definition coarser (A B : Opens) := finer B A.
  Definition smaller (A B : Opens) := coarser A B.
  Definition strictly_coarser (A B : Opens) := strictly_finer B A.
  Definition comparable (A B : Opens) := finer A B \/ finer B A.

  Lemma comparable_comm (A B : Opens) :
    comparable A B <-> comparable B A.
  Proof. firstorder. Qed.

  Lemma strictly_finer_implies_finer (A B : Opens) :
    strictly_finer A B -> finer A B.
  Proof. firstorder. Qed.

  Lemma strictly_coarser_implies_coarser (A B : Opens) :
    strictly_coarser A B -> coarser A B.
  Proof. firstorder. Qed.

  Definition interior {O : Opens} (A : set X) :=
    big_union (fun B => open B /\ subset B A).

  Lemma interior_open {O : Opens} {T : Topology O} (A : set X) :
    open (interior A).
  Proof. 
    destruct T as [_ _ unionAxiom _]; apply unionAxiom; firstorder.
  Qed.

  Definition neighborhood {O : Opens} (A : set X) (x : X) :=
    open A /\ A x.

  Lemma exists_neighborhood {O : Opens} {T : Topology O} (x : X) :
    exists U, neighborhood U x.
  Proof. firstorder. Qed.
End topology.


Section basis.
  Variable X : Type.

  (** Basis of a topology *)

  Class BasisSet : Type :=
    basis : pow X.

  Definition basisAxiom1 (C : pow X) := forall x : X, exists b, C b /\ b x.
  Definition basisAxiom2 (C : pow X) := forall x b1 b2,
      C b1 -> C b2 -> (intersection b1 b2) x ->
      exists b3, C b3 /\ b3 x /\ subset b3 (intersection b1 b2).

  Class Basis (BSet : BasisSet)
    : Type :=
    { basisAx1 : basisAxiom1 BSet;
      basisAx2 : basisAxiom2 BSet }.

  Definition generate (B : pow X) := fun A => exists C, subset C B /\ big_union C = A.

  (* Basis B generates the open sets O. *)
  Definition generates `(B : Basis) (O : Opens X) :=
    forall (U : set X), (forall x, U x -> exists b, basis b /\ b x /\ subset b U) <-> O U.

  Lemma generate_generates `(B : Basis) :
    generates B (generate basis).
  Proof.
    destruct B as [ax1 ax2].
    unfold generates, generate.
    intros U. split; intro H0.
    - exists (fun A => basis A /\ subset A U).
      split; firstorder.
      apply extensionality; firstorder.
    - intros x HUx.
      destruct H0 as [C [H0 H1]]; subst.
      unfold big_union in HUx.
      destruct HUx as [A [H1 H2]].
      exists A; firstorder.
  Qed.

  (* Given a basis B, a topology O, and a proof of [generates B O], we
     show that the four topology axioms are satisfied by O. Note that
     O and open are synonyms.*)

  Lemma basis_topology_empty_axiom `(B : Basis) (O : Opens X) :
    generates B O ->
    O (@empty X).
  Proof.
    unfold generates. intro Hgen.
    apply Hgen; intros x Hempty; inversion Hempty.
  Qed.

  Lemma basis_topology_full_axiom `(B : Basis) (O : Opens X) :
    generates B O ->
    O (@full X).
  Proof.
    intro Hgen; apply Hgen; intros x Hfull.
    destruct B as [ax1 ax2].
    destruct (ax1 x) as [b [Hb0 Hb1]].
    exists b; split; auto; split; auto; apply all_subset_full.
  Qed.

  Lemma basis_topology_union_axiom `(B : Basis) (O : Opens X) :
    generates B O ->
    forall (C : pow X),
      (forall A : set X, C A -> O A) ->
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

  Lemma basis_topology_intersection_axiom `(basis : Basis) (O : Opens X) :
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
    pose proof basis as basis'.
    destruct basis' as [_ ax2].
    pose proof ax2 as Hax2.
    assert (Hint: intersection b b' x) by (split; auto).
    specialize (Hax2 x b b' Hb0 Hb0' Hint).
    destruct Hax2 as [b'' [H2 [H3 H4]]].
    exists b''; split; auto; split; auto.
    eapply subset_trans; eauto.
    apply subset_intersection; auto.
  Qed.

  Instance BasisTopology `(basis : Basis)
          (O : Opens X) (pf : generates basis O) :
    Topology O.
  Proof with assumption.
    constructor.
    - eapply basis_topology_empty_axiom...
    - eapply basis_topology_full_axiom...
    - eapply basis_topology_union_axiom...
    - eapply basis_topology_intersection_axiom...
  Qed.

  (* Any basis element is open. *)
  Lemma basis_set_open `(B : Basis) (O : Opens X) A :
    generates B O ->
    basis A -> open A.
  Proof. firstorder. Qed.

  Lemma open_union_subset_basis `(B : Basis) (O : Opens X) A :
    generates B O ->
    O A ->
    exists C, subset C basis /\ A = big_union C.
  Proof.
    intros Hgen HOA. unfold generates in Hgen.
    pose proof HOA as H0. rewrite <- Hgen in H0.
    exists (fun B => basis B /\ subset B A).
    split; firstorder.
    apply extensionality. split; intros x H1.
    - unfold big_union. destruct (H0 x H1) as [b H2].
      exists b;  intuition.
    - destruct H1 as [b [[H1 H2] H3]]; apply H2; assumption.
  Qed.

  Lemma all_open_subset_basis `(B : Basis) (O : Opens X) (C : pow X) :
    generates B O ->
    all_open _ C ->
    exists D, subset D basis /\ big_union D = big_union C.
  Proof.
    intros Hgen Hopen.
    exists (fun b => basis b /\ subset b (big_union C)). split.
    - firstorder.
    -  apply extensionality. split.
       + firstorder.
       + intros x Hunion.
         destruct Hunion as [A [H0 H1]]; specialize (Hopen A H0).
         unfold generates in Hgen; rewrite <- Hgen in Hopen; firstorder.
  Qed.

 Lemma subset_basis_union_open `(B : Basis) (O : Opens X) C :
    generates B O ->
    subset C basis ->
    O (big_union C).
  Proof.
    intros Hgen Hsubset.
    assert (H0: forall A, C A -> O A).
    { intros x HCx; eapply basis_set_open; auto. }
    generalize (BasisTopology B O Hgen).
    intro H1; apply Hgen; firstorder.
  Qed.

  Lemma big_union_basis_equals_domain `(B : Basis) :
    big_union basis = (@full X).
  Proof. apply extensionality; firstorder. Qed.

  (** Lemma 13.1: Let B be a basis for a topology O on X. Then O
      equals the collection of all unions of elements of B. *)
  Lemma opens_equal_all_basis_unions `(B : Basis) (O : Opens X) :
    generates B O ->
    O = all_unions basis.
  Proof.
    intro Hgen.
    apply extensionality; split; intros A H0.
    - eapply open_union_subset_basis in H0; eauto.
    - destruct H0 as [C [Hsubset Hunion]].
      rewrite Hunion; eapply subset_basis_union_open; eauto.
  Qed.


  (** Lemma 13.2 : Let X be a topological space. Suppose that C is a
      collection of open sets of X such that for each open set U of X
      and each x in U, there is an element b of C such that x \in b
      and b \subset U. Then, C is a basis for the topology of X.  *)
  Section lemma_13_2.
    Context `(T : Topology X) (C : pow X).
    Variable H0 : all_open opens C.
    Variable H1: forall U, open U ->
                      forall x, U x ->
                           exists b, C b /\ b x /\ subset b U.

    (* First, we show that C satisfies the basis axioms. *)
    Lemma l_13_2_axiom1 : basisAxiom1 C.
    Proof.
      destruct T as [_ fullAx _ _].
      intros x; specialize (@H1 (@full X) fullAx x); firstorder.
    Qed.

    Lemma l_13_2_axiom2 : basisAxiom2 C.
    Proof.
      intros x b1 b2 HCb1 HCb2 Hint.
      assert (Hopen: open (intersection b1 b2)).
      { destruct T as [_ _ _ intersectionAx];
          apply intersectionAx; firstorder. }
      specialize (H1 Hopen Hint); firstorder.
    Qed.

    (* Construct a Basis instance for C. *)
    Instance lemma_13_2_Basis : @Basis C.
    Proof.
      constructor.
      - apply l_13_2_axiom1.
      - apply l_13_2_axiom2.
    Qed.

    (* From here on in this section, C and basis are synonyms for the
       same collection of sets (the basis elements), since by this
       point we have proven that C forms a basis. *)

    Lemma l_13_2_1 (U : set X) :
      (forall x : X, U x -> exists b : set X, C b /\ b x /\ subset b U) ->
      exists D, subset D C /\ U = big_union D.
    Proof.
      intro H2. exists (fun A => C A /\ subset A U).
      split. firstorder. apply extensionality; firstorder.
    Qed.

    (* C generates the topology. *)
    Lemma l_13_2_generates : generates lemma_13_2_Basis opens.
    Proof.
      unfold generates.
      intro U; split.
      - intro H2; apply l_13_2_1 in H2; destruct H2 as [E [H2 H3]].
        subst; destruct T.
        apply unionAxiom0; firstorder.
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
    Variable basis basis' : pow X.
    Context (B : @Basis basis) (B' : @Basis basis').
    Context (O : Opens X) (O' : Opens X).
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


Section subbasis.
  Variable X : Type.
  Notation D := (@full X).

  (** A subbasis S for a topology on D is a collection of subsets of D
      whose union equals D. *)

  Class SubbasisSet : Type :=
    subbasis : pow X.

  Definition subbasisAxiom (C : pow X) := big_union C = D.

  Class Subbasis (SBSet : SubbasisSet)
    : Type :=
    { subbasisAx : subbasisAxiom SBSet }.

  (* A subbasis gives rise to a basis by letting the basis elements be
     finite intersections of subbasis elements. *)

  Definition subbasis_basis (B : pow X) :=
    fun A => exists l, List.Forall B l /\ A = finite_intersection l.

  Program Instance subbasisBasis `(SB : Subbasis)
    : Basis (subbasis_basis subbasis).
  Next Obligation.
    intros x; destruct SB as [ax].
    assert (H0: full x) by firstorder. rewrite <- ax in H0.
    destruct H0 as [A [H0 H1]].
    exists A; firstorder.
    unfold subbasis_basis; subst.
    exists [A]; firstorder; apply extensionality; firstorder.
  Qed.
  Next Obligation.
    intros x b1 b2 [l1 [H0 H1]] [l2 [H2 H3]] [H4 H5].
    subst. rewrite Forall_forall in H0. rewrite Forall_forall in H2.
    exists (finite_intersection (l1 ++ l2)). split.
    - unfold subbasis_basis. exists (l1 ++ l2). split.
      + apply Forall_forall; intros y Hy.
        apply in_app_or in Hy; firstorder.
      + reflexivity.
    - split.
      + apply finite_intersection_app; assumption.
      + intros y Hy. split; auto.
        * apply finite_intersection_app_1 in Hy; assumption.
        * apply finite_intersection_app_2 in Hy; assumption.
  Qed.

(* Now that we can derive a basis from a subbasis, we can contruct a
   topology instance. *)
End subbasis.


(** Some results in this section rely on nonconstructive axioms. *)
Section closed.
  Variable X : Type.
  Notation D := (@full X).
  Context {O : Opens X} {T : Topology O}.

  Definition closed (A : set X) :=
    open (complement A).

  Definition all_closed (C : pow X) := forall A, C A -> closed A.

  Definition closure (A : set X) :=
    big_intersection (fun B => closed B /\ subset A B).

  Lemma complement_empty_equals_domain : complement (@empty X) = D.
  Proof. apply extensionality; firstorder. Qed.

  Lemma complement_domain_equals_empty : complement D = (@empty X).
  Proof. apply extensionality; firstorder. Qed.

  Lemma empty_closed : closed (@empty X).
  Proof.
    unfold closed; rewrite complement_empty_equals_domain; firstorder.
  Qed.

  Lemma domain_closed : closed D.
  Proof.
    unfold closed; rewrite complement_domain_equals_empty; firstorder.
  Qed.

  Lemma arbitrary_intersections_closed (C : pow X) :
    all_closed C -> closed (big_intersection C).
  Proof.
    intro Hclosed; unfold closed.
    destruct T as [_ _ unionAxiom intersectionAxiom].
    rewrite complement_subtract_full, demorgan_1_big.
    apply unionAxiom; intros A H0; subst.
    destruct H0 as [c [H0 H1]]; subst; firstorder.
  Qed.

  Lemma finite_unions_closed (A B : set X) :
    closed A ->
    closed B ->
    closed (union A B).
  Proof.
    intros HclosedA HclosedB; unfold closed.
    rewrite complement_subtract_full, demorgan_2; firstorder.
  Qed.

  Lemma closure_subset_domain (A : set X) :
    subset (closure A) D.
  Proof. firstorder. Qed.

  Lemma closure_closed (A : set X) :
    closed (closure A).
  Proof.
    unfold closed, closure.
    rewrite complement_subtract_full, demorgan_1_big.
    destruct T as [_ _ unionAxiom _]; apply unionAxiom.
    intros B H0; destruct H0 as [c [H1 H2]]; subst; firstorder.
  Qed.

  Lemma closed_equals_closure (A : set X) :
    closed A <-> A = closure A.
  Proof.
    split; intro H0.
    - apply extensionality; firstorder.
    - rewrite H0; apply closure_closed.
  Qed.

  Lemma complement_closure_open (A : set X) :
    O (complement (closure A)).
  Proof.
  Admitted.

  Lemma subset_closure (A U : set X) :
    closed U ->
    subset A U ->
    subset (closure A) U.
  Proof. firstorder. Qed.
End closed.


(* Given two topologies, form the basis for a binary product topology
   by letting basis elements be products of open sets of the two
   underlying topologies. *)
Section binaryProductTopology.
  Variable X Y : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Notation D := (@full (X*Y)).
  Context (O1 : Opens X) (T1 : Topology O1).
  Context (O2 : Opens Y) (T2 : Topology O2).

  Instance binaryProductBasisSet : BasisSet (X*Y) :=
    fun C => exists A B, O1 A /\ O2 B /\ C = product A B.

  Instance binaryProductBasis : Basis binaryProductBasisSet.
  Proof.
    constructor.
    - intros [x y].
      exists D; split.
      exists D1, D2; split. firstorder. split. firstorder.
      apply extensionality; split; intros [x' y'] H0; firstorder.
      firstorder.
    - intros [x y] b1 b2 Hb1 Hb2 Hint.
      destruct Hb1 as [A1 [B1 [Hb1 [Hb1' Hb1'']]]].
      destruct Hb2 as [A2 [B2 [Hb2 [Hb2' Hb2'']]]].
      subst. rewrite intersection_product in Hint.
      rewrite intersection_product.
      exists (product (intersection A1 A2) (intersection B1 B2)). split.
      + exists (intersection A1 A2), (intersection B1 B2); firstorder.
      + split; firstorder.
  Qed.

  Instance binaryProductOpens : Opens (X*Y) :=
    generate binaryProductBasisSet.

  Instance binaryProductTopology : Topology binaryProductOpens.
  Proof.
    apply (BasisTopology binaryProductBasis
                         binaryProductOpens
                         (generate_generates _)).
  Qed.
End binaryProductTopology.


(* Similar to above, but the basis elements are products of basis
   elements of the underlying topologies. *)
Section binaryProductBasisTopology.
  Variable X Y : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Notation D := (@full (X*Y)).
  Context (bsetX : BasisSet X) (BX : Basis bsetX).
  Context (bsetY : BasisSet Y) (BY : Basis bsetY).

  Instance binaryProductBasisSet' : BasisSet (X*Y) :=
    fun C => exists A B, bsetX A /\ bsetY B /\ C = product A B.

  Instance binaryProductBasis' : Basis binaryProductBasisSet'.
  Proof.
    constructor.
    - intros [x y].
      destruct BX as [ax1 _]. destruct BY as [ax1' _]. 
      specialize (ax1 x). specialize (ax1' y).
      destruct ax1 as [b [? ?]]. destruct ax1' as [b' [? ?]].
      exists (product b b'); firstorder.
    - intros [x y] b1 b2 Hb1 Hb2 Hint.
      destruct Hb1 as [A1 [B1 [Hb1 [Hb1' Hb1'']]]].
      destruct Hb2 as [A2 [B2 [Hb2 [Hb2' Hb2'']]]].
      subst.
      rewrite intersection_product in Hint.
      destruct Hint as [Hintx Hinty].
      rewrite intersection_product.
      destruct BX as [_ ax2]. destruct BY as [_ ax2'].
      specialize (ax2 x A1 A2 Hb1 Hb2 Hintx).
      specialize (ax2' y B1 B2 Hb1' Hb2' Hinty).
      destruct ax2 as [b [? [? ?]]].
      destruct ax2' as [b' [? [? ?]]].
      exists (product b b'). split. firstorder. split. firstorder.
      intros [x' y']; firstorder.
  Qed.

  Instance binaryProductBasisOpens : Opens (X*Y) :=
    generate binaryProductBasisSet'.

  Instance binaryProductBasisTopology : Topology binaryProductBasisOpens.
  Proof.
    apply (BasisTopology binaryProductBasis'
                         binaryProductBasisOpens
                         (generate_generates _)).
  Qed.

  Notation OX := (generate bsetX).
  Notation OY := (generate bsetY).

  (* Theorem 15.2 *)
  Instance binaryProductSubbasisSet : SubbasisSet (X*Y) :=
    union (fun A : set (X*Y) => exists U, OX U /\ A = preimage fst U)
          (fun A : set (X*Y) => exists V, OY V /\ A = preimage snd V).
  Instance binaryProductSubbasis : Subbasis binaryProductSubbasisSet.
  Proof.
    constructor. unfold subbasisAxiom. apply extensionality. split.
    - firstorder.
    - admit.
  Admitted.

  (* The product topology formed from products of basis elements is
     finer than the one formed from products of open sets. *)
  Lemma binary_products_finer :
    finer binaryProductBasisOpens
          (binaryProductOpens (generate bsetX) (generate bsetY)).
  Proof.
    intros x H0.
    destruct H0 as [C [H0 H1]]; subst.
    exists (fun A => binaryProductBasisSet' A /\ exists B, C B /\ subset A B).
    split.
    - firstorder.
    - apply extensionality; split.
      + firstorder.
      + intros [x y] [Z [H1 H2]].
        assert (H3: exists C0 : pow (X*Y), subset C0 binaryProductBasisSet' /\
                                    Z = big_union C0).
        { eapply l_13_2_1. apply binaryProductBasisTopology.
          firstorder; subst; firstorder.
          intros [x' y'] H3; specialize (H0 Z H1).
          destruct H0 as [A [B [[C' [H0 ?]] [[C'' [H4 ?]] ?]]]]; subst.
          destruct H3 as [[A [H3 H5]] [B [H6 H7]]].
          exists (product A B); split. 
          - exists A, B; firstorder.
          - split. firstorder. intros [? ?]; firstorder. }
        destruct H3 as [C0 [H3 ?]]; subst.
        destruct H2 as [Z [H2 H4]].
        exists Z; split; auto; split; auto.
        exists (big_union C0); split; auto; firstorder.
  Qed.
End binaryProductBasisTopology.


(** Theorem 17.5: Let A be a subset of the topological space D.
    a) Then x is in the closure of A iff every open set U containing x
       intersects A.
    b) Supposing the topology of X is given by a basis, then x is in
       the closure of A iff every basis element b containing x
       intersects A. *)
Section theorem_17_5.
  Variable X : Type.
  Notation D := (@full X).
  Context (O : Opens X) (T : Topology O).
  Variable A : set X.

  Lemma theorem_17_5_1 :
    forall x, closure A x <-> forall U, neighborhood U x -> intersects U A.
  Proof.
    intro x. split.
    - apply (@contrapositive
               (closure A x)
               (forall U : set X, neighborhood U x -> intersects (T:=X) U A)).
      intro H0.
      apply not_all_ex_not in H0; destruct H0 as [U H0].
      apply imply_to_and in H0; destruct H0 as [H0 ?].
      assert (closed (complement U)).
      { unfold closed; rewrite complement_cancel; firstorder. }
      assert (subset A (complement U)) by firstorder.
      assert (subset (closure A) (complement U)).
      { apply subset_closure; auto. }
      firstorder.
    - apply contrapositive; intro H0.
      assert (H1: exists U, neighborhood U x /\ ~ intersects U A).
      { exists (complement (closure A)). split.
        - split. 
          + apply complement_closure_open; auto.
          + firstorder.
        - firstorder. }
      intro HC; destruct H1 as [U [H1 H2]].
      specialize (HC U H1); congruence.
  Qed.

  (* A simple consequence of the above theorem. *)
  Lemma corollary_17_5_1 (U : set X) (x : X) :
    closure A x ->
    neighborhood U x ->
    exists y, intersects_at A U y.
  Proof.
    intros H0 [? ?]; rewrite theorem_17_5_1 in H0;
      specialize (H0 U); firstorder.
  Qed.


  Section theorem_17_5_2.
    Context (bset : BasisSet X) (B : Basis bset).
    Variable gen_pf : generates B O.

    Lemma theorem_17_5_2 :
      forall x, closure A x <-> forall b, bset b -> b x -> intersects b A.
    Admitted.
  End theorem_17_5_2.
End theorem_17_5.


Section limitPoint.
  Variable X : Type.
  Notation D := (@full X).
  Context (O : Opens X) (T : Topology O).

  (* x is a limit point of A. *)
  Definition limit_point (x : X) (A : set X) :=
    forall U, neighborhood U x -> exists y, y <> x /\ A y /\ U y.

  Definition limit_point' (x : X) (A : set X) :=
    closure (subtract A (singleton x)) x.

  Lemma limit_point_equiv (x : X) (A : set X) :
    limit_point x A <-> limit_point' x A.
  Admitted.

  Definition limit_points (A : set X) :=
    fun x => limit_point x A.

  Lemma jkdfgfd (A : set X) (x : X) :
    closure A x -> A x \/ limit_points A x.
  Admitted.

  (** Theorem 17.6: Let A be a subset of the topological space D. Then
    the closure of A is equal to the union of A with the set of all
    limit points of A. *)
  Lemma theorem_17_6 (A : set X) :
    closure A = union A (limit_points A).
  Proof.
    apply extensionality; split.
    - intros x H1. unfold closure in H1.
      unfold big_intersection in H1.
      assert (A x \/ limit_points A x).
      { apply jkdfgfd; firstorder. }
      firstorder.
    - intros x [H1 | H1].
      + firstorder.
      + apply theorem_17_5_1; firstorder.
  Qed.

  Lemma jkdfg (A : set X) :
    A = closure A <-> subset (limit_points A) A.
  Proof.
    split; intro H0.
    - rewrite H0. 
      intros x Hx.
      unfold closure, intersection.
      unfold limit_points, limit_point in Hx.
      + unfold big_intersection. intros B [H1 H2].
  Admitted.

  (** Corollary 17.7: A subset of a topological space is closed if and
    only if it contains all its limit points. *)
  Lemma corollary_17_7 (A : set X) :
    closed A <-> subset (limit_points A) A.
  Proof.
    split; intro H0.
    - intros x Hx. apply closed_equals_closure in H0; auto.
  Admitted.
End limitPoint.


Section hausdorff.
  Variable X : Type.
  Notation D := (@full X).
  Context (O : Opens X).

  (* There exist disjoint neighborhoods for distinct points. *)
  Definition hausdorff (T : Topology O) :=
    forall x1 x2,
      x1 <> x2 ->
      exists U1 U2, O U1 /\ O U2 /\ U1 x1 /\ U2 x2 /\ disjoint U1 U2.  
End hausdorff.


Section continuous.
  Variable X Y : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Context {O1 : Opens X} {T1 : Topology O1}.
  Context {O2 : Opens Y} {T2 : Topology O2}.
  Variable f : X -> Y.

  Definition continuous := forall V, O2 V -> O1 (preimage f V).

  (* TODO: If the topology on Y is generated by a basis B, then to
     show that f is continuous it suffices to show that the preimage
     of every basis element is open. *)
  (* Similarly, if the topology on Y is generated by a subbasis, it
     suffices to just show that the preimage of every subbasis element
     is open.*)

  Definition continuous_b :=
    forall A : set X,
      subset (image f (closure A)) (closure (image f A)).

  Definition continuous_c :=
    forall B : set Y, closed B -> closed (preimage f B).

  Definition continuous_at (x : X) :=
    forall (V : set Y),
      neighborhood V (f x) ->
      exists (U : set X), neighborhood U x /\ subset (image f U) V.

  Lemma theorem_18_1_1 :
    continuous -> continuous_b.
  Proof.
    intros H0 A y Hy.
    destruct Hy as [x [H1 H2]]; subst.
    apply theorem_17_5_1; auto.
    intros V [H2 H3]; specialize (H0 V H2).
    rewrite theorem_17_5_1 in H1; auto.
    specialize (H1 (preimage f V)); firstorder.
  Qed.

  Lemma theorem_18_1_2 :
    continuous_b -> continuous_c.
  Proof.
    intros H0 B H1. 
    set (A := preimage f B).
  Admitted.

  Lemma theorem_18_1_3 :
    continuous_c -> continuous.
  Proof.
  Admitted.

  Lemma theorem_18_1_4 :
    continuous <-> (forall x, continuous_at x).
  Proof.
  Admitted.
End continuous.


Section homeo.
  Variable X Y : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Context (O1 : Opens X) (T1 : Topology O1).
  Context (O2 : Opens Y) (T2 : Topology O2).
  Variable f : X -> Y.
  Variable f' : Y -> X.
  Variable pf : inverse f f'.

  Definition homeomorphism := continuous f /\ continuous f'.
End homeo.


(* A slightly different characterization of a homeomorphism: a
   bijective mapping such that the image of any open set is open. *)
Section homeo2.
  Variable X Y : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Context (O1 : Opens X) (T1 : Topology O1).
  Context (O2 : Opens Y) (T2 : Topology O2).
  Variable f : X -> Y.
  Variable pf : bijective f.

  Definition homeo2 := forall U, O2 (image f U) <-> O1 U.

  (* This definition is implied by the previous one, but I'm not sure
     if the converse can be proven (need the fact that bijection
     implies the existence of an inverse function). *)
  Lemma homeo_homeo2 f' :
    inverse f f' ->
    homeomorphism O1 O2 f f' ->
    homeo2.
  Proof.
    intros [H0 H1] [H2 H3] U.
    split; intros H4.
    - apply H2 in H4. 
      rewrite bijective_preimage_image_cancel in H4; auto.
    - assert (O1 (preimage f (image f U))).
      { rewrite bijective_preimage_image_cancel; auto. }
      apply H3 in H.
      rewrite bijective_preimage_image_cancel in H; auto.
      rewrite inverse_image_preimage with (f':=f'); firstorder.
  Qed.
End homeo2.


(* Most of the constructions are related to constraining / relaxing
   domains of functions so we can't really do them currently. *)
Section constructingContinuous.
  Variable X Y : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Context (O1 : Opens X) (T1 : Topology O1).
  Context (O2 : Opens Y) (T2 : Topology O2).

  (* Not constructive *)
  Lemma constant_continuous (f : X -> Y) (y : Y) :
    constant f y ->
    continuous f.
  Proof.
    intros Hc V H0. unfold constant in Hc.
    (* Is this necessary? y is either in V or not. *)
    destruct (classic (V y)).
    - erewrite preimage_constant_full; firstorder.
    - erewrite preimage_constant_empty; firstorder.
  Qed.
End constructingContinuous.


Section compositionContinuous.
  Variable X Y Z : Type.
  Notation D1 := (@full X).
  Notation D2 := (@full Y).
  Notation D3 := (@full Z).
  Context (O1 : Opens X) (T1 : Topology O1).
  Context (O2 : Opens Y) (T2 : Topology O2).
  Context (O3 : Opens Z) (T3 : Topology O3).

  Lemma composition_continuous (f : X -> Y) (g : Y -> Z) :
    continuous (compose g f).
  Proof.
  Admitted.
End compositionContinuous.


Section mapsIntoBinaryProducts.
  Variable A X Y : Type.
  Notation DA := (@full A).
  Notation DX := (@full X).
  Notation DY := (@full Y).
  Context (OA : Opens A) (TA : Topology OA).
  Context (OX : Opens X) (TX : Topology OX).
  Context (OY : Opens Y) (TY : Topology OY).
  Variable f : A -> X.
  Variable g : A -> Y.

  Notation OP := (binaryProductOpens OX OY).
  Notation OT := (binaryProductTopology TX TY).

  Definition h := fun a => (f a, g a).

  Lemma binary_product_map_continuous :
    @continuous _ _ _ OP h <-> continuous f /\ continuous g.
  Proof.
    split.
    - intro H0; split.
      + admit.
      + admit.
    - intros [H0 H1].
      admit.
  Admitted.
End mapsIntoBinaryProducts.


Section boxTopology.
  Variable J : Type. (* Index set *)
  Variable X : J -> Type.
  Variable O : J_tuple (fun j => Opens (X j)).
  Variable T : J_tuple (fun j => Topology (@O j)).

  Instance boxBasisSet : BasisSet (J_tuple X) :=
    fun A => exists x, forall j, O (x j) /\ A = cartesian_product x.

  Instance boxBasis : Basis boxBasisSet.
  Proof.
    constructor.
    - intro j; exists (@full _); firstorder.
      exists (fun j => @full (X j)); firstorder.
      apply extensionality; firstorder.
    - intros f b1 b2 [f1 Hb1] [f2 Hb2] ?.
      exists (intersection b1 b2); firstorder.
      exists (family_setwise_intersection f1 f2).
      intro j; destruct (Hb1 j); destruct (Hb2 j); subst;
        firstorder; apply intersection_cartesian_product.
  Qed.

  Instance boxOpens : Opens (J_tuple X) :=
    generate boxBasisSet.

  Instance boxTopology : Topology boxOpens.
  Proof.
    apply (BasisTopology boxBasis boxOpens (generate_generates _)).
  Qed.
End boxTopology.


(* General product topology *)
Section productTopology.
  Variable J : Type. (* Index set *)
  Variable j0 : J. (* J is nonempty *)
  Variable X : J -> Type.
  Variable O : J_tuple (fun j => Opens (X j)).
  Variable T : J_tuple (fun j => Topology (@O j)).

  Definition S_beta (j : J) : pow (J_tuple X) :=
    fun s => exists U, O U /\ s = preimage (proj j) U.

  (* The above definition with explicit type annotations *)
  (* fun s : set (J_tuple X) => *)
  (*   exists U : set (X j), *)
  (*     @O j U /\ s = preimage (@proj J X j) U. *)

  (* Subbasis for the product topology. *)
  Instance productSubbasisSet : SubbasisSet (J_tuple X) :=
    family_union S_beta.

  Instance productSubbasis : Subbasis productSubbasisSet.
  Proof.
    constructor; apply extensionality; split.
    - firstorder.
    - intros f Hf; exists (@full _); split; firstorder.
  Qed.

  Instance productBasisSet : BasisSet (J_tuple X) :=
    subbasis_basis productSubbasisSet.

  Instance productBasis : Basis productBasisSet.
  Proof. apply subbasisBasis, productSubbasis. Qed.

  Instance productOpens : Opens (J_tuple X) :=
    generate productBasisSet.

  Instance productTopology : Topology productOpens.
  Proof.
    apply (BasisTopology productBasis productOpens
                         (generate_generates _)).
  Qed.
End productTopology.


(*****************)
(** Begin Grappa *)

Section lemma1.
  Variable X : Type.
  Notation D := (@full X).
  Context {O : Opens X} {T : Topology O}.
  Variable B : pow X.
  Variable pf : forall U, O U -> exists C, subset C B /\ big_union C = U.

  Instance basisInstance : Basis B.
  Proof.
    constructor.
    - intros x; assert (H0: D x) by firstorder.
      assert (H1: O D) by firstorder.
      specialize (pf H1); destruct pf as [C [H2 H3]].
      rewrite <- H3 in H0; firstorder.
    - admit.
      (* Not sure about this. *)
  Admitted.

  Lemma exists_topology : exists T, generates basisInstance T.
  Proof. exists (generate B); apply generate_generates. Qed.

  Lemma topology_unique : forall T1 T2,
      generates basisInstance T1 ->
      generates basisInstance T2 ->
      T1 = T2.
  Proof.
    intros T1 T2 Hgen1 Hgen2; apply extensionality; firstorder.
  Qed.
End lemma1.
