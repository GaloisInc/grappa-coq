Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import QArith.
Require Import Coq.micromega.Lqa.

Require Import GrappaCoq.Domain GrappaCoq.Set.


(** Intervals with rational endpoints. *)

Section interval.
  (* CompleteQI represents the entire space of rationals, i.e.,
     (-∞, ∞). *)
  Inductive qI :=
  | CompleteQI
  | BoundedQI : Q -> Q -> qI.

  (* q is in interval I. *)
  Definition inI (I : qI) (q : Q) :=
    match I with
    | CompleteQI => True
    | BoundedQI l h => l <= q /\ q <= h
    end.

  Definition qMin (a b : Q) :=
    if Qlt_le_dec a b then a else b.
  Definition qMax (a b : Q) :=
    if Qlt_le_dec a b then b else a.

  (* The intersection of two intervals. *)
  Definition intersectionI (I1 I2 : qI) : qI :=
    match I1, I2 with
    | CompleteQI, _ => I2
    | _, CompleteQI => I1
    | BoundedQI l1 h1, BoundedQI l2 h2 =>
      BoundedQI (qMax l1 l2) (qMin h1 h2)
    end.

  (* I1 is a subset of I2. *)
  Definition subsetI (I1 I2 : qI) :=
    forall x, inI I1 x -> inI I2 x.
End interval.

Notation "x '∈' a" := (inI a x) (at level 65).
Notation "x '∉' a" := (~ inI a x) (at level 65).
Notation "a '∩' b" := (intersectionI a b) (at level 65).
Notation "a '⊆' b" := (subsetI a b) (at level 65).


Section intervalFacts.
  Lemma intersection_complete (A : qI) :
    A ∩ CompleteQI = A.
  Proof. destruct A; auto. Qed.

  Lemma subsetI_refl (A : qI) :
    A ⊆ A.
  Proof. firstorder. Qed.

  Lemma subsetI_trans (A B C : qI) :
    A ⊆ B -> B ⊆ C -> A ⊆ C.
  Proof. firstorder. Qed.

  Lemma intersectionI_subsetI_1 (A B : qI) :
    (A ∩ B) ⊆ A.
  Proof.
    intros x H0; unfold inI in *; unfold intersectionI in H0.
    destruct A; destruct B; auto.
    unfold qMax, qMin in H0.
    destruct (Qlt_le_dec q q1); destruct (Qlt_le_dec q0 q2); lra.
  Qed.

  Lemma intersectionI_subsetI_2 (A B : qI) :
    (A ∩ B) ⊆ B.
  Proof.
    intros x H0; unfold inI in *; unfold intersectionI in H0.
    destruct A; destruct B; auto.
    unfold qMax, qMin in H0.
    destruct (Qlt_le_dec q q1); destruct (Qlt_le_dec q0 q2); lra.
  Qed.

  Lemma intersectionI_inI_1 (A B : qI) (x : Q) :
    x ∈ (A ∩ B) -> x ∈ A.
  Proof.
    intros H0; unfold inI, intersectionI, qMax, qMin in *.
    destruct A; destruct B; auto.
    destruct (Qlt_le_dec q q1); destruct (Qlt_le_dec q0 q2); lra.
  Qed.

  Lemma intersectionI_inI_2 (A B : qI) (x : Q) :
    x ∈ (A ∩ B) -> x ∈ B.
  Proof.
    intros H0; unfold inI, intersectionI, qMax, qMin in *.
    destruct A; destruct B; auto.
    destruct (Qlt_le_dec q q1); destruct (Qlt_le_dec q0 q2); lra.
  Qed.

  Lemma subsetI_intersectionI_1 (A B C : qI) :
    A ⊆ (B ∩ C) -> A ⊆ B.
  Proof.
    intros H0 x H1.
    specialize (H0 x H1).
    eapply intersectionI_inI_1; eauto.
  Qed.

  Lemma subsetI_intersectionI_2 (A B C : qI) :
    A ⊆ (B ∩ C) -> A ⊆ C.
  Proof.
    intros H0 x H1.
    specialize (H0 x H1).
    eapply intersectionI_inI_2; eauto.
  Qed.

  Lemma inI_intersectionI (A B : qI) (x : Q) :
    x ∈ A -> x ∈ B -> x ∈ (A ∩ B).
  Proof.
    intros H0 H1; unfold inI, intersectionI, qMax, qMin in *.
    destruct A; destruct B; auto.
    destruct (Qlt_le_dec q q1); destruct (Qlt_le_dec q0 q2); lra.
  Qed.
End intervalFacts.

Notation "'val' x" := (proj1_sig x) (at level 10).


(** "Pseudo-reals": infinite sequences of intervals with rational
    endpoints such that each interval is a subset of its
    predecessor. *)

Section pseudoReal.
  Definition rAx (f : nat -> qI) := forall j, (f (S j)) ⊆ (f j).
  Definition R := { f : nat -> qI | rAx f }.

  (* The approximation ordering on pseudo-reals. *)
  (* For every interval I1 in r1, there exists an interval I2 in r2
     such that I2 is a subset of I1. *)
  Definition Rle (r1 r2 : R) :=
    forall i, exists j, subsetI (val r2 j) (val r1 i).

  (* Antisymmetry wrt strict equality seems to not hold. *)

  Program Definition Rbot : R :=
    fun _ => CompleteQI.
  Next Obligation. firstorder. Qed.
End pseudoReal.

Notation "x '⊑' y" := (Rle x y) (at level 65).


(** Ascending chains of pseudo-reals. *)

Section chain.
  Definition chainAx (g : nat -> R) := forall j, (g j) ⊑ (g (S j)).
  Definition chain := { g : nat -> R | chainAx g }.

  (* Finite subchains (lists). Not used at the moment. *)
  Inductive subchainAx : list R -> chain -> nat -> Prop :=
  | subchainNil : forall A, subchainAx nil A 0
  | subchainCons : forall l A n,
      subchainAx l A n ->
      subchainAx (val A n :: l) A (S n).
  Definition subchain A n := { l : list R | subchainAx l A n }.

  Program Fixpoint subchain_of (A : chain) (n : nat) : subchain A n :=
    match n with
    | O => []
    | S n' => val A n' :: subchain_of A n'
    end.
  Next Obligation. constructor. Qed.
  Next Obligation.
    inversion s; subst; constructor; constructor; auto.
  Defined.

  Definition subchain_intersection_i A n (C : subchain A n) i :=
    fold_right (fun x acc => val x i ∩ acc) CompleteQI (val C).

  (* End subchains *)

  (* x is an upper bound of chain A. *)
  Definition upper_bound (x : R) (A : chain) :=
    forall j, Rle (val A j) x.
End chain.


(* Computing the supremum of a chain of pseudo-reals. *)

Section supremum.
  (* Auxiliary function that does most of the work. *)
  Fixpoint RsupAux (A : chain) (j k : nat) :=
    match k with
    | O => CompleteQI
    | S k' => val (val A k') j ∩ RsupAux A j k'
    end.

  Lemma sup_pf1 A j k :
    RsupAux A j (S k) ⊆ RsupAux A j k.
  Proof.
    intros x H0; apply intersectionI_subsetI_2 in H0; auto.
  Qed.

  Lemma sup_pf2 A j k :
    RsupAux A (S j) k ⊆ RsupAux A j k.
  Proof.
    intros x H0; induction k; auto; simpl in *.
    assert (H1: inI ((val ((val A) k)) (S j)) x).
    { apply intersectionI_subsetI_1 in H0; auto. }
    assert (H2: inI (RsupAux A (S j) k) x).
    { apply intersectionI_subsetI_2 in H0; auto. }
    apply inI_intersectionI; auto.
    destruct A as [q ?]; simpl in *.
    destruct (q k) as [qI ax]; simpl in *.
    apply ax; assumption.
  Qed.

  Lemma lem1 (A : chain) j x :
    x ∈ RsupAux A j (S j) ->
    x ∈ val ((val A) j) j.
  Proof.
    intros H0. induction j.
    - simpl in *. rewrite intersection_complete in H0; assumption.
    - simpl in H0; eapply intersectionI_subsetI_1; eauto.
  Qed.

  (* The supremum of chain A. *)
  Program Definition Rsupremum (A : chain) : R :=
    fun j => RsupAux A j (S j).
  Next Obligation.
    intros i x H0.
    assert (H1: inI ((val ((val A) (S i))) (S i)) x).
    { apply intersectionI_subsetI_1 in H0; auto. }
    assert (H2: inI (RsupAux A (S i) (S i)) x).
    { apply intersectionI_subsetI_2 in H0; auto. }
    apply inI_intersectionI.
    - apply lem1, sup_pf2; auto.
    - apply sup_pf1, sup_pf2; auto.
  Qed.
End supremum.

Notation "'⊔' r" := (Rsupremum r) (at level 65) : pseudoreal_scope.
Open Scope pseudoreal_scope.


Section pseudoRealFacts.
  Lemma rAx_le (r : R) (i j : nat) :
    (i <= j)%nat ->
    val r j ⊆ val r i.
  Proof.
    intros H0 x H1; destruct r as [f ax]; simpl in *.
    induction H0; auto; apply ax in H1; auto.
  Qed.

  Lemma rAx_lt (r : R) (i j : nat) :
    (i < j)%nat ->
    val r j ⊆ val r i.
  Proof.
    intros H0 x H1; destruct r as [f ax]; simpl in *.
    induction H0; auto; apply ax in H1; auto.
  Qed.

  Lemma Rle_refl x : x ⊑ x.
  Proof. firstorder. Qed.

  Lemma Rle_trans x y z :
    x ⊑ y -> y ⊑ z -> x ⊑ z.
  Proof.
    intros H0 H1 i.
    destruct (H0 i) as [j H2]; destruct (H1 j) as [k H3].
    exists k; intro q; eapply subsetI_trans; eauto.
  Qed.

  Lemma Rbot_bottom :
    forall r, Rbot ⊑ r.
  Proof. firstorder. Qed.

  Lemma chainAx_trans (A : chain) (i j : nat) :
    (i <= j)%nat ->
    val A i ⊑ val A j.
  Proof.
    intros H0; destruct A.
    induction H0. apply Rle_refl.
    eapply Rle_trans; eauto.
  Qed.
End pseudoRealFacts.


Section supremumFacts.
  Lemma lem2 (A : chain) j :
    val (⊔ A) j ⊆ val (val A j) j.
  Proof. intros ? ?; apply lem1; auto. Qed.

  (* Lemma lem3 (A : chain) j : *)
  (*   subsetI ((val (supremum A)) (S j)) ((val ((val A) j)) (S j)). *)
  (* Proof. *)
  (*   simpl; intros x H0. *)
  (*   apply intersectionI_subsetI_2, intersectionI_subsetI_1 in H0. *)
  (*   assumption. *)
  (* Qed. *)

  Lemma lem3 (A : chain) i j k :
    (j <= i)%nat ->
    RsupAux A k i ⊆ RsupAux A k j.
  Proof.
    intros H0 x H1.
    induction H0; auto.
    apply IHle. apply sup_pf1; auto.
  Qed.

  (* Lemma lem4 (A : chain) i j : *)
  (*   (j <= i)%nat -> *)
  (*   subsetI (supAux A i j) (supAux A j j). *)
  (* Proof. *)
  (*   intros H0 x H1. *)
  (*   induction H0; auto. *)
  (*   apply IHle. *)
  (*   apply sup_pf2; auto. *)
  (* Qed. *)

  Lemma lem4 (A : chain) i j :
    (j <= i)%nat ->
    RsupAux A i (S j) ⊆ val (val A j) i.
  Proof.
    intros H0 x H1.
    simpl in *.
    apply intersectionI_subsetI_1 in H1; auto.
  Qed.

  Lemma lem5 (A : chain) j i :
    (j <= i)%nat ->
    val (⊔ A) i ⊆ (val ((val A) j)) i.
  Proof.
    intros H0.
    assert (subsetI (RsupAux A i (S i)) (RsupAux A i (S j))).
    { apply lem3; omega. }
    eapply subsetI_trans. apply H. apply lem4; auto.
  Qed.

  (* [Rsupremum A] is an upper bound of A. *)
  Lemma Rsupremum_upper_bound (A : chain) :
    upper_bound (⊔ A) A.
  Proof.
    (* jth element in the chain *)
    (* ith interval of that element *)
    intros j i. exists (max j i).
    destruct (Nat.le_decidable j i).
    - rewrite max_r; auto.
      induction H. apply lem2; auto.
      apply lem5; omega.
    - rewrite max_l; try omega.
      apply Nat.nle_gt in H.
      (* Since the intervals are decreasing and the jth interval comes
         after the ith, we have that the jth interval is a subset of
         the ith interval.
         We also have that the jth interval of the supremum is a
         subset of the jth interval of the element, so by transitivity
         it's a subset of the ith interval of the element. *)
      set (r := (val ((val A) j))).
      assert (H0: subsetI (r j) (r i)) by (apply rAx_lt; auto).
      assert (H1: subsetI (val (Rsupremum A) j) (r j)).
      { intros x H1; apply lem1; auto. }
      eapply subsetI_trans; eauto.
  Qed.

  (* The last element A_j of a finite prefix of a chain is an upper
     bound of the prefix, so for every element A_i in it there is an
     interval in A_j that is a subset of the kth interval of A_i. *)
  Lemma lem6 (A : chain) i j k :
    (i <= j)%nat ->
    exists l, val (val A j) l ⊆ val (val A i) k.
  Proof.
    intros H0.
    assert (Rle (val A i) (val A j)).
    { apply chainAx_trans; auto. }
    specialize (H k); auto.
  Qed.

  (* A slight generalization of lem9. *)
  Lemma lem7 (j : nat) (P : nat -> nat -> Prop) :
    (forall i l l', P l i -> (l <= l')%nat -> P l' i) ->
    (forall i, (i <= j)%nat -> exists l, P l i) ->
    exists l, forall i, (i <= j)%nat -> P l i.
  Proof.
    intros H0 H1; induction j.
    - specialize (H1 O (le_n O)); destruct H1 as [l H1].
      exists l. intros i H2.
      assert (i = O) by omega; subst; auto.
    - assert (H2: forall i : nat, (i <= j)%nat ->
                                  exists l : nat, P l i) by auto.
      specialize (IHj H2); clear H2; destruct IHj as [l H3].
      specialize (H1 (S j) (le_n (S j))); destruct H1 as [l' H1].
      destruct (Nat.leb_spec0 l l').
      + exists l'; intros i H2.
        destruct (Nat.eqb_spec i (S j)); subst; auto.
        assert (i <= j)%nat by omega.
        eapply H0; eauto.
      + exists l; intros i H2.
        destruct (Nat.eqb_spec i (S j)); subst.
        * eapply H0. apply H1. omega.
        * apply H3; omega.
  Qed.

  Lemma lem8 (r1 r2 : R) i l l' :
    (l <= l')%nat ->
    val r2 l ⊆ val r1 i ->
    val r2 l' ⊆ val r1 i.
  Proof.
    intros H0 H1.
    apply subsetI_trans with (B:=val r2 l); auto.
    apply rAx_le; auto.
  Qed.

  (* lem6 gives us an interval in A_j for each A_i. One of them is the
     smallest (largest index). That interval is a subset of the kth
     interval for every i. This means it's a subset of their
     intersection, a fact we use below. *)
  Lemma lem9 (A : chain) j k :
    (forall i, (i <= j)%nat ->
          exists l, val (val A j) l ⊆ val (val A i) k) ->
    exists l, forall i, (i <= j)%nat ->
              val (val A j) l ⊆ val (val A i) k.
  Proof.
    intros H0.
    apply lem7; auto.
    intros i l l' H1 H2. eapply lem8; eauto.
  Qed.

  (* Given the fact proven in lem9, we prove that the given interval I
     is a subset of the kth interval of the supremum, since I is just
     the intersection of the kth intervals of the first j elements. *)
  Lemma lem10 (A : chain) I j k :
    (forall i, (i <= j)%nat ->
          I ⊆ val (val A i) k) ->
    I ⊆ RsupAux A k (S j).
  Proof.
    generalize dependent k. induction j; intros k H0; simpl in *.
    - rewrite intersection_complete.
      specialize (H0 O (le_n O)); assumption.
    - intros x H1.
      apply inI_intersectionI.
      + apply H0; auto.
      + apply inI_intersectionI.
        * apply H0; auto.
        * specialize (IHj k).
          assert (H2: forall i : nat, (i <= j)%nat ->
                               subsetI I ((val ((val A) i)) k)).
          { intros i H2; assert (H3: (i <= S j)%nat) by omega.
            specialize (H0 i H3); auto. }
          specialize (IHj H2); clear H2.
          apply subsetI_intersectionI_2 in IHj; auto.
  Qed.

  (* [Rsupremum A] is "less than" any upper bound of A. *)
  Lemma Rsupremum_le_upper_bounds (A : chain) :
    forall b, upper_bound b A -> ⊔ A ⊑ b.
  Proof.
    intros b H0 j.
    assert (exists l, forall i, (i <= j)%nat -> val (val A j) l ⊆ val (val A i) j).
    apply lem9. intros i' H1. apply lem6; auto.
    destruct H as [i' H].
    apply lem10 in H; auto.
    specialize (H0 j i'); destruct H0 as [k H0].
    exists k; eapply subsetI_trans; eauto.
  Qed.

  (* [Rsupremum A] is the least upper bound of A. *)
  Lemma Rsupremum_lub (A : chain) :
    upper_bound (⊔ A) A /\
    forall s, upper_bound s A -> ⊔ A ⊑ s.
  Proof.
    split.
    - apply Rsupremum_upper_bound.
    - apply Rsupremum_le_upper_bounds.
  Qed.
End supremumFacts.


(* The pseudo-reals form an ω-DCPO. *)
Section pseudoRealDomain.
  Open Scope domain_scope.
  Instance pseudoRealOrder : PosetOrder := Rle.

  Program Instance pseudoRealPoset : Poset pseudoRealOrder.
  Next Obligation. apply Rle_refl. Qed.
  Next Obligation. eapply Rle_trans; eauto. Qed.

  Instance pseudoRealBottom : Bottom := Rbot.

  Program Instance pseudoRealPointedPoset
    : PointedPoset pseudoRealPoset pseudoRealBottom.
  Next Obligation. unfold bottomAxiom; apply Rbot_bottom. Qed.

  Instance pseudoRealSupremum : OmegaSupremum pseudoRealPoset :=
    Rsupremum.

  Program Instance pseudoRealOmegaDCPO : OmegaDCPO pseudoRealSupremum.
  Next Obligation. apply Rsupremum_lub. Qed.
End pseudoRealDomain.
