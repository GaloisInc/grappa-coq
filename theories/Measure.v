Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import QArith Coq.micromega.Lqa.

Require Import GrappaCoq.Domain GrappaCoq.Pseudoreal GrappaCoq.Rational
        GrappaCoq.Real GrappaCoq.Set GrappaCoq.Topology.


Section measure.
  Context {X : Type} {O : Opens X} {T : Topology O}.

  Class MeasureFun : Type :=
    mu : set X -> eR.

  Notation "'μ' U" := (mu U) (at level 65) : measure_scope.
  Open Scope measure_scope.

  Class Measure (M : MeasureFun) : Prop :=
    { measureEmptyAx : μ (@empty X) = eRzero;
      measureAddAx : forall C : sequence (set X),
          countable_disjoint C ->
          μ (countable_union C) = eR_sequence_sum (fun i => μ (C i)) }.
End measure.

Notation "'μ' U" := (mu U) (at level 65) : measure_scope.
Open Scope measure_scope.


Section lebesgue.
  Existing Instance eROrder.
  
  (** The Lebesgue measure of the set E is the infimum of the set of
      sums of lengths of sequences of intervals that cover E. *)
  Definition lebesgue_measure (E : set R) : eR :=
    eRInfimum (fun x =>
                 (* The set of values x such that: *)
                 (* there exists a sequence of intervals f *)
                 exists f : nat -> qI,
                   (* such that every r ∈ E is in the union of f *)
                   (forall r, r ∈ E ->
                         R_in_set r (⋃ set_of_sequence
                                       (map_sequence set_of_qI f))) /\
                   (* and x equals the sum of their lengths *)
                   x ~~ eR_sequence_sum (map_sequence qI_length f)).

  (** The Lebesgue measure of the empty set is zero. *)
  Lemma lebesque_empty : lebesgue_measure (@empty R) = eRzero.
  Proof.
    destruct (lebesgue_measure _) as [x Hx] eqn:H0; inversion H0 as [H1].
    destruct eRzero as [x0 Hx0] eqn:H2; inversion H2 as [H3].
    assert (H4: x = x0).
    { apply extensionality; subst; split.
      - intros x (A & (r & (f & [H3 H4]) & H5) & H6); subst.
        destruct r as (r & Hr & ?); apply Hr; auto.
      - intros x H3; eexists; split; eauto.
        exists eRzero; split; auto.
        exists (fun _ => BoundedQI 0 0); split.
        + intros ? Hr; inversion Hr.
        + split.
          * intros y [[_ Hy] _]; auto.
          * intros y Hy; simpl in *.
            assert (Hzero: 0 - 0 = 0) by auto; split.
            -- split; auto; intros ? [? [[i ?] ?]]; subst.
               unfold map_sequence; simpl; rewrite Hzero.
               rewrite eR_of_Q_0; rewrite sum_list_const_0; auto.
            -- exists (y / (2#1)); split.
               ++ split.
                  ** intros A [r [HA ?]]; subst.
                     destruct HA as [i ?]; subst.
                     unfold map_sequence; simpl; rewrite Hzero.
                     rewrite eR_of_Q_0; rewrite sum_list_const_0; auto.
                     rewrite H2; simpl; unfold positive_rationals in *.
                     apply Qlt_shift_div_l; lra.
                  ** unfold positive_rationals in *.
                     apply Qlt_shift_div_l; lra.
               ++ unfold lt; split.
                  ** apply Qdiv_2_not_equiv; auto.
                  ** apply Qdiv_2_le; auto. }
    apply subset_PI; auto.
  Qed.

  (** The Lebesgue measure of a sequence of disjoint sets is equal to
      the sum of their individual measures. *)
  Lemma lebesque_additivity :
    forall C : sequence (set R),
      countable_disjoint C ->
      lebesgue_measure (countable_union C) =
      eR_sequence_sum (fun i => lebesgue_measure (C i)).
  Proof. Admitted.

  Instance lebesgueMeasureFun : MeasureFun := lebesgue_measure.
End lebesgue.
