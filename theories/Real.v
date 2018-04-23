Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import QArith.
Require Import Coq.micromega.Lqa.

Require Import GrappaCoq.Domain GrappaCoq.Set.


(** A Poset instance for Coq rationals. *)
Section rationalPoset.
  Instance rationalOrder : PosetOrder := Qle.
  Program Instance rationalPoset : Poset rationalOrder.
  Next Obligation. unfold le, rationalOrder; lra. Qed.
  Next Obligation. unfold equiv, le, rationalOrder in *; lra. Qed.
End rationalPoset.


(** Constructive non-negative reals extended with +∞. *)
Section extendedReal.
  Existing Instance rationalOrder.
  Existing Instance rationalPoset.

  Definition eRAx (A : set Q) :=
    (forall x, x ∈ A -> 0 < x) /\ is_upper_set A /\ no_least A.
  Definition eR := { A : set Q | eRAx A }.

  Definition Rle (r1 r2 : eR) :=
    val r2 ⊆ val r1.

  Open Scope domain_scope.
  Instance eROrder : PosetOrder := Rle.  

  Program Instance eRPoset : Poset eROrder.
  Solve Obligations with firstorder.

  Definition positive_rationals : set Q := fun x => 0 < x.

  Program Definition eRtop : eR := (@empty Q).
  Next Obligation. firstorder. Qed.

  Lemma Qdiv_mult_shift :
    forall x y z, ~ y == 0 -> x / y * z == x * z / y.
  Proof. intros x y z Hy; field; auto. Qed.

  Program Definition eRbot : eR := positive_rationals.
  Next Obligation.
    split.
    - firstorder.
    - split.
      + intros x y H0 H1; unfold positive_rationals, in_set in *.
        unfold le, rationalOrder in H0; lra.
      + intros x H0; exists (x / (2#1)); split.
        * unfold in_set, positive_rationals in *.
          apply Qlt_shift_div_l; lra.
        * unfold lt, equiv, le, in_set, rationalOrder,
          positive_rationals in *; split.
          -- intros [H1 H2].
             assert (x == x / (2 # 1)) by lra.
             assert (x * (2#1) == x / (2#1) * (2#1)).
             { apply Qmult_inj_r; lra. }
             rewrite Qdiv_mult_shift in H3; try lra.
             rewrite Qdiv_mult_l in H3; lra.
          -- apply Qle_shift_div_r; lra.
  Qed.

  Notation "+∞" := eRtop : real_scope.
  Open Scope real_scope.

  Lemma eRtop_top :
    forall r, r ⊑ +∞.
  Proof. firstorder. Qed.

  Lemma eRbot_bot :
    forall r, eRbot ⊑ r.
  Proof.
    unfold le, eROrder, Rle, eRbot.
    intros r; destruct r; simpl; firstorder.
  Qed.

  (** The supremum is the intersection of the sets of rationals. We
      must also intersect with positive_rationals in case A is empty,
      and then ensure that there is no least element. *)
  Program Definition eRSupremum (A : set eR) : eR :=
    without_least (⋂ image (@proj1_sig _ _) A ∩ positive_rationals).
  Next Obligation.
    split.
    - intros x [[_ H0] _]; assumption.
    - split.
      + intros x y H0 H1.
        destruct H1 as [H1 (z & H2 & H3)].
        split.
        * split.
          -- intros B ([w (H4 & H5 & H6)] & HB & ?); simpl in *; subst.
             eapply H5; eauto; apply H1.
             exists (exist (fun A : set Q => eRAx A) _ (conj H4 (conj H5 H6))).
             subst; split; auto.
          -- unfold le, rationalOrder in H0.
             unfold positive_rationals in *.
             destruct H1; lra.
        * exists z; split; auto.
          unfold lt, equiv, le, rationalOrder in *; lra.
      + apply no_least_without_least.
        intros a b H0 H1 H2.
        exists ((a + b) / (2#1)); split.
        * assert (H3: forall c, a ⊑ c ->
                           c ∈ ⋂ image
                             (proj1_sig (P:=fun A : set Q => eRAx A)) A).
          { intros c Hc B (z & H3 & ?); subst.
            destruct H0 as [H0 H0']; specialize (H0 (val z)).
            assert (exists x : {A : set Q | eRAx A}, x ∈ A /\ val x = val z).
            { exists z; auto. }
            apply H0 in H.
            destruct z as [z (H4 & H5 & H6)]; simpl in *.
            eapply H5; eauto. }
          split.
          -- apply H3; unfold lt, le, rationalOrder in *.
             apply Qle_shift_div_l; lra.
          -- unfold lt, equiv, le, rationalOrder in H2.
             destruct H2 as [H2 H4].
             destruct H0; destruct H1; unfold positive_rationals in *.
             apply Qlt_shift_div_l; lra.
        * unfold lt, equiv, le, rationalOrder in *.
          destruct H2 as [H2 H3].
          assert (a < b) by lra.
          assert (H4: forall x y z, ~ y == 0 -> x / y * z == x * z / y).
          { intros x y z Hy; field; auto. }
          split.
          -- split.
             ++ intros [H5 H6].
                assert (a == (a + b) / (2 # 1)) by lra.
                assert (Hx: a * (2#1) == (a + b) / (2#1) * (2#1)).
                { apply Qmult_inj_r; lra. }
                rewrite H4 in Hx; try lra.
                rewrite Qdiv_mult_l in Hx; lra.
             ++ apply Qle_shift_div_l; lra.
          -- split.
             ++ intros [H5 H6].
                assert (b == (a + b) / (2 # 1)) by lra.
                assert (Hx: b * (2#1) == (a + b) / (2#1) * (2#1)).
                { apply Qmult_inj_r; lra. }
                rewrite H4 in Hx; try lra.
                rewrite Qdiv_mult_l in Hx; lra.
             ++ apply Qle_shift_div_r; lra.
  Qed.

  Program Definition eRInfimum (A : set eR) : eR:=
    big_union (image (@proj1_sig _ _) A).
  Next Obligation.
    split.
    - intros x (B & ([y (Hy & ? & ?)] & H0 & H1) & H2).
      subst; simpl in *; apply Hy; auto.
    - split.
      + intros x y H0 (B & ([z (? & Hz1 & ?)] & H1 & H3) & H2).
        exists B; split; subst; firstorder; eapply Hz1; eauto.
      + intros x (B & ([C HC] & H1 & H2) & H3); subst; simpl in *.
        destruct HC as [H0 H2]; apply H2 in H3.
        destruct H3 as (y & H3 & H4).
        exists y; split; auto.
        exists C; split; auto; eexists; eauto.
  Qed.

  Notation "'⊔' x" := (eRSupremum x) (at level 65) : real_scope.
  Notation "'⊓' x" := (eRInfimum x) (at level 65) : real_scope.

  Lemma eRSupremum_is_supremum (A : set eR) :
    is_supremum (⊔ A) A.
  Proof.
    unfold is_supremum. split.
    - intros y Hy x Hx; apply Hx; exists y; firstorder.
    - intros s Hs x Hx. split. split.
      + eapply big_intersection_largest_subset; eauto.
        intros B (z & HB & ?); subst.
        specialize (Hs z HB); firstorder.
      + destruct s; destruct e; apply q; assumption.
      + destruct s; destruct e as (H0 & H1 & H2).
        apply H2 in Hx; destruct Hx as (y & H3 & H4).
        exists y; split; auto; split.
        * eapply big_intersection_largest_subset; eauto.
          intros B (z & HB & ?); subst.
          apply Hs; assumption.
        * apply H0; assumption.
  Qed.

  Lemma eRInfimum_is_infimum (A : set eR) :
    is_infimum (⊓ A) A.
  Proof.
    split.
    - intros y Hy x Hx; exists (val y); split; auto; exists y; split; auto.
    - intros y Hy x (B & (z & H0 & ?) & H1); subst.
      assert (y ⊑ z) by (apply Hy; auto).
      destruct y; destruct z; simpl in *; firstorder.
  Qed.
End extendedReal.

(** The non-negative reals extended with +∞ form a complete lattice. *)
Section extendedRealDomain.
  Program Instance eRCompleteLattice :
    @CompleteLattice _ _ eRPoset eRSupremum eRInfimum.
  Next Obligation. apply eRSupremum_is_supremum. Qed.
  Next Obligation. apply eRInfimum_is_infimum. Qed.

  Instance eRBottom : Bottom := eRbot.

  Program Instance eRPointedCompleteLattice
    : PointedCompleteLattice eRCompleteLattice eRBottom.
  Next Obligation. unfold bottomAxiom; apply eRbot_bot. Qed.
End extendedRealDomain.
