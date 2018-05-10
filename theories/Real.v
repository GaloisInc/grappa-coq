Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import QArith.
Require Import Coq.micromega.Lqa.

Require Import GrappaCoq.Domain GrappaCoq.Pseudoreal GrappaCoq.Rational
        GrappaCoq.Set.


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
  Next Obligation. firstorder. Qed.
  Next Obligation. eapply subset_trans; eauto. Qed.

  Definition positive_rationals : set Q := fun x => 0 < x.

  Program Definition eRtop : eR := (@empty Q).
  Next Obligation. firstorder. Qed.

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
          -- apply Qdiv_2_not_equiv; auto.
          -- apply Qdiv_2_le; auto.
  Qed.

  Definition eRzero := eRbot.

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

  Program Definition eRInfimum (A : set eR) : eR :=
    ⋃ (image (@proj1_sig _ _) A).
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


Require Import ProofIrrelevance.
Lemma subset_PI {X : Type} {P : X -> Prop} (x y : X) (pf1 : P x) (pf2 : P y) :
  x = y ->
  exist _ x pf1 = exist _ y pf2.
Proof. intros ->; f_equal; apply proof_irrelevance. Qed.


Section sum.
  (* Binary sum of nonnegative reals. *)
  Program Definition eRplus (r1 r2 : eR) : eR :=
    fun x => exists a b, a ∈ val r1 /\ b ∈ val r2 /\ x == a + b.
  Next Obligation.
    destruct r1 as (r1 & r1Ax0 & r1Ax1 & r1Ax2);
      destruct r2 as (r2 & r2Ax0 & r2Ax1 & r2Ax2); simpl.
    split.
    - intros x (a & b & H0 & H1 & H2); subst.
      specialize (r1Ax0 a H0); specialize (r2Ax0 b H1); lra.
    - split.
      + unfold is_upper_set in *.
        intros x y H0 (a & b & H1 & H2 & H3).
        unfold in_set.
        assert (H4: a <= y).
        { unfold le, rationalOrder in H0;
            specialize (r2Ax0 b H2); lra. }
        set (c := y - a - b).
        assert (H5: b + c <= y).
        { unfold le, rationalOrder in H0;
            specialize (r1Ax0 a H1); unfold c; lra. }
        assert (H6: b + c ∈ r2).
        { apply r2Ax1 with b; auto. unfold le, rationalOrder in *.
          unfold c in *. lra. }
        exists a, (b + c). split; auto. split; auto.
        unfold c; lra.
      + intros x (a & b & H1 & H2 & H3); subst.
        specialize (r1Ax2 a H1); destruct r1Ax2  as (y & Hy0 & Hy1).
        specialize (r2Ax2 b H2); destruct r2Ax2  as (z & Hz0 & Hz1).
        exists (y + z); split.
        * exists y, z; firstorder.
        * unfold lt, equiv, le, rationalOrder in *. split; lra.
  Qed.

  Lemma eRplus_0_l r:
    eRplus eRzero r = r.
  Proof.
    destruct r as [r Hr]; apply subset_PI; simpl.
    apply extensionality; split.
    - intros x (a & b & H0 & H1 & H2).
      unfold in_set, positive_rationals in *.
      assert (H3: b <= x) by lra.
      destruct Hr as (_ & Hr & _); eapply Hr; eauto.
    - intros x Hx; destruct Hr as (H0 & H1 & H2).
      specialize (H2 x Hx); destruct H2 as (y & H2 & H3).
      exists (x - y), y; split.
      + destruct H3 as [H3 H4].
        unfold in_set, positive_rationals, equiv, le, rationalOrder in *.
        lra.
      + split; auto; lra.
  Qed.

  Lemma eRplus_0_r r:
    eRplus r eRzero = r.
  Proof.
    destruct r as [r Hr]; apply subset_PI; simpl.
    apply extensionality; split.
    - intros x (a & b & H0 & H1 & H2).
      unfold in_set, positive_rationals in *.
      assert (H3: a <= x) by lra.
      destruct Hr as (_ & Hr & _); eapply Hr; eauto.
    - intros x Hx; destruct Hr as (H0 & H1 & H2).
      specialize (H2 x Hx); destruct H2 as (y & H2 & H3).
      exists y, (x - y); split; auto. split; try lra.
      unfold in_set, lt, equiv, le, rationalOrder,
      positive_rationals in *; lra.
  Qed.

  Lemma eRplus_comm a b :
    eRplus a b = eRplus b a.
  Proof.
    apply subset_PI; apply extensionality; split;
      intros x (p & q & ?); exists q, p; rewrite Qplus_comm; intuition.
  Qed.

  Lemma eRplus_assoc a b c :
    eRplus a (eRplus b c) = eRplus (eRplus a b) c.
  Proof.
    apply subset_PI; apply extensionality; split.
    - intros x (y & z & H0 & (p & q & H3 & H4 & H5) & H2).
      exists (y + p), q; split.
      + exists y, p; split; auto; split; auto; lra.
      + split; auto; lra.
    - intros x (y & z & (p & q & H3 & H4 & H5) & H1 & H2).
      exists p, (q + z); split; auto; split; try lra.
      + exists q, z; split; auto; split; auto; lra.
  Qed.

  (* Sum over a finite list of nonnegative reals. *)
  Definition sum_list := fold_right eRplus eRzero.

  Lemma sum_list_app (l1 l2 : list eR) :
    sum_list (l1 ++ l2) = eRplus (sum_list l1) (sum_list l2).
  Proof.
    induction l1; simpl.
    - rewrite eRplus_0_l; auto.
    - rewrite IHl1; apply eRplus_assoc.
  Qed.

  Lemma sum_list_const_0 i :
    sum_list (prefix (fun _ => eRzero) i) = eRzero.
  Proof.
    induction i; auto.
    simpl. rewrite sum_list_app. simpl. rewrite IHi.
    rewrite !eRplus_0_l; auto.
  Qed.

  (* Sum over a countable set of nonnegative reals by taking the
     supremum of an ascending chain of prefix sums. *)
  Program Definition eR_sequence_sum (A : sequence eR) : eR :=
    eRSupremum (set_of_sequence (fun i => sum_list (prefix A i))).
End sum.


(* Section minus. *)
(*   Program Definition eRminus (r1 r2 : eR) : eR := *)
(*     fun x => exists a b, a ∈ val r1 /\ b ∈ val r2 /\ x == a - b /\ 0 < x. *)
(*   Next Obligation. *)
(*     split. firstorder. split. *)
(*     - admit. *)
(*     - admit. *)
(*   Admitted. *)
(* End minus. *)


Section interval.
  Program Definition eR_of_Q (q : Q) : eR :=
    fun x => 0 < x /\ q < x.
  Next Obligation.
    split. firstorder. split.
    - intros x y H0 [H1 H2].
      unfold le, rationalOrder in H0; unfold in_set; lra.
    - intros x [H0 H1]; destruct (Qlt_le_dec 0 q).
      + exists ((x+q) / (2#1)); split.
        * split; apply Qlt_shift_div_l; lra.
        * unfold lt, le, rationalOrder; split.
          -- apply Qplus_Qdiv_2_not_equiv; auto; intros ?; subst; lra.
          -- apply Qle_shift_div_r; lra.
      + exists (x / (2#1)); split.
        * split; apply Qlt_shift_div_l; lra.
        * unfold lt, le, rationalOrder; split.
          -- apply Qdiv_2_not_equiv; auto.
          -- apply Qdiv_2_le; auto.
  Qed.

  Lemma eR_of_Q_0 :
    eR_of_Q 0 = eRzero.
  Proof. apply subset_PI; apply extensionality; firstorder. Qed.

  (* Length of an interval (produces a real). *)
  Definition qI_length (q : qI) :=
    match q with
    | CompleteQI => eRtop
    | BoundedQI l h => eR_of_Q (h - l)
    end.
End interval.
