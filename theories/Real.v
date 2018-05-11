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

  Definition RplusAx (A : set Q) :=
    (forall x, x ∈ A -> 0 < x) /\ is_upper_set A /\ no_least A.
  Definition Rplus := { A : set Q | RplusAx A }.

  Definition Rle (r1 r2 : Rplus) :=
    val r2 ⊆ val r1.

  Open Scope domain_scope.
  Instance RplusOrder : PosetOrder := Rle.

  Program Instance RplusPoset : Poset RplusOrder.
  Next Obligation. firstorder. Qed.
  Next Obligation. eapply subset_trans; eauto. Qed.

  Definition positive_rationals : set Q := fun x => 0 < x.

  Program Definition Rplustop : Rplus := (@empty Q).
  Next Obligation. firstorder. Qed.

  Program Definition Rplusbot : Rplus := positive_rationals.
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

  Definition Rpluszero := Rplusbot.

  Notation "+∞" := Rplustop : real_scope.
  Open Scope real_scope.

  Lemma Rplustop_top :
    forall r, r ⊑ +∞.
  Proof. firstorder. Qed.

  Lemma Rplusbot_bot :
    forall r, Rplusbot ⊑ r.
  Proof.
    unfold le, RplusOrder, Rle, Rplusbot.
    intros r; destruct r; simpl; firstorder.
  Qed.

  (** The supremum is the intersection of the sets of rationals. We
      must also intersect with positive_rationals in case A is empty,
      and then ensure that there is no least element. *)
  Program Definition RplusSupremum (A : set Rplus) : Rplus :=
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
             exists (exist (fun A : set Q => RplusAx A) _ (conj H4 (conj H5 H6))).
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
                             (proj1_sig (P:=fun A : set Q => RplusAx A)) A).
          { intros c Hc B (z & H3 & ?); subst.
            destruct H0 as [H0 H0']; specialize (H0 (val z)).
            assert (exists x : {A : set Q | RplusAx A}, x ∈ A /\ val x = val z).
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

  Program Definition RplusInfimum (A : set Rplus) : Rplus :=
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

  Notation "'⊔' x" := (RplusSupremum x) (at level 65) : real_scope.
  Notation "'⊓' x" := (RplusInfimum x) (at level 65) : real_scope.

  Lemma RplusSupremum_is_supremum (A : set Rplus) :
    is_supremum (⊔ A) A.
  Proof.
    unfold is_supremum. split.
    - intros y Hy x Hx; apply Hx; exists y; firstorder.
    - intros s Hs x Hx. split. split.
      + eapply big_intersection_largest_subset; eauto.
        intros B (z & HB & ?); subst.
        specialize (Hs z HB); firstorder.
      + destruct s as (? & Hpos & ?); apply Hpos; auto.
      + destruct s as (? & Hpos & (? & Hax)).
        apply Hax in Hx; destruct Hx as (y & ? & ?).
        exists y; split; auto; split.
        * eapply big_intersection_largest_subset; eauto.
          intros ? (? & ? & ?); subst.
          apply Hs; assumption.
        * apply Hpos; assumption.
  Qed.

  Lemma RplusInfimum_is_infimum (A : set Rplus) :
    is_infimum (⊓ A) A.
  Proof.
    split.
    - intros y ? ? ?; exists (val y); split; auto; exists y; split; auto.
    - intros y Hy x (? & (z & ? & ?) & ?); subst.
      assert (y ⊑ z) by (apply Hy; auto).
      destruct y; destruct z; simpl in *; firstorder.
  Qed.
End extendedReal.

Notation "+∞" := Rplustop : real_scope.
Notation "'⊔' x" := (RplusSupremum x) (at level 65) : real_scope.
Notation "'⊓' x" := (RplusInfimum x) (at level 65) : real_scope.
Open Scope real_scope.


(** The non-negative reals extended with +∞ form a complete lattice. *)
Section extendedRealDomain.
  Program Instance RplusCompleteLattice :
    @CompleteLattice _ _ RplusPoset RplusSupremum RplusInfimum.
  Next Obligation. apply RplusSupremum_is_supremum. Qed.
  Next Obligation. apply RplusInfimum_is_infimum. Qed.

  Instance RplusBottom : Bottom := Rplusbot.

  Program Instance RplusPointedCompleteLattice
    : PointedCompleteLattice RplusCompleteLattice RplusBottom.
  Next Obligation. unfold bottomAxiom; apply Rplusbot_bot. Qed.
End extendedRealDomain.


Require Import ProofIrrelevance.
Lemma subset_PI {X : Type} {P : X -> Prop} (x y : X) (pf1 : P x) (pf2 : P y) :
  x = y -> exist _ x pf1 = exist _ y pf2.
Proof. intros ->; f_equal; apply proof_irrelevance. Qed.


Section sum.
  (* Binary sum of nonnegative reals. *)
  Program Definition Rplusplus (r1 r2 : Rplus) : Rplus :=
    fun x => exists a b, a ∈ val r1 /\ b ∈ val r2 /\ x == a + b.
  Next Obligation.
    destruct r1 as (r1 & r1Ax0 & r1Ax1 & r1Ax2);
      destruct r2 as (r2 & r2Ax0 & r2Ax1 & r2Ax2); simpl.
    split.
    - intros ? (? & ? & Ha & Hb & ?); subst.
      specialize (r1Ax0 _ Ha); specialize (r2Ax0 _ Hb); lra.
    - split.
      + intros x y H0 (a & b & Ha & Hb & ?).
        assert (a <= y).
        { unfold le, rationalOrder in H0;
            specialize (r2Ax0 b Hb); lra. }
        set (c := y - a - b).
        assert (b + c <= y).
        { unfold le, rationalOrder in H0;
            specialize (r1Ax0 a Ha); unfold c; lra. }
        assert (b + c ∈ r2).
        { apply r2Ax1 with b; auto.
          unfold le, rationalOrder, c in *; lra. }
        exists a, (b + c); split; auto; split; auto; unfold c; lra.
      + intros x (? & ? & Hx & Hy & ?); subst.
        specialize (r1Ax2 _ Hx); destruct r1Ax2 as (y & ? & ?).
        specialize (r2Ax2 _ Hy); destruct r2Ax2 as (z & ? & ?).
        exists (y + z); split.
        * exists y, z; firstorder.
        * unfold lt, equiv, le, rationalOrder in *; split; lra.
  Qed.

  Lemma Rplusplus_0_l r :
    Rplusplus Rpluszero r = r.
  Proof.
    destruct r as [r Hr]; apply subset_PI; simpl.
    apply extensionality; split.
    - intros x (? & b & ? & ? & ?).
      unfold in_set, positive_rationals in *.
      assert (b <= x) by lra.
      destruct Hr as (_ & Hr & _); eapply Hr; eauto.
    - intros x Hx; destruct Hr as (? & ? & Hr).
      specialize (Hr x Hx); destruct Hr as (y & ? & Hr).
      exists (x - y), y; split.
      + destruct Hr as [? ?].
        unfold in_set, positive_rationals,
        equiv, le, rationalOrder in *; lra.
      + split; auto; lra.
  Qed.

  Lemma Rplusplus_0_r r :
    Rplusplus r Rpluszero = r.
  Proof.
    destruct r as [r Hr]; apply subset_PI; simpl.
    apply extensionality; split.
    - intros x (a & ? & ? & ? & ?).
      unfold in_set, positive_rationals in *.
      assert (a <= x) by lra.
      destruct Hr as (_ & Hr & _); eapply Hr; eauto.
    - intros x Hx; destruct Hr as (? & ? & Hr).
      specialize (Hr x Hx); destruct Hr as (y & ? & ?).
      exists y, (x - y); split; auto. split; try lra.
      unfold in_set, lt, equiv, le, rationalOrder,
      positive_rationals in *; lra.
  Qed.

  Lemma Rplusplus_comm a b :
    Rplusplus a b = Rplusplus b a.
  Proof.
    apply subset_PI; apply extensionality; split;
      intros x (p & q & ?); exists q, p; rewrite Qplus_comm; intuition.
  Qed.

  Lemma Rplusplus_assoc a b c :
    Rplusplus a (Rplusplus b c) = Rplusplus (Rplusplus a b) c.
  Proof.
    apply subset_PI; apply extensionality; split.
    - intros ? (y & ? & ? & (p & q & ? & ? & ?) & ?).
      exists (y + p), q; split.
      + exists y, p; split; auto; split; auto; lra.
      + split; auto; lra.
    - intros ? (? & z & (p & q & ? & ? & ?) & ? & ?).
      exists p, (q + z); split; auto; split; try lra.
      + exists q, z; split; auto; split; auto; lra.
  Qed.

  (* Sum over a finite list of nonnegative reals. *)
  Definition sum_list := fold_right Rplusplus Rpluszero.

  Lemma sum_list_app (l1 l2 : list Rplus) :
    sum_list (l1 ++ l2) = Rplusplus (sum_list l1) (sum_list l2).
  Proof.
    induction l1 as [| ? ? IH]; simpl.
    - rewrite Rplusplus_0_l; auto.
    - rewrite IH; apply Rplusplus_assoc.
  Qed.

  Lemma sum_list_const_0 i :
    sum_list (prefix (fun _ => Rpluszero) i) = Rpluszero.
  Proof.
    induction i as [| ? IH]; auto; simpl.
    rewrite sum_list_app, IH; simpl; rewrite !Rplusplus_0_l; auto.
  Qed.

  (* Sum over a countable set of nonnegative reals by taking the
     supremum of an ascending chain of prefix sums. *)
  Program Definition Rplus_sequence_sum (A : sequence Rplus) : Rplus :=
    RplusSupremum (set_of_sequence (fun i => sum_list (prefix A i))).
End sum.


(* Section minus. *)
(*   Program Definition Rplusminus (r1 r2 : Rplus) : Rplus := *)
(*     fun x => exists a b, a ∈ val r1 /\ b ∈ val r2 /\ x == a - b /\ 0 < x. *)
(*   Next Obligation. *)
(*     split. firstorder. split. *)
(*     - admit. *)
(*     - admit. *)
(*   Admitted. *)
(* End minus. *)


Section interval.
  Program Definition Rplus_of_Q (q : Q) : Rplus :=
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

  Lemma Rplus_of_Q_0 :
    Rplus_of_Q 0 = Rpluszero.
  Proof. apply subset_PI; apply extensionality; firstorder. Qed.

  (* Length of an interval (produces a real). *)
  Definition qI_length (q : qI) :=
    match q with
    | CompleteQI => +∞
    | BoundedQI l h => Rplus_of_Q (h - l)
    end.
End interval.
