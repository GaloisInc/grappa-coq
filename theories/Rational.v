Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import QArith.
Require Import Coq.micromega.Lqa.

Require Import GrappaCoq.Domain.


(** A Poset instance for Coq rationals. *)
Section rationalPoset.
  Instance rationalOrder : PosetOrder := Qle.
  Program Instance rationalPoset : Poset rationalOrder.
  Next Obligation. unfold le, rationalOrder; lra. Qed.
  Next Obligation. unfold equiv, le, rationalOrder in *; lra. Qed.
End rationalPoset.


Section rationalLemmas.
  Existing Instance rationalOrder.
  Existing Instance rationalPoset.

  Lemma Qdiv_mult_shift :
    forall x y z, ~ y == 0 -> x / y * z == x * z / y.
  Proof. intros x y z Hy; field; auto. Qed.

  Lemma Qdiv_2_not_equiv x :
    0 < x ->
    ~ x / (2 # 1) ~~ x.
  Proof.
    intros H0 [H1 H2]; unfold le, rationalOrder in *.
    assert (H4: x * (2#1) == x / (2#1) * (2#1)).
    { apply Qmult_inj_r; lra. }
    rewrite Qdiv_mult_shift in H4; try lra.
    rewrite Qdiv_mult_l in H4; lra.
  Qed.

  Lemma Qplus_Qdiv_2_not_equiv x y :
    0 < x ->
    ~ y == 0 ->
    ~ y == x ->
    ~ (x + y) / (2 # 1) ~~ x.
  Proof.
    intros H0 H1 H2 [H3 H4]; unfold le, rationalOrder in *.
    assert (H6: x * (2#1) == (x + y) / (2#1) * (2#1)).
    { apply Qmult_inj_r; lra. }
    rewrite Qdiv_mult_shift in H6; try lra.
    rewrite Qdiv_mult_l in H6; lra.
  Qed.

  Lemma Qdiv_2_le x :
    0 < x ->
    x / (2 # 1) <= x.
  Proof. intros H0; apply Qle_shift_div_r; lra. Qed.
End rationalLemmas.
