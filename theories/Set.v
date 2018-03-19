Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import Coq.Logic.Classical_Prop.


Section set.
  Variable T : Type.

  Definition set := T -> Prop.
  Definition union (A B : set) :=
    fun x => A x \/ B x.
  Definition intersection (A B : set) :=
    fun x => A x /\ B x.

  Definition empty_set := fun _ : T => False.
  Definition full_set := fun _ : T => True.

  Definition subset (A B : set) := forall x, A x -> B x.
  Definition proper_subset (A B : set) := subset A B /\ exists x, B x /\ ~ A x.

  Definition disjoint (A B : set) :=
    forall x, ~ (A x /\ B x).

  Definition finite_union (l : list set) :=
    fun x => List.Exists (fun s => s x) l.

  Definition finite_intersection (l : list set) :=
    fun x => List.Forall (fun s => s x) l.

  Axiom extensionality : forall A B : set, subset A B /\ subset B A -> A = B.
End set.

Notation "'P' x" := (set (set x)) (at level 65).

Section power_set.
  Variable T : Type.
  Definition power (A : set T) :=
    fun x => subset x A.
End power_set.


Section arbitrary.
  Variable T : Type.
  Definition big_union (C : set (set T)) :=
    fun x => exists A, C A /\ A x.

  Definition big_intersection (C : set (set T)) :=
    fun x => forall A, C A -> A x.

  Definition all_unions (A : P T) :=
    fun B => exists C, subset C A /\ B = (big_union C).
End arbitrary.

Section setLemmas.
  Variable T : Type.

  Lemma all_subset_full (A : set T) :
    subset A (@full_set T).
  Proof. firstorder. Qed.

  Lemma no_element_implies_empty (A : set T) :
    ~ (exists x, A x) -> A = (@empty_set T).
  Proof.
    intro H; apply extensionality; split; intros x H0; firstorder.
  Qed.

  Lemma subset_big_union (A : set T) (C : P T) :
    C A -> subset A (big_union C).
  Proof. firstorder. Qed.

  Lemma subset_intersection (A B C D : set T) :
    subset A C ->
    subset B D ->
    subset (intersection A B) (intersection C D).
  Proof. firstorder. Qed.

  Lemma subset_trans (A B C : set T) :
    subset A B -> subset B C -> subset A C.
  Proof. firstorder. Qed.

  Lemma subset_big_union2 (C C' : P T) :
    subset C C' ->
    subset (big_union C) (big_union C').
  Proof. firstorder. Qed.

  Lemma big_union_all_unions (C : P T) :
    big_union (all_unions C) = big_union C.
  Proof.
    apply extensionality. split; intros x Hx.
    - destruct Hx as [A [H0 H1]].
      destruct H0 as [C' [H0 H2]].
      rewrite H2 in H1; firstorder.
    - destruct Hx as [A [H0 H1]].
      unfold big_union.
      exists A; split; auto.
      unfold all_unions. exists (fun B => B = A). split.
      + intros y Hy; subst; auto.
      + apply extensionality. split; intros y Hy.
        * firstorder.
        * destruct Hy as [B [H2 H3]]; subst; assumption.
  Qed.
End setLemmas.
