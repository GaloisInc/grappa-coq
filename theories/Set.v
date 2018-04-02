Set Implicit Arguments.
Unset Strict Implicit.
Require Import List. Import ListNotations.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.


Section set.
  Variable T : Type.

  Definition set := T -> Prop.
  Definition union (A B : set) :=
    fun x => A x \/ B x.
  Definition intersection (A B : set) :=
    fun x => A x /\ B x.

  Definition singleton (x : T) :=
    fun y => x = y.

  Definition empty := fun _ : T => False.
  Definition full := fun _ : T => True.

  Definition subset (A B : set) := forall x, A x -> B x.
  Definition proper_subset (A B : set) := subset A B /\ exists x, B x /\ ~ A x.

  Definition disjoint (A B : set) :=
    forall x, ~ (A x /\ B x).

  Definition complement (A : set) :=
    fun x => ~ A x.

  Definition subtract (A B : set) :=
    fun x => A x /\ ~ B x.

  Definition not_empty (A : set) :=
    exists x, A x.

  Definition is_empty (A : set) :=
    ~ not_empty A.

  Definition intersects (A B : set) :=
    not_empty (intersection A B).

  Definition finite_intersection (l : list set) :=
    fold_right (fun x acc => intersection x acc) full l.

  Axiom extensionality : forall A B : set, subset A B /\ subset B A -> A = B.
End set.


Notation "'P' x" := (set (set x)) (at level 65).

Section power_set.
  Variable T : Type.
  Definition power (A : set T) :=
    fun x => subset x A.
End power_set.


Section product.
  Variable X Y : Type.

  Definition product (A : set X) (B : set Y) :=
    fun p : X*Y => let (x, y) := p in A x /\ B y.

  Definition pi1_set (A : set (X*Y)) : set X :=
    fun x => exists p, A p /\ fst p = x.

  Definition pi2_set (A : set (X*Y)) : set Y :=
    fun y => exists p, A p /\ snd p = y.

  Definition pi1_collection (A : P (X*Y)) : P X :=
    fun B => exists p, A p /\ pi1_set p = B.

  Definition pi2_collection (A : P (X*Y)) : P Y :=
    fun B => exists p, A p /\ pi2_set p = B.
End product.


Section arbitrary.
  Variable T : Type.
  Definition big_union (C : P T) :=
    fun x => exists A, C A /\ A x.

  Definition big_intersection (C : P T) :=
    fun x => forall A, C A -> A x.

  (* (* Wrt a domain D instead of the entire space of T. *) *)
  (* Definition big_intersectionD (D : set T) (C : P T) := *)
  (*   (* fun x => forall A, C A -> A x /\ D x. *) *)
  (*   intersection (big_intersection C) D. *)

  Definition all_unions (A : P T) :=
    fun B => exists C, subset C A /\ B = (big_union C).

  Definition big_subtract (A : set T) (C : P T) :=
    fun B => exists c, C c /\ B = subtract A c.

  Definition binary_collection (A B : set T) :=
    fun X => X = A \/ X = B.
End arbitrary.


Section tuple.
  Variable J : Type. (* The index set *)
  Definition J_tuple (X : J -> Type) := forall j, X j.

  (* A family of sets indexed by J. This generalizes collections of
     sets, since each set can have its own type. *)
  Definition family (X : J -> Type) := J_tuple (fun j => set (X j)).

  (* Given a family of sets A indexed by J, The cartesian product is
     the set of all J-tuples f such that f j \in A j for all j. *)
  Definition cartesian_product (X : J -> Type) (A : family X)
    : set (J_tuple X) :=
    fun f => forall j : J, A j (f j).

  Definition cartesian_product' (X : J -> Type)
    : set (J_tuple X) :=
    fun f => forall j : J, @full (X j) (f j).

  (* If all sets in the family are equal to one set X, then the
     cartesian product is just the set X^J of all J-tuples of elements
     of X. *)
  Definition cartesian_product'' (X : Type) (A : set X)
    : set (J_tuple (fun _ => X)) :=
    fun f => forall j, A (f j).

  Definition family_setwise_intersection (X : J -> Type) (A B : family X) :=
    fun j => intersection (A j) (B j).

  Definition family_union (X : Type) (A : family (fun _ => X)) :=
    fun x => exists j, A j x.

  Definition family_intersection (X : Type) (A : family (fun _ => X)) :=
    fun x => forall j, A j x.

  Definition family_collection (X : Type) (A : family (fun _ => X))
    : P X :=
    fun B => exists j, A j = B.

  Definition proj (X : J -> Type) (j : J) (A : J_tuple X)
    : X j := A j.
End tuple.


Section function.
  Variable X Y : Type.
  Variable f : X -> Y.

  Definition image (A : set X) :=
    fun y => exists x, A x /\ f x = y.

  Definition preimage (A : set Y) :=
    fun x => A (f x).

  Definition injective :=
    forall x y, f x = f y -> x = y.

  Definition surjective :=
    forall y, exists x, f x = y.

  Definition bijective :=
    injective /\ surjective.

  Definition inverse (f' : Y -> X) :=
    (forall x, f' (f x) = x) /\ (forall y, f (f' y) = y).

  Definition constant (c : Y) :=
    forall a, f a = c.
End function.


Section compose.
  Variable X Y Z : Type.

  Definition compose (g : Y -> Z) (f : X -> Y) :=
    fun x => g (f x).
End compose.

Section setLemmas.
  Variable T : Type.

  Lemma intersection_comm (A B : set T) :
    intersection A B = intersection B A.
  Proof. apply extensionality; firstorder. Qed.

  Lemma union_comm (A B : set T) :
    union A B = union B A.
  Proof. apply extensionality; firstorder. Qed.

  Lemma disjoint_comm (A B : set T) :
    disjoint A B <-> disjoint B A.
  Proof. firstorder. Qed.

  Lemma all_subset_full (A : set T) :
    subset A (@full T).
  Proof. firstorder. Qed.

  Lemma no_element_implies_empty (A : set T) :
    ~ (exists x, A x) -> A = (@empty T).
  Proof.
    intros ?; apply extensionality; split; intros ? ?; firstorder.
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

  (* Not constructive. *)
  Lemma demorgan_1 (A B C : set T) :
    subtract A (intersection B C) = union (subtract A B) (subtract A C).
  Proof.
    apply extensionality. split.
    - intros x Hx. unfold subtract, intersection in Hx.
      assert (H0: ~ B x \/ ~ C x) by (apply not_and_or; intuition).
      firstorder.
    - firstorder.
  Qed.

  Lemma demorgan_2 (A B C : set T) :
    subtract A (union B C) = intersection (subtract A B) (subtract A C).
  Proof. apply extensionality; firstorder. Qed.

  (* Not constructive. *)
  Lemma demorgan_1_big (A : set T) (C : P T) :
    subtract A (big_intersection C) = big_union (big_subtract A C).
  Proof.
    apply extensionality. split.
    - intros x [H0 H1].
      assert (exists A', C A' /\ ~ A' x).
      { apply not_all_ex_not in H1; destruct H1 as [A' H1].
        exists A'; apply imply_to_and; assumption. }
      destruct H as [A' [H3 H4]].
      exists (subtract A A'). firstorder.
    - intros x [A' [H0 H1]].
      split; destruct H0 as [B [H2 H3]]; subst; firstorder.
  Qed.      

  Lemma union_binary_collection (A B : set T) :
    union A B = big_union (binary_collection A B).
  Proof.
    apply extensionality; split.
    - firstorder.
    - intros x [A' [H0 H1]]. destruct H0; subst; firstorder.
  Qed.

  Lemma union_exists_big_union (A B : set T) :
    exists C, big_union C = union A B.
  Proof.
    exists (binary_collection A B).
    apply extensionality. split.
    - intros x [A' [H0 H1]]; destruct H0; subst; firstorder.
    - firstorder.
  Qed.

  Lemma collection_subset_intersection (C : P T) (A : set T) :
    exists B, C B /\ subset B A -> subset (big_intersection C) A.
  Proof. firstorder. Qed.

  Lemma collection_subset_union (C : P T) (A : set T) :
    (forall B, C B -> subset B A) -> subset (big_union C) A.
  Proof. firstorder. Qed.

  Lemma subtract_self_empty (A : set T) :
    subtract A A = @empty T.
  Proof. apply extensionality; firstorder. Qed.

  (* Not constructive *)
  Lemma subset_subtract_union (A B C : set T) :
    subset B A ->
    subtract A B = C ->
    A = union B C.
  Proof.
    intros Hsubset Hsubtract.
    apply extensionality. split.
    - intros x Hx.
      unfold union.
      unfold subtract in Hsubtract.
      rewrite <- Hsubtract.
      destruct (classic (B x)); firstorder.
    - intros x [? | H]; firstorder.
      rewrite <- Hsubtract in H; firstorder.
  Qed.

  (* Not constructive *)
  Lemma subtract_intersection (A B : set T) :
    subtract A (subtract A B) = intersection A B.
  Proof.
    apply extensionality. split.
    - intros ? ?; firstorder.
      destruct (classic (B x)); auto; contradiction.
    - firstorder.
  Qed.

  Lemma intersection_subset (A B : set T) :
    subset A B ->
    intersection A B = A.
  Proof. intros ?; apply extensionality; firstorder. Qed.

  Lemma subtract_intersection_disjoint (A B C : set T) :
    subset B A ->
    subtract A B = intersection C A ->
    disjoint B C.
  Proof.
    intros ? ? x [? ?].
    assert (intersection C A x) by firstorder.
    assert (~subtract A B x) by firstorder.
    congruence.
  Qed.

  (* Not constructive *)
  Lemma subtract_intersection_disjoint2 (A B C : set T) :
    subtract A B = intersection B C ->
    disjoint A C.
  Proof.
    intro Hsub.
    intros x [? ?].
    destruct (classic (B x)).
    - assert (~subtract A B x) by firstorder.
      assert (intersection B C x) by firstorder.
      congruence.
    - assert (subtract A B x) by firstorder.
      assert (~intersection B C x) by firstorder.
      congruence.
  Qed.

  Lemma finite_intersection_app (l1 l2 : list (set T)) (x : T) :
    finite_intersection l1 x ->
    finite_intersection l2 x ->
    finite_intersection (l1 ++ l2) x.
  Proof. intros ? ?; induction l1; firstorder. Qed.

  Lemma finite_intersection_app_1 (l1 l2 : list (set T))  :
    subset (finite_intersection (l1 ++ l2)) (finite_intersection l1).
  Proof. intros ? ?; induction l1; firstorder. Qed.

  Lemma finite_intersection_app_2 (l1 l2 : list (set T))  :
    subset (finite_intersection (l1 ++ l2)) (finite_intersection l2).
  Proof. intros ? ?; induction l1; firstorder. Qed.

  Lemma complement_subtract_full (A : set T) : complement A = subtract (@full T) A.
  Proof. apply extensionality; firstorder. Qed.

  Lemma complement_intersection_union (A B : set T) :
    complement (intersection A B) = union (complement A) (complement B).
  Proof.
    rewrite !complement_subtract_full; apply demorgan_1.
  Qed.

  Lemma is_empty_empty :
    is_empty (@empty T).
  Proof. firstorder. Qed.

  Lemma is_empty_iff_empty (A : set T) :
    is_empty A <-> A = (@empty T).
  Proof.
    split; intro H0.
    - apply extensionality; firstorder.
    - subst. firstorder.
  Qed.
End setLemmas.


Section productLemmas.
  Variable X Y : Type.

  Lemma intersection_product (A1 A2 : set X) (B1 B2 : set Y) :
    intersection (product A1 B1) (product A2 B2) =
    product (intersection A1 A2) (intersection B1 B2).
  Proof. apply extensionality. split; intros [? ?]; firstorder. Qed.

  Lemma full_set_product (A : set X) (B : set Y) :
    (@full (X*Y)) = product (@full X) (@full Y).
  Proof. apply extensionality. split; intros [? ?]; firstorder. Qed.

  Lemma pi1_product (A : set X) (B : set Y) :
    not_empty B ->
    pi1_set (product A B) = A.
  Proof.
    intro H0; apply extensionality; split.
    - intros x [[x' y] [? ?]]; subst; firstorder.
    - intros x Hx; destruct H0 as [y H0].
      exists (x, y); firstorder.
  Qed.

  Lemma pi2_product (A : set X) (B : set Y) :
    not_empty A ->
    pi2_set (product A B) = B.
  Proof.
    intro H0; apply extensionality; split.
    - intros x [[x' y] [? ?]]; subst; firstorder.
    - intros y Hx; destruct H0 as [x H0].
      exists (x, y); firstorder.
  Qed.

  Lemma empty_product (A : set X) (B : set Y) :
    is_empty A \/ is_empty B ->
    is_empty (product A B).
  Proof.
    intros [H0 | H0]; intro HC; apply H0;
      destruct HC as [[? ?] ?]; firstorder.
  Qed.

  Lemma pi1_set_empty (A : set (X*Y)) :
    is_empty A ->
    is_empty (pi1_set A).
  Proof. firstorder. Qed.

  Lemma pi2_set_empty (A : set (X*Y)) :
    is_empty A ->
    is_empty (pi2_set A).
  Proof. firstorder. Qed.
End productLemmas.

Section functionLemmas.
  Variable X Y : Type.

  Lemma inverse_comm (f : X -> Y) (f' : Y -> X) :
    inverse f f' <-> inverse f' f.
  Proof. firstorder. Qed.

  (* Seems impossible :( *)
  (* Lemma bijective_exists_inverse (f : X -> Y) : *)
  (*   bijective f -> *)
  (*   exists f', inverse f f'. *)
  (* Admitted. *)

  Lemma inverse_bijective (f : X -> Y) (f' : Y -> X) :
    inverse f f' ->
    bijective f.
  Proof.
    intros [H0 H1]; split.
    - intros x y H2; pose proof H0 as H3.
      specialize (H0 x); specialize (H3 y).
      rewrite <- H0, <- H3, H2; reflexivity.
    - intro y; specialize (H1 y).
      exists (f' y); assumption.
  Qed.

  Lemma bijective_preimage_image_cancel (f : X -> Y) U :
    bijective f ->
    preimage f (image f U) = U.
  Proof.
    intros [Hinj Hsur]; apply extensionality; split.
    - intros ? H0; destruct H0 as [? [? H1]].
      apply Hinj in H1; subst; assumption.
    - firstorder.
  Qed.

  Lemma bijective_image_preimage_cancel (f : X -> Y) U :
    bijective f ->
    image f (preimage f U) = U.
  Proof.
    intros [Hinj Hsur]; apply extensionality; split.
    - intros ? [? [? ?]]; subst; firstorder.
    - intros y ?; destruct (Hsur y); subst; firstorder.
  Qed.

  Lemma inverse_image_preimage (f : X -> Y) (f' : Y -> X) :
    inverse f f' ->
    forall U, image f U = preimage f' U.
  Proof.
    intros [H0 ?] ?; apply extensionality; split.
    - intros ? [? [? ?]]; subst.
      unfold preimage; rewrite H0; assumption.
    - intros x ?; exists (f' x); firstorder.
  Qed.

  Lemma preimage_constant_empty (f : X -> Y) (V : set Y) (y : Y) :
    constant f y ->
    ~ V y ->
    preimage f V = @empty X.
  Proof.
    intros H0 ?; apply extensionality; split.
    - intros x Hx; unfold preimage in Hx.
      specialize (H0 x); subst; congruence.
    - firstorder.
  Qed.

  Lemma preimage_constant_full (f : X -> Y) (V : set Y) (y : Y) :
    constant f y ->
    V y ->
    preimage f V = @full X.
  Proof.
    intros H0 ?; apply extensionality; split.
    - firstorder.
    - intros x ?; specialize (H0 x); subst; assumption.
  Qed.
End functionLemmas.


Section tupleLemmas.
  Variable J : Type.
  Variable X : J -> Type.

  (* This may not be useful. It's more of a sanity check. *)
  Lemma sdsdf (T : Type) (S : set T)
        (A : J_tuple (fun _ => set T)) :
    (forall j : J, A j = S) ->
    cartesian_product A = cartesian_product'' S.
  Proof.
    intros H0; apply extensionality; split;
      intros ? ? j; specialize (H0 j); subst; firstorder.
  Qed.

  Lemma intersection_cartesian_product (A B : family X) :
    intersection (cartesian_product A) (cartesian_product B) =
    cartesian_product (family_setwise_intersection A B).
  Proof. apply extensionality; firstorder. Qed.
End tupleLemmas.
