Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.Lists.Streams.
Global Close Scope Q_scope.
Local Close Scope nat_scope.

Record Qinterval : Set := make_Qinterval {
  min : Q;
  max : Q;
}.

Declare Scope QI_scope.
Delimit Scope QI_scope with QI.
Bind Scope QI_scope with Qinterval.
Local Open Scope QI_scope.
Notation "[ a , b ]Q" := (make_Qinterval a b) (at level 0) : QI_scope.
Notation "s .[ k ]" := (Str_nth k s) (at level 2, left associativity, format "s .[ k ]") : QI_scope.

Definition width (xs : Qinterval) : Q :=
  max xs - min xs.

Definition in_Qinterval (q : Q) (rs : Qinterval) :=
  (min rs <= q <= max rs)%Q.

Infix "∈" := in_Qinterval (at level 70, no associativity) : QI_scope.

Record R : Set := make {
  bounds : Stream Qinterval;
  bounds_min_le_max : forall k, (min bounds.[k] <= max bounds.[k])%Q;
  bounds_stricter_min : forall k1 k2, (k2 >= k1)%nat -> (min bounds.[k2] >= min bounds.[k1])%Q;
  bounds_stricter_max : forall k1 k2, (k2 >= k1)%nat -> (max bounds.[k2] <= max bounds.[k1])%Q;
  bounds_convergent : (forall eps, eps > 0 -> exists k, width bounds.[k] < eps)%Q;
}.

Declare Scope R_scope.
Delimit Scope R_scope with R.
Bind Scope R_scope with R.
Local Open Scope R_scope.

Coercion bounds : R >-> Stream.

Lemma bounds_consistent : forall (x : R) k1 k2, (min x.[k1] <= max x.[k2])%Q.
Proof.
  intros x k1 k2.
  set (k3 := Nat.max k1 k2).
  apply (Qle_trans _ (min x.[k3])), (Qle_trans _ (max x.[k3])).
  - apply bounds_stricter_min, Nat.le_max_l.
  - apply bounds_min_le_max.
  - apply bounds_stricter_max, Nat.le_max_r.
Qed.

Lemma bounds_min_elem : forall (x : R) k, min x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_min_le_max.
Qed.

Lemma bounds_max_elem : forall (x : R) k, max x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_min_le_max.
Qed.

Lemma bounds_nested_elem : forall (x : R) k1 k2 r, (k2 >= k1)%nat -> r ∈ x.[k2] -> r ∈ x.[k1].
Proof.
  intros x k1 k2 r Hk [H1 H2].
  pose (bounds_stricter_min x k1 k2 Hk).
  pose (bounds_stricter_max x k1 k2 Hk).
  split; q_order.
Qed.

Lemma bounds_width_decr : forall (x : R) k1 k2, (k2 >= k1)%nat -> (width x.[k2] <= width x.[k1])%Q.
Proof.
  intros x k1 k2 Hk.
  apply Qplus_le_compat.
  - apply bounds_stricter_max, Hk.
  - apply Qopp_le_compat, bounds_stricter_min, Hk.
Qed.

Definition lt (x y : R) :=
  exists k, (max x.[k] < min y.[k])%Q.

Infix "<" := lt : R_scope.
Notation "x > y" := (lt y x) (only parsing) : R_scope.

Theorem lt_trans : forall x y z, x < y -> y < z -> x < z.
Proof.
  intros x y z [k1 H1] [k2 H2].
  set (k3 := Nat.max k1 k2).
  exists k3.
  apply (Qle_lt_trans _ (max x.[k1])), (Qlt_trans _ (min y.[k1])), (Qle_lt_trans _ (max y.[k2])), (Qlt_le_trans _ (min z.[k2]));
    trivial.
  - apply bounds_stricter_max, Nat.le_max_l.
  - apply bounds_consistent.
  - apply bounds_stricter_min, Nat.le_max_r.
Defined.

Theorem lt_irrefl : forall x, ~ x < x.
Proof.
  intros x [k H].
  apply Qlt_not_le in H.
  apply H, bounds_min_le_max.
Qed.

Theorem lt_not_gt : forall x y, x < y -> ~ x > y.
Proof.
  intros x y H1 H2.
  apply (lt_irrefl x), (lt_trans _ y); trivial.
Qed.

Lemma lt_gap :
  forall x y, x < y -> exists k eps, (eps > 0)%Q /\
    forall n r s, (n >= k)%nat -> r ∈ x.[n] -> s ∈ y.[n] -> (s - r >= eps)%Q.
Proof.
  intros x y [k Hk].
  exists k, (min y.[k] - max x.[k])%Q.
  split; [apply (Qlt_minus_iff (max x.[k])), Hk|].
  intros n r s Hn Hr Hs.
  apply (bounds_nested_elem _ k) in Hr, Hs; trivial.
  destruct Hr as [_ Hr], Hs as [Hs _].
  apply Qplus_le_compat; trivial.
  apply Qopp_le_compat; trivial.
Defined.

Theorem lt_or : forall x y z, x < y -> z < y \/ z > x.
Proof.
  intros x y z H.
  apply lt_gap in H.
  destruct H as [k1 [eps [Heps H]]].
  destruct (bounds_convergent z eps Heps) as [k2 Hk2].
  set (k3 := Nat.max k1 k2).
  apply (Qle_lt_trans (width z.[k3])) in Hk2; [|apply bounds_width_decr, Nat.le_max_r].
  destruct (Qlt_le_dec (max x.[k3]) (min z.[k3])) as [HC|HC].
  - right. exists k3. trivial.
  - left. exists k3.
    apply (Qplus_lt_l _ _ (- min z.[k3])).
    apply (Qlt_le_trans _ eps), (Qle_trans _ (min y.[k3] - max x.[k3])); trivial.
    + apply (H k3).
      * apply Nat.le_max_l.
      * apply bounds_max_elem.
      * apply bounds_min_elem.
    + apply Qplus_le_r, Qopp_le_compat, HC.
Defined.
