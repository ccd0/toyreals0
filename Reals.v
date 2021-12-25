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

Theorem bounds_min_elem : forall (x : R) k, min x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_min_le_max.
Qed.

Theorem bounds_max_elem : forall (x : R) k, max x.[k] ∈ x.[k].
Proof.
  intros x k.
  split; try q_order.
  apply bounds_min_le_max.
Qed.

Theorem bounds_nonempty : forall (x : R) k, exists r, r ∈ x.[k].
Proof.
  intros x k.
  exists (min x.[k]).
  apply bounds_min_elem.
Qed.

Theorem bounds_nested_elem: forall (x : R) k1 k2 r, (k2 >= k1)%nat -> r ∈ x.[k2] -> r ∈ x.[k1].
Proof.
  intros x k1 k2 r Hk [H1 H2].
  pose (bounds_stricter_min x k1 k2 Hk).
  pose (bounds_stricter_max x k1 k2 Hk).
  split; q_order.
Qed.

Definition lt (x y : R) :=
  exists k, (max x.[k] < min y.[k])%Q.

Infix "<" := lt : R_scope.
Notation "x > y" := (lt y x) (only parsing) : R_scope.
