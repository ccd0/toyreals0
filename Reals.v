Require Import Coq.QArith.QArith.
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
Notation "[ a , b ]Q" := (make_Qinterval a b) (at level 0) : QI_scope.
Notation "s .[ k ]" := (Str_nth k s) (at level 2, left associativity, format "s .[ k ]") : QI_scope.

Definition width (xs : Qinterval) : Q :=
  max xs - min xs.

Record R : Set := make {
  bounds : Stream Qinterval;
  bounds_min_le_max : forall k, (min bounds.[k] <= max bounds.[k])%Q;
  bounds_stricter_min : forall k1 k2, (k2 >= k1)%nat -> (min bounds.[k2] >= min bounds.[k1])%Q;
  bounds_stricter_max : forall k1 k2, (k2 >= k1)%nat -> (max bounds.[k2] <= max bounds.[k1])%Q;
  bounds_convergent : (forall eps, eps > 0 -> exists k, width bounds.[k] < eps)%Q;
}.
