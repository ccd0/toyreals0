Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.

Module RE.

  Record estimate : Set := make {
    value : Q;
    error : Q;
  }.

  Definition min (x : estimate) : Q :=
    value x - error x.

  Definition max (x : estimate) : Q :=
    value x + error x.

  Definition estimator : Set :=
    Q -> estimate.

  Definition consistent (f : estimator) : Prop :=
    forall t1 t2, min (f t1) <= max (f t2).

  Definition meets_target (f : estimator) : Prop :=
    forall target_accuracy, target_accuracy * error (f target_accuracy) <= 1.

End RE.

Module R.

  Record R : Set := make {
    compute : RE.estimator;
    compute_consistent : RE.consistent compute;
    compute_meets_target : RE.meets_target compute;
  }.

End R.
Export R (R).

Definition RQapprox (x : R) (target_accuracy : Q) : Q :=
  RE.value (R.compute x target_accuracy).

Definition R_lower_bound (x : R) (t : Q) : Q :=
  RE.min (R.compute x t).

Definition R_upper_bound (x : R) (t : Q) : Q :=
  RE.max (R.compute x t).

Module Q2R.
  Section params.

    Variable x : Q.

    Definition compute (t : Q) : RE.estimate :=
      RE.make x 0.

    Theorem consistent : RE.consistent compute.
      intros t1 t2.
      apply Qplus_le_r.
      discriminate.
    Qed.

    Theorem meets_target : RE.meets_target compute.
      intros t.
      rewrite Qmult_0_r.
      discriminate.
    Qed.

    Definition Q2R : R :=
      R.make compute consistent meets_target.

  End params.
End Q2R.
Export Q2R (Q2R).

Definition Rle (x y : R) : Prop :=
  forall tx ty, R_lower_bound x tx <= R_upper_bound y ty.

Definition Rge (x y : R) : Prop :=
  Rle y x.

Definition Req (x y : R) : Prop :=
  Rle x y /\ Rle y x.

Definition Rlt (x y : R) : Prop :=
  exists tx ty, R_upper_bound x tx < R_lower_bound y ty.

Definition Rgt (x y : R) : Prop :=
  Rlt y x.

Definition Rneq (x y : R) : Prop :=
  Rlt x y \/ Rlt y x.

Theorem Rle_not_lt : forall x y, Rle x y <-> ~ Rlt y x.
  intros x y.
  split.
  - intros H1 [tx [ty H2]].
    specialize (H1 ty tx).
    contradict H2.
    apply Qle_not_lt, H1.
  - intros H tx ty.
    apply Qnot_lt_le.
    contradict H.
    exists ty, tx.
    apply H.
Qed.

Theorem Q2R_lt : forall x y, x < y -> Rlt (Q2R x) (Q2R y).
  intros x y H.
  exists 0, 0.
  apply Qplus_lt_l, H.
Defined.

Theorem Q2R_neq : forall x y, ~ x == y -> Rneq (Q2R x) (Q2R y).
  intros x y H.
  destruct (Q_dec x y) as [[H2|H2]|H2].
  - left.
    apply Q2R_lt, H2.
  - right.
    apply Q2R_lt, H2.
  - tauto.
Defined.

Theorem R_lower_bound_spec :
  forall x t, Rle (Q2R (R_lower_bound x t)) x.
Proof.
  intros x t t1 t2.
  apply (Qle_trans _ (R_lower_bound x t)).
  - unfold R_lower_bound, RE.min; cbn.
    setoid_rewrite Qplus_0_r.
    apply Qle_refl.
  - apply R.compute_consistent.
Qed.

Theorem R_upper_bound_spec :
  forall x t, Rle x (Q2R (R_upper_bound x t)).
Proof.
  intros x t t1 t2.
  apply (Qle_trans _ (R_upper_bound x t)).
  - apply R.compute_consistent.
  - unfold R_upper_bound, RE.max; cbn.
    setoid_rewrite Qplus_0_r.
    apply Qle_refl.
Qed.

Definition RQapprox_w_den (x : R) (den : positive) : Q :=
  let den' := Z.pos den # 1 in
    Qfloor (RQapprox x (2 * den') * den' + (1 # 2)) # den.

Module Rplus.
  Section params.

    Variables x y : R.

    Definition compute (t : Q) :=
      let x' := R.compute x (2 * t) in
        let y' := R.compute y (2 * t) in
          RE.make
            (Qred (RE.value x' + RE.value y'))
            (Qred (RE.error x' + RE.error y')).

  End params.
End Rplus.
