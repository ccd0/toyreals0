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

  Definition Qapprox (x : R) (target_accuracy : Q) : Q :=
    RE.value (compute x target_accuracy).

  Definition lower_bound (x : R) (t : Q) : Q :=
    RE.min (compute x t).

  Definition upper_bound (x : R) (t : Q) : Q :=
    RE.max (compute x t).

  Module ofQ. Section params.

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

    Definition ofQ : R :=
      make compute consistent meets_target.

  End params. End ofQ. Export ofQ (ofQ).

  Definition le (x y : R) : Prop :=
    forall tx ty, lower_bound x tx <= upper_bound y ty.

  Definition ge (x y : R) : Prop :=
    le y x.

  Definition eq (x y : R) : Prop :=
    le x y /\ le y x.

  Definition lt (x y : R) : Prop :=
    exists tx ty, upper_bound x tx < lower_bound y ty.

  Definition gt (x y : R) : Prop :=
    lt y x.

  Definition neq (x y : R) : Prop :=
    lt x y \/ lt y x.

  Theorem le_not_lt : forall x y, le x y <-> ~ lt y x.
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

  Theorem ofQ_lt : forall x y, x < y -> lt (ofQ x) (ofQ y).
    intros x y H.
    exists 0, 0.
    apply Qplus_lt_l, H.
  Defined.

  Theorem ofQ_neq : forall x y, ~ x == y -> neq (ofQ x) (ofQ y).
    intros x y H.
    destruct (Q_dec x y) as [[H2|H2]|H2].
    - left.
      apply ofQ_lt, H2.
    - right.
      apply ofQ_lt, H2.
    - tauto.
  Defined.

  Theorem lower_bound_spec :
    forall x t, le (ofQ (lower_bound x t)) x.
  Proof.
    intros x t t1 t2.
    apply (Qle_trans _ (lower_bound x t)).
    - unfold lower_bound, RE.min; cbn.
      setoid_rewrite Qplus_0_r.
      apply Qle_refl.
    - apply compute_consistent.
  Qed.

  Theorem upper_bound_spec :
    forall x t, le x (ofQ (upper_bound x t)).
  Proof.
    intros x t t1 t2.
    apply (Qle_trans _ (upper_bound x t)).
    - apply compute_consistent.
    - unfold upper_bound, RE.max; cbn.
      setoid_rewrite Qplus_0_r.
      apply Qle_refl.
  Qed.

  Definition Qapprox_w_den (x : R) (den : positive) : Q :=
    let den' := Z.pos den # 1 in
      Qfloor (Qapprox x (2 * den') * den' + (1 # 2)) # den.

  Module plus. Section params.

    Variables x y : R.

    Definition compute (t : Q) :=
      let x' := R.compute x (2 * t) in
        let y' := R.compute y (2 * t) in
          RE.make
            (Qred (RE.value x' + RE.value y'))
            (Qred (RE.error x' + RE.error y')).

  End params. End plus.

End R. Export R (R).
