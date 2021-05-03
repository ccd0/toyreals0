Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qminmax.

Module RE.

  Record estimate : Set := make {
    value : Q;
    error : Q;
  }.

  Definition min (x : estimate) : Q :=
    match x with
    | make val err => val - err
    end.

  Definition max (x : estimate) : Q :=
    match x with
    | make val err => val + err
    end.

  Definition estimator : Set :=
    Q -> estimate.

  Definition consistent (x : estimator) : Prop :=
    forall t1 t2, min (x t1) <= max (x t2).

  Definition meets_target (x : estimator) : Prop :=
    forall target_accuracy, target_accuracy * error (x target_accuracy) <= 1.

  Definition le (x y : estimator) : Prop :=
    forall t1 t2, min (x t1) <= max (y t2).

  Definition eqv (x y : estimator) : Prop :=
    le x y /\ le y x.

  Definition exact (x : Q) : estimate :=
    make x 0.

  Definition overlaps (x1 x2 : estimate) : Prop :=
    Qmax (min x1) (min x2) <= Qmin (max x1) (max x2).

  Inductive point_in : estimate -> estimate -> Prop :=
    | point_in_intro (x : Q) (xs : estimate) :
        min xs <= x <= max xs -> point_in (exact x) xs.

  Definition value_in (xs ys : estimate) : Prop :=
    min ys <= value xs <= max ys.

  Lemma average_between :
    forall x y, x <= y -> x <= (x + y) / 2 <= y.
  Proof.
    intros x y H.
    apply Qle_minus_iff in H.
    split;
      [apply Qle_shift_div_l|apply Qle_shift_div_r];
      try reflexivity;
      apply Qle_minus_iff;
      apply (Qle_trans _ _ _ H);
      apply Qle_minus_iff;
      ring_simplify;
      discriminate.
  Qed.

  Definition common_point (x y : estimate) : Q :=
    (Qmax (min x) (min y) + Qmin (max x) (max y)) / 2.

  Theorem common_point_spec :
    forall x y, overlaps x y ->
      min x <= common_point x y <= max x /\ min y <= common_point x y <= max y.
  Proof.
    intros x y H.
    assert (Qmax (min x) (min y) <= common_point x y <= Qmin (max x) (max y)) as G;
      [|rewrite Q.min_glb_iff, Q.max_lub_iff in G; tauto].
    apply average_between, H.
  Qed.

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

  Module ofQ.

    Definition ofQ1 (x t : Q) : RE.estimate :=
      RE.make x 0.

    Theorem consistent : forall x, RE.consistent (ofQ1 x).
    Proof.
      intros x t1 t2.
      apply Qplus_le_r.
      discriminate.
    Qed.

    Theorem meets_target : forall x, RE.meets_target (ofQ1 x).
    Proof.
      intros x t.
      rewrite Qmult_0_r.
      discriminate.
    Qed.

  End ofQ.

  Definition ofQ (x : Q) : R :=
    make (ofQ.ofQ1 x) (ofQ.consistent x) (ofQ.meets_target x).

  Definition le (x y : R) : Prop :=
    forall tx ty, lower_bound x tx <= upper_bound y ty.

  Definition ge (x y : R) : Prop :=
    le y x.

  Definition eqv (x y : R) : Prop :=
    le x y /\ le y x.

  Definition lt (x y : R) : Prop :=
    exists tx ty, upper_bound x tx < lower_bound y ty.

  Definition gt (x y : R) : Prop :=
    lt y x.

  Definition neq (x y : R) : Prop :=
    lt x y \/ lt y x.

  Theorem le_not_lt : forall x y, le x y <-> ~ lt y x.
  Proof.
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

  Theorem eqv_refl :
    forall x, eqv x x.
  Proof.
    intros x.
    split; apply R.compute_consistent.
  Qed.

  Theorem eqv_overlaps :
    forall x y,
      eqv x y <->
      forall tx ty, RE.overlaps (compute x tx) (compute y ty).
  Proof.
    intros x y.
    unfold eqv, le, RE.overlaps.
    unfold lower_bound, upper_bound.
    setoid_rewrite Q.max_lub_iff.
    setoid_rewrite Q.min_glb_iff.
    split; intro H.
    - intros tx ty.
      repeat split; try apply H; apply compute_consistent.
    - split; intros; apply H.
  Qed.

  Theorem eqv_common_point :
    forall tx ty x y, eqv x y ->
      RE.min (compute x tx) <= RE.common_point (compute x tx) (compute y ty) <= RE.max (compute x tx) /\
      RE.min (compute y ty) <= RE.common_point (compute x tx) (compute y ty) <= RE.max (compute y ty).
  Proof.
    intros tx ty x y H.
    apply RE.common_point_spec, eqv_overlaps, H.
  Qed.

  Theorem ofQ_lt : forall x y, x < y -> lt (ofQ x) (ofQ y).
  Proof.
    intros x y H.
    exists 0, 0.
    apply Qplus_lt_l, H.
  Defined.

  Theorem ofQ_neq : forall x y, ~ x == y -> neq (ofQ x) (ofQ y).
  Proof.
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

  Theorem errors_correct_compatible1 :
    forall f tx,
      Proper (RE.point_in ==> RE.value_in) f ->
        Proper (eqv ==> RE.eqv)
          (fun x t => f (compute x (tx x t))).
  Proof.
    intros f tx H x1 x2 Hx.
    split; [intros t1 t2|intros t2 t1];
      set (tx1 := tx x1 t1);
      set (tx2 := tx x2 t2);
      apply (eqv_common_point tx1 tx2) in Hx;
      set (x := RE.common_point (compute x1 tx1) (compute x2 tx2)) in *;
      set (v := f (RE.exact x));
      apply (Qle_trans _ (RE.value v));
        apply H;
          apply RE.point_in_intro;
          tauto.
  Qed.

  Theorem errors_correct_compatible2 :
    forall f tx ty,
      Proper (RE.point_in ==> RE.point_in ==> RE.value_in) f ->
        Proper (eqv ==> eqv ==> RE.eqv)
          (fun x y t => f (compute x (tx x y t)) (compute y (ty x y t))).
  Proof.
    intros f tx ty H x1 x2 Hx y1 y2 Hy.
    split; [intros t1 t2|intros t2 t1];
      set (tx1 := tx x1 y1 t1);
      set (tx2 := tx x2 y2 t2);
      set (ty1 := ty x1 y1 t1);
      set (ty2 := ty x2 y2 t2);
      apply (eqv_common_point tx1 tx2) in Hx;
      apply (eqv_common_point ty1 ty2) in Hy;
      set (x := RE.common_point (compute x1 tx1) (compute x2 tx2)) in *;
      set (y := RE.common_point (compute y1 ty1) (compute y2 ty2)) in *;
      set (v := f (RE.exact x) (RE.exact y));
      apply (Qle_trans _ (RE.value v));
        apply H;
          apply RE.point_in_intro;
          tauto.
  Qed.

  Module plus.

    Definition plus1 (x y : RE.estimate) : RE.estimate :=
      RE.make
        (Qred (RE.value x + RE.value y))
        (Qred (RE.error x + RE.error y)).

    Definition plus2 (x y : R) (t : Q) : RE.estimate :=
      plus1 (R.compute x (2 * t)) (R.compute y (2 * t)).

    Lemma errors_correct :
      Proper (RE.point_in ==> RE.point_in ==> RE.value_in) plus1.
    Proof.
      intros _ _ [x [x0 dx] Hx] _ _ [y [y0 dy] Hy].
      unfold RE.value_in.
      cbn - [Qred] in *.
      repeat rewrite Qred_correct.
      setoid_replace (x0 + y0 - (dx + dy)) with ((x0 - dx) + (y0 - dy)) by ring.
      setoid_replace (x0 + y0 + (dx + dy)) with ((x0 + dx) + (y0 + dy)) by ring.
      split; apply Qplus_le_compat; tauto.
    Qed.

    Lemma compatible : Proper (eqv ==> eqv ==> RE.eqv) plus2.
    Proof.
      apply errors_correct_compatible2, errors_correct.
    Qed.

    Theorem consistent : forall x y, RE.consistent (plus2 x y).
    Proof.
      intros x y t1 t2.
      apply compatible; apply eqv_refl.
    Qed.

    Theorem meets_target : forall x y, RE.meets_target (plus2 x y).
    Proof.
      intros x y t.
      cbn - [Qred].
      rewrite Qred_correct.
      pose (R.compute_meets_target x (2 * t)) as Hx.
      pose (R.compute_meets_target y (2 * t)) as Hy.
      apply (Qmult_le_l _ _ 2); [reflexivity|].
      ring_simplify.
      replace 2 with (1 + 1) at 5 by trivial.
      apply Qplus_le_compat; trivial.
    Qed.

  End plus.

  Definition plus (x y : R) : R :=
    make (plus.plus2 x y) (plus.consistent x y) (plus.meets_target x y).

End R. Export R (R).
