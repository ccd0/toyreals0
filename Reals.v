Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qminmax.
Require Import Coq.Logic.ConstructiveEpsilon.
Global Close Scope Q_scope.

Module RE.
  Local Open Scope Q_scope.

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

  Theorem average_between :
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

  Theorem consistent_error_nonneg :
    forall x t, consistent x -> 0 <= RE.error (x t).
  Proof.
    intros x t H.
    specialize (H t t).
    destruct (x t) as [x0 dx].
    unfold min, max in *.
    cbn in *.
    apply Qplus_le_r in H.
    apply Qle_minus_iff in H.
    ring_simplify in H.
    apply (Qmult_le_l 0 dx 2) in H; trivial.
    reflexivity.
  Qed.

End RE.

Module R.

  Declare Scope R_scope.
  Delimit Scope R_scope with R.
  Local Open Scope R_scope.

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
      RE.exact x.

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
    (forall tx ty, lower_bound x tx <= upper_bound y ty)%Q.

  Infix "<=" := le : R_scope.
  Notation "x >= y" := (le y x) (only parsing) : R_scope.

  Definition eqv (x y : R) : Prop :=
    x <= y /\ y <= x.

  Infix "==" := eqv (at level 70, no associativity) : R_scope.

  Definition lt (x y : R) : Prop :=
    (exists tx ty, upper_bound x tx < lower_bound y ty)%Q.

  Infix "<" := lt : R_scope.
  Notation "x > y" := (lt y x) (only parsing) : R_scope.

  Definition apart (x y : R) : Prop :=
    x < y \/ y < x.

  Infix "=/=" := apart (no associativity, at level 70) : R_scope.

  Theorem le_not_gt : forall x y, x <= y <-> ~ y < x.
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

  Theorem lt_irrefl : forall x, ~ x < x.
  Proof.
    intros x [t1 [t2 H]].
    contradict H.
    apply Qle_not_lt, compute_consistent.
  Qed.

  Theorem lt_not_gt : forall x y, x < y -> ~ y < x.
  Proof.
    intros x y [t1 [t2 H1]] [t3 [t4 H2]].
    apply (Qlt_le_trans _  _ (upper_bound y t3)) in H1.
    - apply (Qlt_trans _ _ (lower_bound x t4)) in H1; trivial.
      apply (Qlt_le_trans _  _ (upper_bound x t1)) in H1.
      + contradict H1.
        apply Qlt_irrefl.
      + apply compute_consistent.
    - apply compute_consistent.
  Qed.

  Theorem lt_le : forall x y, x < y -> x <= y.
  Proof.
    intros x y H.
    apply le_not_gt, lt_not_gt, H.
  Qed.

  Theorem eqv_le : forall x y, x == y -> x <= y.
  Proof.
    intros x y [H1 H2].
    exact H1.
  Qed.

  Theorem lt_apart : forall x y, x < y -> x =/= y.
  Proof.
    intros x y H.
    left.
    exact H.
  Defined.

  Theorem le_antisym : forall x y, x <= y -> y <= x -> x == y.
  Proof.
    intros x y H1 H2.
    split; trivial.
  Qed.

  Theorem lt_trans : forall x y z, x < y -> y < z -> x < z.
  Proof.
    intros x y z [t1 [t2 H1]] [t3 [t4 H2]].
    exists t1, t4.
    apply (Qlt_trans _ (lower_bound y t2));
      [|apply (Qle_lt_trans _ (upper_bound y t3))];
        trivial.
    apply compute_consistent.
  Defined.

  Theorem bound_diff_control_u :
    (forall x d t, 0 < d -> 2 / d < t ->
      upper_bound x t < lower_bound x t + d)%Q.
  Proof.
    intros x d t Hd Ht.
    unfold lower_bound, upper_bound, RE.min, RE.max.
    unfold Qminus.
    rewrite <- Qplus_assoc.
    apply Qplus_lt_r.
    apply (Qplus_lt_l _ _ (RE.error (compute x t))).
    apply (Qmult_lt_l _ _ (1 # 2)); [reflexivity|].
    ring_simplify.
    apply (Qmult_lt_l _ _ t); trivial.
    - apply (Qlt_trans _ (2 / d)); trivial.
      apply Qlt_shift_div_l; trivial.
      reflexivity.
    - apply (Qle_lt_trans _ 1); [apply compute_meets_target|].
      apply (Qmult_lt_l _ _ 2); [reflexivity|].
      apply (Qmult_lt_r _ _ (/ d)); [apply Qinv_lt_0_compat, Hd|].
      apply Qlt_not_eq, Qnot_eq_sym in Hd.
      field_simplify; trivial.
  Qed.

  Theorem bound_diff_control_l :
    (forall x d t, 0 < d -> 2 / d < t ->
      upper_bound x t - d < lower_bound x t)%Q.
  Proof.
    intros x d t Hd Ht.
    apply (Qplus_lt_l _ _ d).
    setoid_replace (upper_bound x t - d + d)%Q with (upper_bound x t) by ring.
    apply bound_diff_control_u; trivial.
  Qed.

  Theorem not_both_in_bounds :
    (forall x y z, x < y ->
      let t := 4 / (y - x) in
        y <= upper_bound z t -> x < lower_bound z t)%Q.
  Proof.
    intros x y z H1 t H2.
    apply Qlt_minus_iff in H1.
    setoid_replace x with (y - (y - x))%Q by ring.
    apply (Qle_lt_trans _ (upper_bound z t - (y - x))).
      - apply Qplus_le_l, H2.
      - apply bound_diff_control_l; trivial.
        apply Qmult_lt_r; [apply Qinv_lt_0_compat, H1|reflexivity].
  Qed.

  Theorem lt_or : forall x y z, x < y -> z < y \/ x < z.
  Proof.
    intros x y z [t1 [t2 H]].
    set (a := upper_bound x t1) in *.
    set (b := lower_bound y t2) in *.
    set (t := (4 / (b - a))%Q).
    destruct (Qlt_le_dec (upper_bound z t) b) as [H2|H2].
    - left.
      exists t, t2.
      trivial.
    - right.
      exists t1, t.
      apply (not_both_in_bounds a b); trivial.
  Defined.

  Theorem le_trans : forall x y z, x <= y -> y <= z -> x <= z.
  Proof.
    intros x y z H1 H2.
    apply le_not_gt in H1, H2.
    apply le_not_gt.
    intro H3.
    apply (lt_or _ _ y) in H3.
    tauto.
  Qed.

  Theorem lt_le_trans : forall x y z, x < y -> y <= z -> x < z.
  Proof.
    intros x y z H1 H2.
    apply le_not_gt in H2.
    apply (lt_or _ _ z) in H1.
    tauto.
  Defined.

  Theorem le_lt_trans : forall x y z, x <= y -> y < z -> x < z.
  Proof.
    intros x y z H1 H2.
    apply le_not_gt in H1.
    apply (lt_or _ _ x) in H2.
    tauto.
  Defined.

  Theorem eqv_refl : forall x, x == x.
  Proof.
    intros x.
    split; apply R.compute_consistent.
  Qed.

  Theorem eqv_sym : forall x y, x == y -> y == x.
  Proof.
    intros x y [H1 H2].
    split; trivial.
  Qed.

  Theorem eqv_trans : forall x y z, x == y -> y == z -> x == z.
  Proof.
    intros x y z [H1 H2] [H3 H4].
    split; apply (le_trans _ y); trivial.
  Qed.

  Add Relation R eqv
    reflexivity proved by eqv_refl
    symmetry proved by eqv_sym
    transitivity proved by eqv_trans
    as eqv_rel.

  Add Morphism le with signature (eqv ==> eqv ==> iff) as le_mor.
  Proof.
    intros x1 x2 [Hx1 Hx2] y1 y2 [Hy1 Hy2].
    split; intro H.
    - apply (le_trans _ x1); trivial.
      apply (le_trans _ y1); trivial.
    - apply (le_trans _ x2); trivial.
      apply (le_trans _ y2); trivial.
  Qed.

  Add Morphism lt with signature (eqv ==> eqv ==> iff) as lt_mor.
  Proof.
    intros x1 x2 [Hx1 Hx2] y1 y2 [Hy1 Hy2].
    split; intro H.
    - apply (le_lt_trans _ x1); trivial.
      apply (lt_le_trans _ y1); trivial.
    - apply (le_lt_trans _ x2); trivial.
      apply (lt_le_trans _ y2); trivial.
  Defined.

  Add Morphism apart with signature (eqv ==> eqv ==> iff) as apart_mor.
  Proof.
    intros x1 x2 Ex y1 y2 Ey.
    unfold apart.
    split; (intros [H|H]; [left|right]);
      revert H; apply lt_mor; trivial; apply eqv_sym; trivial.
  Defined.

  Theorem eqv_not_apart : forall x y, x == y <-> ~ x =/= y.
  Proof.
    intros x y.
    split.
    - intros [H1 H2] [H3|H3]; revert H3; apply le_not_gt; trivial.
    - intro H3.
      split; apply le_not_gt; contradict H3; [right|left]; trivial.
  Qed.

  Theorem apart_irrefl : forall x, ~ x =/= x.
  Proof.
    intros x.
    apply eqv_not_apart.
    reflexivity.
  Qed.

  Theorem apart_sym : forall x y, x =/= y -> y =/= x.
  Proof.
    intros x y [H|H]; [right|left]; trivial.
  Defined.

  Theorem eqv_overlaps :
    forall x y,
      x == y <->
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
    forall tx ty x y, x == y ->
      (RE.min (compute x tx) <= RE.common_point (compute x tx) (compute y ty) <= RE.max (compute x tx) /\
       RE.min (compute y ty) <= RE.common_point (compute x tx) (compute y ty) <= RE.max (compute y ty))%Q.
  Proof.
    intros tx ty x y H.
    apply RE.common_point_spec, eqv_overlaps, H.
  Qed.

  Definition is_lt_witness (x y : R) (tx ty : Q) : Prop :=
    (upper_bound x tx < lower_bound y ty)%Q.

  Theorem lt_same_witness :
    forall x y tx ty,
      is_lt_witness x y tx ty ->
        forall t, (8 / (lower_bound y ty - upper_bound x tx) <= t)%Q ->
          is_lt_witness x y t t.
  Proof.
    intros x y tx ty H t Ht.
    unfold is_lt_witness in *.
    set (a := upper_bound x tx) in *.
    set (b := lower_bound y ty) in *.
    apply Qlt_minus_iff in H.
    apply (Qlt_le_trans (4 / (b - a))) in Ht;
      [|apply Qmult_lt_r; [apply Qinv_lt_0_compat, H|reflexivity]].
    setoid_replace (4 / (b - a))%Q with (2 / ((b - a) / 2))%Q in Ht
      by (field; apply Qnot_eq_sym, Qlt_not_eq, H).
    apply (Qmult_lt_r _ _ (/ 2)) in H; [|reflexivity].
    rewrite Qmult_0_l in H.
    apply (Qlt_trans _ (lower_bound x t + (b - a) / 2)),
      (Qle_lt_trans _ (a + (b - a) / 2)),
      (Qle_lt_trans _ (upper_bound y t - (b - a) / 2)).
    - apply bound_diff_control_u; trivial.
    - apply Qplus_le_l, compute_consistent.
    - setoid_replace (a + (b - a) / 2)%Q with (b - (b - a) / 2)%Q by field.
      apply Qplus_le_l, compute_consistent.
    - apply bound_diff_control_l; trivial.
  Qed.

  Theorem lt_same_witness_exists :
    forall x y, x < y ->
      exists t, forall t2, (t <= t2)%Q -> is_lt_witness x y t2 t2.
  Proof.
    intros x y [tx [ty H]].
    exists (8 / (lower_bound y ty - upper_bound x tx))%Q.
    apply lt_same_witness, H.
  Defined.

  Definition keep_pos (x : Q) : Q :=
    if Qlt_le_dec 0 x then x else 1.

  Theorem keep_pos_spec : (forall x, 0 < keep_pos x)%Q.
  Proof.
    intro x.
    unfold keep_pos.
    destruct (Qlt_le_dec 0 x) as [H|H].
    - exact H.
    - reflexivity.
  Qed.

  Definition wlog2 (t err0 : Q) : nat :=
    Z.to_nat (Z.log2_up (Qceiling (t * (keep_pos err0)))).

  Definition wpow2 (n : nat) (err0 : Q) : Q :=
    inject_Z (2 ^ Z.of_nat n) / (keep_pos err0).

  Theorem wlog2_spec :
    forall t err0, (t <= wpow2 (wlog2 t err0) err0)%Q.
  Proof.
    intros t err0.
    unfold wpow2, wlog2.
    rewrite Z2Nat.id by apply Z.log2_up_nonneg.
    apply Qle_shift_div_l; [apply keep_pos_spec|].
    apply (Qle_trans _ (inject_Z (Qceiling (t * keep_pos err0))));
      [apply Qle_ceiling|].
    rewrite <- Zle_Qle.
    destruct (Z_lt_le_dec 0 (Qceiling (t * keep_pos err0))) as [H|H].
    - apply Z.log2_log2_up_spec, H.
    - rewrite Z.log2_up_nonpos; trivial.
      apply (Z.le_trans _ 0); trivial; discriminate.
  Qed.

  Definition Qlt_bool (x y : Q) :=
    (Qnum x * QDen y <? Qnum y * QDen x)%Z.

  Theorem Qlt_bool_iff : forall x y : Q, Qlt_bool x y = true <-> (x < y)%Q.
  Proof.
    intros x y.
    apply Z.ltb_lt.
  Qed.

  Definition init_discriminating_power (x y : R) : Q :=
    (Qmax (RE.error (compute x 0)) (RE.error (compute y 0)))%Q.

  Definition can_discriminate (x y : R) (n : nat) : bool :=
    let t := wpow2 n (init_discriminating_power x y) in
      Qlt_bool (upper_bound x t) (lower_bound y t) ||
      Qlt_bool (upper_bound y t) (lower_bound x t).

  Theorem can_discriminate_spec :
    forall x y n,
      can_discriminate x y n = true <->
        let t := wpow2 n (init_discriminating_power x y) in
          is_lt_witness x y t t \/
          is_lt_witness y x t t.
  Proof.
    intros x y t.
    unfold can_discriminate, is_lt_witness.
    rewrite orb_true_iff, Qlt_bool_iff, Qlt_bool_iff.
    tauto.
  Qed.

  Theorem can_discriminate_exists :
    forall x y, x =/= y ->
      exists n, can_discriminate x y n = true.
  Proof.
    intros x y [H|H];
      apply lt_same_witness_exists in H;
      destruct H as [t H];
      exists (wlog2 t (init_discriminating_power x y));
      apply can_discriminate_spec;
      [left|right];
      apply H, wlog2_spec.
  Defined.

  Definition find_discriminating_power (x y : R) (p : x =/= y) : nat :=
    constructive_ground_epsilon_nat
      (fun n => can_discriminate x y n = true)
      (fun n => bool_dec (can_discriminate x y n) true)
      (can_discriminate_exists x y p).

  Theorem find_discriminating_power_spec :
    forall x y p, can_discriminate x y (find_discriminating_power x y p) = true.
  Proof.
    intros x y p.
    unfold find_discriminating_power.
    apply constructive_ground_epsilon_spec_nat.
  Qed.

  Definition lt_bool (x y : R) (p : x =/= y) : bool :=
    let t := wpow2 (find_discriminating_power x y p) (init_discriminating_power x y) in
      Qlt_bool (upper_bound x t) (lower_bound y t).

  Theorem lt_bool_spec :
    forall x y p, if lt_bool x y p then x < y else y < x.
  Proof.
    intros x y p.
    destruct (lt_bool x y p) eqn:E;
      repeat exists (wpow2 (find_discriminating_power x y p) (init_discriminating_power x y)).
    - apply Qlt_bool_iff, E.
    - pose (find_discriminating_power_spec x y p) as H.
      unfold lt_bool in E.
      unfold can_discriminate in H.
      rewrite E, orb_false_l in H.
      apply Qlt_bool_iff, H.
  Defined.

  Theorem ofQ_lt : forall x y, (x < y)%Q -> ofQ x < ofQ y.
  Proof.
    intros x y H.
    exists 0%Q, 0%Q.
    apply Qplus_lt_l, H.
  Defined.

  Theorem ofQ_apart : forall x y, (~ x == y)%Q -> ofQ x =/= ofQ y.
  Proof.
    intros x y H.
    destruct (Q_dec x y) as [[H2|H2]|H2].
    - left.
      apply ofQ_lt, H2.
    - right.
      apply ofQ_lt, H2.
    - tauto.
  Defined.

  Theorem ofQ_le : forall x y, (x <= y)%Q -> ofQ x <= ofQ y.
  Proof.
    intros x y H t1 t2.
    unfold lower_bound, upper_bound, RE.min, RE.max.
    cbn.
    change (x + 0 <= y + 0)%Q.
    repeat rewrite Qplus_0_r.
    exact H.
  Qed.

  Add Morphism ofQ with signature (Qeq ==> eqv) as ofQ_mor.
  Proof.
    intros x y H.
    split; apply ofQ_le; rewrite H; apply Qle_refl.
  Qed.

  Theorem Qapprox_Qle_le :
    forall x y, (forall t, Qapprox x t <= Qapprox y t)%Q -> x <= y.
  Proof.
    intros x y H.
    apply le_not_gt.
    intro H2.
    apply lt_same_witness_exists in H2.
    destruct H2 as [t H2].
    specialize (H2 t (Qle_refl t)).
    contradict H2.
    unfold is_lt_witness.
    apply Qle_not_lt.
    change (
      Qapprox x t - RE.error (R.compute x t) <=
      Qapprox y t + RE.error (R.compute y t)
    )%Q.
    apply (Qle_trans _ (Qapprox x t)), (Qle_trans _ (Qapprox y t)); trivial;
      apply Qle_minus_iff;
      ring_simplify;
      apply RE.consistent_error_nonneg, compute_consistent.
  Qed.

  Theorem Qapprox_Qeq_eqv :
    forall x y, (forall t, Qapprox x t == Qapprox y t)%Q -> x == y.
  Proof.
    intros x y H.
    split;
      apply Qapprox_Qle_le;
      intro t;
      rewrite H;
      apply Qle_refl.
  Qed.

  Theorem lower_bound_spec :
    forall x t, ofQ (lower_bound x t) <= x.
  Proof.
    intros x t t1 t2.
    apply (Qle_trans _ (lower_bound x t)).
    - unfold lower_bound, RE.min; cbn.
      setoid_rewrite Qplus_0_r.
      apply Qle_refl.
    - apply compute_consistent.
  Qed.

  Theorem upper_bound_spec :
    forall x t, x <= ofQ (upper_bound x t).
  Proof.
    intros x t t1 t2.
    apply (Qle_trans _ (upper_bound x t)).
    - apply compute_consistent.
    - unfold upper_bound, RE.max; cbn.
      setoid_rewrite Qplus_0_r.
      apply Qle_refl.
  Qed.

  Theorem Qapprox_spec :
    forall x t, (t > 0)%Q ->
      ofQ (Qapprox x t - 1 / t) <= x /\ x <= ofQ (Qapprox x t + 1 / t).
  Proof.
    intros x t H.
    assert (RE.error (R.compute x t) <= 1 / t)%Q as H2.
    - apply Qle_shift_div_l; trivial.
      rewrite Qmult_comm.
      apply compute_meets_target.
    - split.
      + apply (le_trans _ (ofQ (lower_bound x t))), lower_bound_spec.
        apply ofQ_le.
        unfold Qapprox, lower_bound, RE.min.
        apply Qplus_le_r, Qopp_le_compat, H2.
      + apply (le_trans _ (ofQ (upper_bound x t))); [apply upper_bound_spec|].
        apply ofQ_le.
        unfold Qapprox, upper_bound, RE.max.
        apply Qplus_le_r, H2.
  Qed.

  Definition Qapprox_w_den (x : R) (den : positive) : Q :=
    (let den' := Z.pos den # 1 in
      Qfloor (Qapprox x (2 * den') * den' + (1 # 2)) # den)%Q.

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
      (plus1 (R.compute x (2 * t)) (R.compute y (2 * t)))%Q.

    Theorem errors_correct :
      Proper (RE.point_in ==> RE.point_in ==> RE.value_in) plus1.
    Proof.
      intros _ _ [x [x0 dx] Hx] _ _ [y [y0 dy] Hy].
      unfold RE.value_in, RE.min, RE.max in *.
      cbn - [Qred] in *.
      repeat rewrite Qred_correct.
      setoid_replace (x0 + y0 - (dx + dy))%Q with ((x0 - dx) + (y0 - dy))%Q by ring.
      setoid_replace (x0 + y0 + (dx + dy))%Q with ((x0 + dx) + (y0 + dy))%Q by ring.
      split; apply Qplus_le_compat; tauto.
    Qed.

    Theorem compatible : Proper (eqv ==> eqv ==> RE.eqv) plus2.
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
      pose (R.compute_meets_target x (2 * t))%Q as Hx.
      pose (R.compute_meets_target y (2 * t))%Q as Hy.
      apply (Qmult_le_l _ _ 2); [reflexivity|].
      ring_simplify.
      replace 2%Q with (1 + 1)%Q at 5 by trivial.
      apply Qplus_le_compat; trivial.
    Qed.

  End plus.

  Definition plus (x y : R) : R :=
    make (plus.plus2 x y) (plus.consistent x y) (plus.meets_target x y).

  Infix "+" := plus : R_scope.

  Add Morphism plus with signature (eqv ==> eqv ==> eqv) as plus_mor.
  Proof.
    apply plus.compatible.
  Qed.

  Theorem plus_comm : forall x y, x + y == y + x.
  Proof.
    intros x y.
    apply Qapprox_Qeq_eqv.
    intro t.
    unfold plus, plus.plus2, plus.plus1.
    cbn - [Qred].
    repeat rewrite Qred_correct.
    apply Qplus_comm.
  Qed.

  Theorem ofQ_plus : forall x y, ofQ (x + y) == ofQ x + ofQ y.
  Proof.
    intros x y.
    compute - [Qred Qplus Qminus Qle].
    repeat setoid_rewrite Qred_correct.
    split; intros _ _; ring_simplify; apply Qle_refl.
  Qed.

End R. Export R (R).

Delimit Scope R_scope with R.
Infix "<=" := R.le : R_scope.
Notation "x >= y" := (R.le y x) (only parsing) : R_scope.
Infix "==" := R.eqv (at level 70, no associativity) : R_scope.
Infix "<" := R.lt : R_scope.
Notation "x > y" := (R.lt y x) (only parsing) : R_scope.
Infix "=/=" := R.apart (no associativity, at level 70) : R_scope.
Infix "+" := R.plus : R_scope.
