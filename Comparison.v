Require Import ToyReals.Reals.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Logic.ConstructiveEpsilon.
Global Close Scope Q_scope.

Local Open Scope R_scope.

Definition is_Rlt_witness (x y : R) (tx ty : Q) : Prop :=
  (R.upper_bound x tx < R.lower_bound y ty)%Q.

Definition Rlt_witness_make_same (x y : R) (tx ty : Q) : Q :=
  (8 / (R.lower_bound y ty - R.upper_bound x tx))%Q.

Lemma Rlt_witness_make_same_spec :
  forall x y tx ty,
    is_Rlt_witness x y tx ty ->
      forall t, (Rlt_witness_make_same x y tx ty <= t)%Q ->
        is_Rlt_witness x y t t.
Proof.
  intros x y tx ty H t Ht.
  unfold is_Rlt_witness.
  setoid_replace (R.upper_bound x t)
    with (R.lower_bound x t + 2 * RE.error (R.compute x t))%Q
    by (unfold R.upper_bound, R.lower_bound, RE.min, RE.max; ring).
  setoid_replace (R.lower_bound y t)
    with (R.upper_bound y t - 2 * RE.error (R.compute y t))%Q
    by (unfold R.upper_bound, R.lower_bound, RE.min, RE.max; ring).
  apply (Qle_lt_trans _ (R.upper_bound x tx + 2 * RE.error (R.compute x t)));
    [apply Qplus_le_l, R.compute_consistent|].
  apply (Qlt_le_trans _ (R.lower_bound y ty - 2 * RE.error (R.compute y t)));
    [|apply Qplus_le_l, R.compute_consistent].
  apply (Qplus_lt_l _ _ (2 * RE.error (R.compute y t) - R.upper_bound x tx)).
  apply (Qmult_lt_l _ _ (1 # 2)); [reflexivity|].
  ring_simplify.
  setoid_replace ((-1 # 2) * R.upper_bound x tx + (1 # 2) * R.lower_bound y ty)%Q
    with ((R.lower_bound y ty - R.upper_bound x tx) / 2)%Q by field.
  unfold Rlt_witness_make_same in Ht.
  cbn in Ht.
  set (z := (R.lower_bound y ty - R.upper_bound x tx)%Q) in *.
  assert (z > 0)%Q as Hz.
  - subst z.
    setoid_rewrite <- (Qplus_opp_r (R.upper_bound x tx)).
    apply Qplus_lt_l.
    apply H.
  - apply (Qmult_lt_l _ _ t).
    + apply (Qlt_le_trans _ (8 / z)); trivial.
      apply Qlt_shift_div_l; trivial.
      reflexivity.
    + ring_simplify.
      apply (Qle_lt_trans _ (1 + t * RE.error (R.compute y t)));
        [apply Qplus_le_l, R.compute_meets_target|].
      apply (Qle_lt_trans _ (1 + 1));
        [apply Qplus_le_r, R.compute_meets_target|].
      apply (Qmult_le_r _ _ (z / 2)) in Ht;
        [|rewrite <- (Qmult_0_l (/ 2)); apply Qmult_lt_r; trivial; reflexivity].
      apply (Qlt_le_trans _ (8 / z * (z / 2))), Ht.
      field_simplify; try reflexivity.
      intro Hz2.
      rewrite Hz2 in Hz.
      discriminate.
Qed.

Lemma Rlt_exists_same_witness :
  forall x y, x < y ->
    exists t, forall t2, (t <= t2)%Q -> is_Rlt_witness x y t2 t2.
Proof.
  intros x y [tx [ty H]].
  exists (Rlt_witness_make_same x y tx ty).
  apply Rlt_witness_make_same_spec, H.
Defined.

Definition wlog2 (t : Q) : nat :=
  Nat.log2_up (Z.to_nat (Z.max 2 (Qceiling t))).

Definition wpow2 (n : nat) : Q :=
  inject_Z (Z.of_nat (2 ^ n)).

Lemma wlog2_spec :
  forall t, (t <= wpow2 (wlog2 t))%Q.
Proof.
  intro t.
  unfold wpow2, wlog2.
  apply (Qle_trans _ (inject_Z (Qceiling t))); [apply Qle_ceiling|].
  rewrite <- Zle_Qle.
  apply (Z.le_trans _ (Z.max 2 (Qceiling t))); [apply Z.le_max_r|].
  assert (0 <= Z.max 2 (Qceiling t))%Z as H
    by (apply (Z.le_trans _ (Z.max 0 (Qceiling t)));
      [apply Z.le_max_l|apply Z.max_le_compat_r; discriminate]).
  rewrite <- (Z2Nat.id (Z.max 2 (Qceiling t))) at 1 by apply H.
  apply inj_le.
  apply Nat.log2_up_spec.
  apply (Nat.lt_le_trans _ 2); auto.
  change (Z.to_nat 2 <= Z.to_nat (Z.max 2 (Qceiling t)))%nat.
  apply Z2Nat.inj_le; trivial; try discriminate.
  apply Z.le_max_l.
Qed.

Definition Qlt_bool (x y : Q) :=
  (Qnum x * QDen y <? Qnum y * QDen x)%Z.

Lemma Qlt_bool_iff : forall x y : Q, Qlt_bool x y = true <-> (x < y)%Q.
Proof.
  intros x y.
  apply Z.ltb_lt.
Qed.

Definition Rcan_discriminate (x y : R) (n : nat) : bool :=
  Qlt_bool (R.upper_bound x (wpow2 n)) (R.lower_bound y (wpow2 n)) ||
  Qlt_bool (R.upper_bound y (wpow2 n)) (R.lower_bound x (wpow2 n)).

Lemma Rcan_discriminate_spec :
  forall x y n,
    Rcan_discriminate x y n = true <->
      is_Rlt_witness x y (wpow2 n) (wpow2 n) \/
      is_Rlt_witness y x (wpow2 n) (wpow2 n).
Proof.
  intros x y t.
  unfold Rcan_discriminate, is_Rlt_witness.
  rewrite orb_true_iff, Qlt_bool_iff, Qlt_bool_iff.
  tauto.
Qed.

Lemma Rcan_discriminate_exists :
  forall x y, x =/= y -> exists n, Rcan_discriminate x y n = true.
Proof.
  intros x y [H|H];
    apply Rlt_exists_same_witness in H;
    destruct H as [t H];
    exists (wlog2 t);
    apply Rcan_discriminate_spec;
    [left|right];
    apply H, wlog2_spec.
Defined.

Definition find_discriminating_power (x y : R) (p : x =/= y) : nat :=
  constructive_ground_epsilon_nat
    (fun n => Rcan_discriminate x y n = true)
    (fun n => bool_dec (Rcan_discriminate x y n) true)
    (Rcan_discriminate_exists x y p).

Lemma find_discriminating_power_spec :
  forall x y p, Rcan_discriminate x y (find_discriminating_power x y p) = true.
Proof.
  intros x y p.
  unfold find_discriminating_power.
  apply constructive_ground_epsilon_spec_nat.
Qed.

Definition Rlt_bool (x y : R) (p : x =/= y) : bool :=
  let n := find_discriminating_power x y p in
    Qlt_bool (R.upper_bound x (wpow2 n)) (R.lower_bound y (wpow2 n)).

Theorem Rlt_bool_spec :
  forall x y p, if Rlt_bool x y p then x < y else y < x.
Proof.
  intros x y p.
  destruct (Rlt_bool x y p) eqn:E;
    repeat exists (wpow2 (find_discriminating_power x y p)).
  - apply Qlt_bool_iff, E.
  - pose (find_discriminating_power_spec x y p) as H.
    unfold Rlt_bool in E.
    unfold Rcan_discriminate in H.
    rewrite E, orb_false_l in H.
    apply Qlt_bool_iff, H.
Defined.
