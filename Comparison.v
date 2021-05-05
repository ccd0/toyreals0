Require Import ToyReals.Reals.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Logic.ConstructiveEpsilon.
Global Close Scope Q_scope.

Local Open Scope R_scope.

Definition is_Rlt_witness (x y : R) (tx ty : Q) : Prop :=
  (R.upper_bound x tx < R.lower_bound y ty)%Q.

Theorem Rlt_same_witness :
  forall x y tx ty,
    is_Rlt_witness x y tx ty ->
      forall t, (8 / (R.lower_bound y ty - R.upper_bound x tx) <= t)%Q ->
        is_Rlt_witness x y t t.
Proof.
  intros x y tx ty H t Ht.
  unfold is_Rlt_witness in *.
  set (a := R.upper_bound x tx) in *.
  set (b := R.lower_bound y ty) in *.
  apply Qlt_minus_iff in H.
  apply (Qlt_le_trans (4 / (b - a))) in Ht;
    [|apply Qmult_lt_r; [apply Qinv_lt_0_compat, H|reflexivity]].
  setoid_replace (4 / (b - a))%Q with (2 / ((b - a) / 2))%Q in Ht
    by (field; apply Qnot_eq_sym, Qlt_not_eq, H).
  apply (Qmult_lt_r _ _ (/ 2)) in H; [|reflexivity].
  rewrite Qmult_0_l in H.
  apply (Qlt_trans _ (R.lower_bound x t + (b - a) / 2)),
    (Qle_lt_trans _ (a + (b - a) / 2)),
    (Qle_lt_trans _ (R.upper_bound y t - (b - a) / 2)).
  - apply R.bound_diff_control_u; trivial.
  - apply Qplus_le_l, R.compute_consistent.
  - setoid_replace (a + (b - a) / 2)%Q with (b - (b - a) / 2)%Q by field.
    apply Qplus_le_l, R.compute_consistent.
  - apply R.bound_diff_control_l; trivial.
Qed.

Theorem Rlt_same_witness_exists :
  forall x y, x < y ->
    exists t, forall t2, (t <= t2)%Q -> is_Rlt_witness x y t2 t2.
Proof.
  intros x y [tx [ty H]].
  exists (8 / (R.lower_bound y ty - R.upper_bound x tx))%Q.
  apply Rlt_same_witness, H.
Defined.

Definition wlog2 (t : Q) : nat :=
  Nat.log2_up (Z.to_nat (Z.max 2 (Qceiling t))).

Definition wpow2 (n : nat) : Q :=
  inject_Z (Z.of_nat (2 ^ n)).

Theorem wlog2_spec :
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

Theorem Qlt_bool_iff : forall x y : Q, Qlt_bool x y = true <-> (x < y)%Q.
Proof.
  intros x y.
  apply Z.ltb_lt.
Qed.

Definition Rcan_discriminate (x y : R) (n : nat) : bool :=
  Qlt_bool (R.upper_bound x (wpow2 n)) (R.lower_bound y (wpow2 n)) ||
  Qlt_bool (R.upper_bound y (wpow2 n)) (R.lower_bound x (wpow2 n)).

Theorem Rcan_discriminate_spec :
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

Theorem Rcan_discriminate_exists :
  forall x y, x =/= y -> exists n, Rcan_discriminate x y n = true.
Proof.
  intros x y [H|H];
    apply Rlt_same_witness_exists in H;
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

Theorem find_discriminating_power_spec :
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
