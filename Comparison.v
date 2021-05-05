Require Import ToyReals.Reals.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qminmax.
Require Import Coq.Logic.ConstructiveEpsilon.
Global Close Scope Q_scope.

Local Open Scope R_scope.
Import R.

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
