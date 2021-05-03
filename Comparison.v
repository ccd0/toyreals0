Require Import ToyReals.Reals.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Logic.ConstructiveEpsilon.

Definition is_Rlt_witness (x y : R) (t : Q * Q) : Prop :=
  R.upper_bound x (fst t) < R.lower_bound y (snd t).

Lemma is_Rlt_witness_spec :
  forall x y t, is_Rlt_witness x y t -> R.lt x y.
Proof.
  intros x y [tx ty] H.
  exists tx, ty.
  exact H.
Defined.

Definition is_Rlt_witness_bool (x y : R) (t : Q * Q) : bool :=
  negb (Qle_bool (R.lower_bound y (snd t)) (R.upper_bound x (fst t))).

Lemma is_Rlt_witness_bool_spec :
  forall x y t, is_Rlt_witness_bool x y t = true <-> is_Rlt_witness x y t.
Proof.
  intros x y [tx ty].
  unfold is_Rlt_witness_bool, is_Rlt_witness.
  cbn.
  rewrite negb_true_iff.
  rewrite <- not_true_iff_false.
  rewrite Qle_bool_iff.
  split; [apply Qnot_le_lt|apply Qlt_not_le].
Qed.

Definition wsame (t : Q) : Q * Q := (t, t).

Definition Rlt_witness_make_same (x y : R) (t : Q * Q) : Q :=
  8 / (R.lower_bound y (snd t) - R.upper_bound x (fst t)).

Lemma Rlt_witness_make_same_spec :
  forall x y t,
    is_Rlt_witness x y t ->
      forall t2, Rlt_witness_make_same x y t <= t2 ->
        is_Rlt_witness x y (wsame t2).
Proof.
  intros x y [tx ty] H t Ht.
  unfold is_Rlt_witness.
  setoid_replace (R.upper_bound x t)
    with (R.lower_bound x t + 2 * RE.error (R.compute x t))
    by (unfold R.upper_bound, R.lower_bound, RE.min, RE.max; ring).
  setoid_replace (R.lower_bound y t)
    with (R.upper_bound y t - 2 * RE.error (R.compute y t))
    by (unfold R.upper_bound, R.lower_bound, RE.min, RE.max; ring).
  apply (Qle_lt_trans _ (R.upper_bound x tx + 2 * RE.error (R.compute x t)));
    [apply Qplus_le_l, R.compute_consistent|].
  apply (Qlt_le_trans _ (R.lower_bound y ty - 2 * RE.error (R.compute y t)));
    [|apply Qplus_le_l, R.compute_consistent].
  apply (Qplus_lt_l _ _ (2 * RE.error (R.compute y t) - R.upper_bound x tx)).
  apply (Qmult_lt_l _ _ (1 # 2)); [reflexivity|].
  ring_simplify.
  setoid_replace ((-1 # 2) * R.upper_bound x tx + (1 # 2) * R.lower_bound y ty)
    with ((R.lower_bound y ty - R.upper_bound x tx) / 2) by field.
  unfold Rlt_witness_make_same in Ht.
  cbn in Ht.
  set (z := R.lower_bound y ty - R.upper_bound x tx) in *.
  assert (z > 0) as Hz.
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

Definition is_Rneq_witness (x y : R) (t : Q * Q) : Prop :=
  is_Rlt_witness x y t \/ is_Rlt_witness y x t.

Lemma is_Rneq_witness_spec :
  forall x y t, is_Rneq_witness x y t -> R.neq x y.
Proof.
  intros x y t [H|H]; [left|right];
    apply (is_Rlt_witness_spec _ _ t H).
Defined.

Lemma Rneq_witness_exists :
  forall x y, R.neq x y -> exists t, is_Rneq_witness x y t.
Proof.
  intros x y p.
  destruct p as [p|p];
    destruct p as [t1 [t2 p]];
    exists ((t1, t2));
    [left|right];
    exact p.
Defined.

Definition is_Rneq_witness_bool (x y : R) (t : Q * Q) : bool :=
  is_Rlt_witness_bool x y t || is_Rlt_witness_bool y x t.

Lemma is_Rneq_witness_bool_spec :
  forall x y t, is_Rneq_witness_bool x y t = true <-> is_Rneq_witness x y t.
Proof.
  intros x y t.
  unfold is_Rneq_witness_bool, is_Rneq_witness.
  rewrite orb_true_iff.
  repeat rewrite is_Rlt_witness_bool_spec.
  tauto.
Qed.

Lemma Rneq_witness_not_lt_gt :
  forall x y t, is_Rneq_witness x y t ->
    is_Rlt_witness_bool x y t = false -> is_Rlt_witness y x t.
Proof.
  intros x y t H1 H2.
  destruct H1 as [H1|H1]; trivial.
  apply is_Rlt_witness_bool_spec in H1.
  contradict H1.
  rewrite H2.
  discriminate.
Qed.

Definition Rneq_witness_make_same (x y : R) (t : Q * Q) : Q :=
  if is_Rlt_witness_bool x y t then
    Rlt_witness_make_same x y t
  else
    Rlt_witness_make_same y x t.

Lemma Rneq_witness_make_same_spec :
  forall x y t,
    is_Rneq_witness x y t ->
      forall t2, Rneq_witness_make_same x y t <= t2 ->
        is_Rneq_witness x y (wsame t2).
Proof.
  intros x y t Ht t2 Ht2.
  unfold Rneq_witness_make_same, is_Rneq_witness in *.
  destruct (is_Rlt_witness_bool x y t) eqn:E.
  - left.
    apply (Rlt_witness_make_same_spec x y t); trivial.
    apply is_Rlt_witness_bool_spec, E.
  - right.
    apply (Rlt_witness_make_same_spec y x t); trivial.
    apply Rneq_witness_not_lt_gt; trivial.
Qed.

Definition wlog2 (t : Q) : nat :=
  Nat.log2_up (Z.to_nat (Z.max 2 (Qceiling t))).

Definition wpow2 (n : nat) : Q :=
  inject_Z (Z.of_nat (2 ^ n)).

Lemma wlog2_spec :
  forall t, t <= wpow2 (wlog2 t).
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
  apply (lt_le_trans _ 2); auto.
  change (Z.to_nat 2 <= Z.to_nat (Z.max 2 (Qceiling t)))%nat.
  apply Z2Nat.inj_le; trivial; try discriminate.
  apply Z.le_max_l.
Qed.

Definition is_Rneq_witness_pow2 (x y : R) (n : nat) : bool :=
  is_Rneq_witness_bool x y (wsame (wpow2 n)).

Lemma Rneq_witness_pow2_exists :
  forall x y, R.neq x y -> exists n, is_Rneq_witness_pow2 x y n = true.
Proof.
  intros x y p.
  apply Rneq_witness_exists in p.
  destruct p as [t p].
  set (t2 := Rneq_witness_make_same x y t).
  exists (wlog2 t2).
  apply is_Rneq_witness_bool_spec.
  apply (Rneq_witness_make_same_spec x y t p).
  apply wlog2_spec.
Defined.

Definition get_Rneq_witness (x y : R) (p : R.neq x y) : Q * Q :=
  wsame (wpow2 (
    constructive_ground_epsilon_nat
      (fun n => is_Rneq_witness_pow2 x y n = true)
      (fun n => bool_dec (is_Rneq_witness_pow2 x y n) true)
      (Rneq_witness_pow2_exists x y p)
  )).

Lemma get_Rneq_witness_spec :
  forall x y p, is_Rneq_witness x y (get_Rneq_witness x y p).
Proof.
  intros x y p.
  unfold get_Rneq_witness.
  apply is_Rneq_witness_bool_spec.
  apply constructive_ground_epsilon_spec_nat.
Defined.

Definition Rlt_bool (x y : R) (p : R.neq x y) : bool :=
  is_Rlt_witness_bool x y (get_Rneq_witness x y p).

Theorem Rlt_bool_spec :
  forall x y p, if Rlt_bool x y p then R.lt x y else R.lt y x.
Proof.
  intros x y p.
  unfold Rlt_bool.
  set (t := get_Rneq_witness x y p).
  destruct (is_Rlt_witness_bool x y t) eqn:E.
  - apply (is_Rlt_witness_spec x y t).
    apply is_Rlt_witness_bool_spec, E.
  - apply (is_Rlt_witness_spec y x t).
    apply Rneq_witness_not_lt_gt; trivial.
    apply get_Rneq_witness_spec.
Defined.
