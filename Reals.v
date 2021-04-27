Require Import QArith.
Require Import Qround.
Require Import ConstructiveEpsilon.
Require Import Lia.

Definition Rfun : Set :=
  positive -> Q.

Definition is_valid_Rfun (x : Rfun) : Prop :=
  forall t1 t2, x t1 - (1 # t1) <= x t2 + (1 # t2).

Inductive R : Set :=
  | Rmake (x : Rfun) (p : is_valid_Rfun x) : R.

Definition RQapprox (x : R) (tolerance : positive) : Q :=
  match x with
  | Rmake f _ => f
  end tolerance.

Definition R_lower_bound (x : R) (t : positive) : Q :=
  RQapprox x t - (1 # t).

Definition R_upper_bound (x : R) (t : positive) : Q :=
  RQapprox x t + (1 # t).

Theorem RQapprox_spec :
  forall x t1 t2, R_lower_bound x t1 <= R_upper_bound x t2.
Proof.
  intros [x H].
  apply H.
Qed.

Theorem Q2Rfun_valid : forall x, is_valid_Rfun (fun t => x).
  intros x tol1 tol2.
  apply Qplus_le_r.
  discriminate.
Qed.

Definition Q2R (x : Q) : R :=
  Rmake (fun t => x) (Q2Rfun_valid x).

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

Definition Qsmaller (x : Q) : positive :=
  2 * Qden x.

Theorem Qsmaller_spec :
  forall x : Q, x > 0 -> 1 # (Qsmaller x) < x.
Proof.
  intros [p q] H.
  unfold Qsmaller, Qlt, Qnum, Qden in *.
  rewrite Pos2Z.inj_mul.
  rewrite Zmult_assoc.
  apply Zmult_lt_compat_r; lia.
Qed.

Theorem Q2R_lt : forall x y, x < y -> Rlt (Q2R x) (Q2R y).
  intros x y H.
  pose (Qsmaller ((y - x) / 2)) as t.
  exists t, t.
  unfold R_upper_bound, R_lower_bound.
  cbn - [t].
  apply (Qplus_lt_l _ _ ((1 # t) - x)).
  apply (Qmult_lt_r _ _ (1 # 2)); [reflexivity|].
  ring_simplify.
  setoid_replace ((-1 # 2) * x + (1 # 2) * y) with ((y - x) / 2) by field.
  apply Qsmaller_spec.
  rewrite <- (Qmult_0_l (/ 2)).
  apply Qmult_lt_r; [reflexivity|].
  apply (Qplus_lt_l _ _ x).
  ring_simplify.
  trivial.
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
  - unfold R_lower_bound.
    rewrite <- (Qplus_0_r (RQapprox x t - (1 # t))) at 2.
    apply Qplus_le_r.
    discriminate.
  - apply RQapprox_spec.
Qed.

Theorem R_upper_bound_spec :
  forall x t, Rle x (Q2R (R_upper_bound x t)).
Proof.
  intros x t t1 t2.
  apply (Qle_trans _ (R_upper_bound x t)).
  - apply RQapprox_spec.
  - rewrite <- (Qplus_0_r (RQapprox x t + (1 # t))) at 1.
    apply Qplus_le_r.
    discriminate.
Qed.

Definition RQapprox_w_den (x : R) (den : positive) : Q :=
  Qfloor (RQapprox x (2 * den) * (Zpos den # 1) + (1 # 2)) # den.

Definition Rfun_plus (x y : Rfun) : Rfun :=
  fun tol => Qred (x (2 * tol)%positive + y (2 * tol)%positive).

Definition is_Rlt_witness (x y : R) (t : positive * positive) : Prop :=
  R_upper_bound x (fst t) < R_lower_bound y (snd t).

Lemma is_Rlt_witness_spec :
  forall x y t, is_Rlt_witness x y t -> Rlt x y.
Proof.
  intros x y [tx ty] H.
  exists tx, ty.
  exact H.
Defined.

Definition is_Rlt_witness_bool (x y : R) (t : positive * positive) : bool :=
  negb (Qle_bool (R_lower_bound y (snd t)) (R_upper_bound x (fst t))).

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

Definition wsame (t : positive) : positive * positive := (t, t).

Definition Rlt_witness_make_same (x y : R) (t : positive * positive) : positive :=
  Qsmaller ((R_lower_bound y (snd t) - R_upper_bound x (fst t)) / 4).

Lemma Rlt_witness_make_same_spec :
  forall x y t,
    is_Rlt_witness x y t ->
      forall t2, (Rlt_witness_make_same x y t <= t2)%positive ->
        is_Rlt_witness x y (wsame t2).
Proof.
  intros x y [tx ty] H t Ht.
  unfold is_Rlt_witness.
  setoid_replace (R_upper_bound x t)
    with (R_lower_bound x t + 2 * (1 # t))
    by (unfold R_upper_bound, R_lower_bound; ring).
  setoid_replace (R_lower_bound y t)
    with (R_upper_bound y t - 2 * (1 # t))
    by (unfold R_upper_bound, R_lower_bound; ring).
  apply (Qle_lt_trans _ (R_upper_bound x tx + 2 * (1 # t)));
    [apply Qplus_le_l, RQapprox_spec|].
  apply (Qlt_le_trans _ (R_lower_bound y ty - 2 * (1 # t)));
    [|apply Qplus_le_l, RQapprox_spec].
  apply (Qplus_lt_l _ _ (2 * (1 # t) - R_upper_bound x tx)).
  apply (Qmult_lt_l _ _ (1 # 4)); [reflexivity|].
  ring_simplify.
  setoid_replace ((-1 # 4) * R_upper_bound x tx + (1 # 4) * R_lower_bound y ty)
    with ((R_lower_bound y ty - R_upper_bound x tx) / 4) by field.
  unfold Rlt_witness_make_same in Ht.
  set (z := (R_lower_bound y ty - R_upper_bound x tx) / 4) in *.
  apply (Qle_lt_trans _ (1 # (Qsmaller z)));
    [apply Pos2Z.pos_le_pos, Ht|].
  apply Qsmaller_spec.
  subst z.
  setoid_replace 0 with (0 / 4) by reflexivity.
  apply Qmult_lt_r; [reflexivity|].
  setoid_rewrite <- (Qplus_opp_r (R_upper_bound x tx)).
  apply Qplus_lt_l.
  apply H.
Qed.

Definition is_Rneq_witness (x y : R) (t : positive * positive) : Prop :=
  is_Rlt_witness x y t \/ is_Rlt_witness y x t.

Lemma is_Rneq_witness_spec :
  forall x y t, is_Rneq_witness x y t -> Rneq x y.
Proof.
  intros x y t [H|H]; [left|right];
    apply (is_Rlt_witness_spec _ _ t H).
Defined.

Lemma Rneq_witness_exists :
  forall x y, Rneq x y -> exists t, is_Rneq_witness x y t.
Proof.
  intros x y p.
  destruct p as [p|p];
    destruct p as [t1 [t2 p]];
    exists ((t1, t2));
    [left|right];
    exact p.
Defined.

Definition is_Rneq_witness_bool (x y : R) (t : positive * positive) : bool :=
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

Definition Rneq_witness_make_same (x y : R) (t : positive * positive) : positive :=
  if is_Rlt_witness_bool x y t then
    Rlt_witness_make_same x y t
  else
    Rlt_witness_make_same y x t.

Lemma Rneq_witness_make_same_spec :
  forall x y t,
    is_Rneq_witness x y t ->
      forall t2, (Rneq_witness_make_same x y t <= t2)%positive ->
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

Definition wlog2 (t : positive) : nat :=
  Nat.log2_up (Pos.to_nat t).

Definition wpow2 (n : nat) :=
  Pos.of_nat (2 ^ n).

Lemma wlog2_spec :
  forall t, (t <= wpow2 (wlog2 t))%positive.
Proof.
  intro t.
  unfold wpow2, wlog2.
  apply Pos2Nat.inj_le.
  rewrite Nat2Pos.id by (apply Nat.pow_nonzero; discriminate).
  apply Nat.log2_log2_up_spec.
  apply Pos2Nat.is_pos.
Qed.

Definition is_Rneq_witness_pow2 (x y : R) (n : nat) : bool :=
  is_Rneq_witness_bool x y (wsame (wpow2 n)).

Lemma Rneq_witness_pow2_exists :
  forall x y, Rneq x y -> exists n, is_Rneq_witness_pow2 x y n = true.
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

Definition get_Rneq_witness (x y : R) (p : Rneq x y) : positive * positive :=
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

Definition Rlt_bool (x y : R) (p : Rneq x y) : bool :=
  is_Rlt_witness_bool x y (get_Rneq_witness x y p).

Theorem Rlt_bool_spec :
  forall x y p, if Rlt_bool x y p then Rlt x y else Rlt y x.
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
