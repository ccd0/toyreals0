Require Import QArith.
Require Import Qround.
Require Import Qabs.
Require Import ConstructiveEpsilon.
Require Import Lia.

Definition Rfun : Set :=
  positive -> Q.

Definition Q2Rfun (x : Q) : Rfun :=
  fun tol => x.

Definition Rfun_le (x y : Rfun) : Prop :=
  forall tolx toly, x tolx - (1 # tolx) <= y toly + (1 # toly).

Definition Rfun_lt (x y : Rfun) : Prop :=
  exists tolx toly, x tolx + (1 # tolx) < y toly - (1 # toly).

Theorem Rfun_le_not_lt : forall x y, Rfun_le x y <-> ~ Rfun_lt y x.
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

Definition is_valid_Rfun (f : Rfun) : Prop :=
  Rfun_le f f.

Definition R : Set :=
  {f | is_valid_Rfun f}.

Theorem Q2Rfun_valid : forall x, is_valid_Rfun (Q2Rfun x).
  intros x tol1 tol2.
  apply Qplus_le_r.
  discriminate.
Qed.

Definition Q2R (x : Q) : R :=
  exist is_valid_Rfun (Q2Rfun x) (Q2Rfun_valid x).

Definition Rle (x y : R) : Prop :=
  Rfun_le (proj1_sig x) (proj1_sig y).

Definition Rge (x y : R) : Prop :=
  Rle y x.

Definition Req (x y : R) : Prop :=
  Rle x y /\ Rle y x.

Definition Rlt (x y : R) : Prop :=
  Rfun_lt (proj1_sig x) (proj1_sig y).

Definition Rgt (x y : R) : Prop :=
  Rlt y x.

Definition Rneq (x y : R) : Prop :=
  Rlt x y \/ Rlt y x.

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
  unfold Q2R, Q2Rfun, proj1_sig.
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

Definition RQapprox (tolerance : positive) (x : R) : Q :=
  proj1_sig x tolerance.

Theorem RQapprox_spec_l :
  forall t x, Rle (Q2R (RQapprox t x - (1 # t))) x.
Proof.
  intros t [x Hx] t1 t2.
  apply (Qle_trans _ (x t - (1 # t))).
  - rewrite <- (Qplus_0_r (x t - (1 # t))).
    apply Qplus_le_r.
    discriminate.
  - apply Hx.
Qed.

Theorem RQapprox_spec_u :
  forall t x, Rle x (Q2R (RQapprox t x + (1 # t))).
Proof.
  intros t [x Hx] t1 t2.
  apply (Qle_trans _ (x t + (1 # t))).
  - apply Hx.
  - rewrite <- (Qplus_0_r (x t + (1 # t))).
    apply Qplus_le_r.
    discriminate.
Qed.

Lemma Rneq0_exists_witness :
  forall x, Rneq x (Q2R 0) -> exists t, 1 # t < Qabs (RQapprox t x).
Proof.
  intros x [H|H]; destruct H as [t1 [t2 H]].
  - exists t1.
    apply (Qlt_le_trans _ (- RQapprox t1 x)).
    + apply (Qplus_lt_r _ _ (RQapprox t1 x)).
      rewrite Qplus_opp_r.
      apply (Qlt_trans _ (- (1 # t2))); trivial.
      reflexivity.
    + rewrite <- Qabs_opp.
      apply Qle_Qabs.
  - exists t2.
    apply (Qlt_le_trans _ (RQapprox t2 x)).
    + apply (Qplus_lt_l _ _ (- (1 # t2))).
      rewrite Qplus_opp_r.
      apply (Qlt_trans _ (1 # t1)); trivial.
      reflexivity.
    + apply Qle_Qabs.
Defined.

Definition Qlt_dec (x y : Q) : {x < y} + {~ x < y} :=
  match Qlt_le_dec x y with
  | left p => left p
  | right p => right (Qle_not_lt y x p)
  end.

Definition Rneq0_witness (x : R) (p : Rneq x (Q2R 0)) :=
  constructive_ground_epsilon
    positive Pos.to_nat Pos.of_nat Pos2Nat.id
    (fun t => 1 # t < Qabs(RQapprox t x))
    (fun t => Qlt_dec (1 # t) (Qabs (RQapprox t x)))
    (Rneq0_exists_witness x p).

Lemma Rneq0_witness_spec :
  forall x p, (1 # Rneq0_witness x p) < Qabs (RQapprox (Rneq0_witness x p) x).
Proof.
  intros x p.
  unfold Rneq0_witness.
  apply constructive_ground_epsilon_spec.
Qed.

Lemma Rneq0_witness_pos :
  forall t x, 1 # t < Qabs(RQapprox t x) ->
    0 < RQapprox t x -> Rgt x (Q2R 0).
Proof.
  intros t x H1 H2.
  rewrite Qabs_pos in H1 by apply Qlt_le_weak, H2.
  exists (Qsmaller (RQapprox t x - (1 # t))).
  exists t.
  apply Qsmaller_spec.
  apply (Qplus_lt_l _ _ (1 # t)).
  ring_simplify.
  trivial.
Defined.

Lemma Rneq0_witness_neg :
  forall t x, 1 # t < Qabs(RQapprox t x) ->
    RQapprox t x <= 0 -> Rlt x (Q2R 0).
Proof.
  intros t x H1 H2.
  rewrite Qabs_neg in H1 by trivial.
  exists t.
  exists (Qsmaller (- (RQapprox t x + (1 # t)))).
  setoid_rewrite Qplus_0_l.
  setoid_rewrite <- Qopp_opp at 1.
  apply Qopp_lt_compat.
  apply Qsmaller_spec.
  rewrite Qopp_plus.
  apply (Qplus_lt_l _ _ (1 # t)).
  ring_simplify.
  trivial.
Defined.

Definition Rpositive_dec (x : R) (p : Rneq x (Q2R 0)) : {Rgt x (Q2R 0)} + {Rlt x (Q2R 0)} :=
  match Qlt_le_dec 0 (RQapprox (Rneq0_witness x p) x) with
  | left pp  => left  (Rneq0_witness_pos (Rneq0_witness x p) x (Rneq0_witness_spec x p) pp)
  | right pn => right (Rneq0_witness_neg (Rneq0_witness x p) x (Rneq0_witness_spec x p) pn)
  end.

Definition Rpositive_bool (x : R) (p : Rneq x (Q2R 0)) : bool :=
  if Rpositive_dec x p then true else false.

Theorem Rpositive_bool_spec :
  forall x p, if Rpositive_bool x p then Rgt x (Q2R 0) else Rlt x (Q2R 0).
Proof.
  intros x p.
  unfold Rpositive_bool.
  destruct (Rpositive_dec x p) as [H|H]; trivial.
Defined.

Definition RQapprox_w_den (den : positive) (x : R) : Q :=
  Qfloor (RQapprox (2 * den) x * (Zpos den # 1) + (1 # 2)) # den.

Definition Rfun_plus (x y : Rfun) : Rfun :=
  fun tol => Qred (x (2 * tol)%positive + y (2 * tol)%positive).
