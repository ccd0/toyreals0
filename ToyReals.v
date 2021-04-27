Require Import QArith.
Require Import Qround.
Require Import Qabs.
Require Import ConstructiveEpsilon.
Require Import Lia.

Definition Rfun : Set :=
  positive -> Q.

Definition is_valid_Rfun (x : Rfun) : Prop :=
  forall t1 t2, x t1 - (1 # t1) <= x t2 + (1 # t2).

Definition R : Set :=
  {x | is_valid_Rfun x}.

Definition RQapprox (x : R) (tolerance : positive) : Q :=
  match x with
  | exist _ f _ => f
  end tolerance.

Theorem RQapprox_spec : forall x, is_valid_Rfun (RQapprox x).
  intros [x H].
  apply H.
Qed.

Theorem Q2Rfun_valid : forall x, is_valid_Rfun (fun t => x).
  intros x tol1 tol2.
  apply Qplus_le_r.
  discriminate.
Qed.

Definition Q2R (x : Q) : R :=
  exist is_valid_Rfun (fun t => x) (Q2Rfun_valid x).

Definition Rle (x y : R) : Prop :=
  forall tx ty, RQapprox x tx - (1 # tx) <= RQapprox y ty + (1 # ty).

Definition Rge (x y : R) : Prop :=
  Rle y x.

Definition Req (x y : R) : Prop :=
  Rle x y /\ Rle y x.

Definition Rlt (x y : R) : Prop :=
  exists tx ty, RQapprox x tx + (1 # tx) < RQapprox y ty - (1 # ty).

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

Theorem RQapprox_lower_bound :
  forall x t, Rle (Q2R (RQapprox x t - (1 # t))) x.
Proof.
  intros x t t1 t2.
  cbn.
  apply (Qle_trans _ (RQapprox x t - (1 # t))).
  - rewrite <- (Qplus_0_r (RQapprox x t - (1 # t))) at 2.
    apply Qplus_le_r.
    discriminate.
  - apply RQapprox_spec.
Qed.

Theorem RQapprox_upper_bound :
  forall x t, Rle x (Q2R (RQapprox x t + (1 # t))).
Proof.
  intros x t t1 t2.
  cbn.
  apply (Qle_trans _ (RQapprox x t + (1 # t))).
  - apply RQapprox_spec.
  - rewrite <- (Qplus_0_r (RQapprox x t + (1 # t))) at 1.
    apply Qplus_le_r.
    discriminate.
Qed.

Lemma Rneq0_exists_witness :
  forall x, Rneq x (Q2R 0) -> exists t, 1 # t < Qabs (RQapprox x t).
Proof.
  intros x [H|H]; destruct H as [t1 [t2 H]].
  - exists t1.
    apply (Qlt_le_trans _ (- RQapprox x t1)).
    + apply (Qplus_lt_r _ _ (RQapprox x t1)).
      rewrite Qplus_opp_r.
      apply (Qlt_trans _ (- (1 # t2))); trivial.
      reflexivity.
    + rewrite <- Qabs_opp.
      apply Qle_Qabs.
  - exists t2.
    apply (Qlt_le_trans _ (RQapprox x t2)).
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
    (fun t => 1 # t < Qabs(RQapprox x t))
    (fun t => Qlt_dec (1 # t) (Qabs (RQapprox x t)))
    (Rneq0_exists_witness x p).

Lemma Rneq0_witness_spec :
  forall x p, (1 # Rneq0_witness x p) < Qabs (RQapprox x (Rneq0_witness x p)).
Proof.
  intros x p.
  unfold Rneq0_witness.
  apply constructive_ground_epsilon_spec.
Qed.

Lemma Rneq0_witness_pos :
  forall x t, 1 # t < Qabs(RQapprox x t) ->
    0 < RQapprox x t -> Rgt x (Q2R 0).
Proof.
  intros x t H1 H2.
  rewrite Qabs_pos in H1 by apply Qlt_le_weak, H2.
  exists (Qsmaller (RQapprox x t - (1 # t))).
  exists t.
  apply Qsmaller_spec.
  apply (Qplus_lt_l _ _ (1 # t)).
  ring_simplify.
  trivial.
Defined.

Lemma Rneq0_witness_neg :
  forall x t, 1 # t < Qabs(RQapprox x t) ->
    RQapprox x t <= 0 -> Rlt x (Q2R 0).
Proof.
  intros x t H1 H2.
  rewrite Qabs_neg in H1 by trivial.
  exists t.
  exists (Qsmaller (- (RQapprox x t + (1 # t)))).
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
  match Qlt_le_dec 0 (RQapprox x (Rneq0_witness x p)) with
  | left pp  => left  (Rneq0_witness_pos x (Rneq0_witness x p) (Rneq0_witness_spec x p) pp)
  | right pn => right (Rneq0_witness_neg x (Rneq0_witness x p) (Rneq0_witness_spec x p) pn)
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

Definition RQapprox_w_den (x : R) (den : positive) : Q :=
  Qfloor (RQapprox x (2 * den) * (Zpos den # 1) + (1 # 2)) # den.

Definition Rfun_plus (x y : Rfun) : Rfun :=
  fun tol => Qred (x (2 * tol)%positive + y (2 * tol)%positive).
