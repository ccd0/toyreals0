Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.

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
  Qden x + 1.

Theorem Qsmaller_spec :
  forall x : Q, x > 0 -> 1 # (Qsmaller x) < x.
Proof.
  intros [p q] H.
  unfold Qlt in *.
  cbn in *.
  rewrite Pos2Z.inj_add.
  rewrite <- (Z.mul_1_l (Z.pos q)) at 1.
  apply Zmult_lt_compat2.
  - rewrite Z.mul_1_r in H.
    split; [reflexivity|].
    apply (Zlt_le_succ 0), H.
  - split.
    + apply Pos2Z.is_pos.
    + apply Z.lt_add_pos_r.
      reflexivity.
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
