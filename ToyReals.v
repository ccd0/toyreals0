Require Import QArith.
Require Import Qround.

Definition Rfun : Set :=
  positive -> Q.

Definition Q2Rfun (x : Q) : Rfun :=
  fun tol => x.

Definition Rfun_le (x y : Rfun) : Prop :=
  forall tolx toly, x tolx - (1 # tolx) <= y toly + (1 # toly).

Definition Rfun_lt (x y : Rfun) : Prop :=
  exists tolx toly, x tolx + (1 # tolx) < y toly - (1 # toly).

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

Theorem Rneq0_exists_witness :
  forall x, Rneq x (Q2R 0) -> exists t,
    RQapprox t x + (1 # t) < 0 \/ 0 < RQapprox t x - (1 # t).
Proof.
  intros x [H|H]; destruct H as [t1 [t2 H]].
  - exists t1.
    left.
    apply (Qlt_trans _ _ _ H).
    reflexivity.
  - exists t2.
    right.
    revert H.
    apply Qlt_trans.
    reflexivity.
Qed.

Definition RQapprox_w_den (den : positive) (x : R) : Q :=
  Qfloor (RQapprox (2 * den) x * (Zpos den # 1) + (1 # 2)) # den.

Definition Rfun_plus (x y : Rfun) : Rfun :=
  fun tol => Qred (x (2 * tol)%positive + y (2 * tol)%positive).
