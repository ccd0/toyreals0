Require Import QArith.
Require Import Qround.

Definition Rfun : Set :=
  positive -> Q.

Definition Rfun_le (x y : Rfun) : Prop :=
  forall tolx toly, x tolx - (1 # tolx) < y toly + (1 # toly).

Definition Rfun_lt (x y : Rfun) : Prop :=
  exists tolx toly, x tolx + (1 # tolx) <= y toly - (1 # toly).

Definition is_valid_Rfun (f : Rfun) : Prop :=
  Rfun_le f f.

Definition R : Set :=
  {f | is_valid_Rfun f}.

Definition RQapprox (tolerance : positive) (x : R) : Q :=
  proj1_sig x tolerance.

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

Definition RQapprox_w_den (den : positive) (x : R) : Q :=
  Qfloor (RQapprox (2 * den) x * (Zpos den # 1) + (1 # 2)) # den.

Definition Rfun_plus (x y : Rfun) : Rfun :=
  fun tol => Qred (x (2 * tol)%positive + y (2 * tol)%positive).
