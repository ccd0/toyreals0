Require Import QArith.

Definition Rfun : Set :=
  positive -> Z.

Definition Rfun_le (f g : Rfun) : Prop :=
  forall x y, (f x - 1) # x < (g y + 1) # y.

Definition Rfun_lt (f g : Rfun) : Prop :=
  exists x y, (f x + 1) # x <= (g y - 1) # y.

Definition is_valid_Rfun (f : Rfun) : Prop :=
  Rfun_le f f.

Definition R : Set :=
  {f | is_valid_Rfun f}.

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

Definition Rfun_plus (f g : Rfun) : Rfun :=
  fun x => ((f (4 * x)%positive + g (4 * x)%positive + 2) / 4)%Z.
