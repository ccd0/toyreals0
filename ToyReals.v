Require Import QArith.

Definition Rfun := positive -> Z.

Definition is_valid_Rfun f :=
  forall x y, (f x - 1) # x < (f y + 1) # y.

Definition R := {f | is_valid_Rfun f}.

Definition Rfun_plus (f g : Rfun) : Rfun :=
  fun x => ((f (4 * x)%positive + g (4 * x)%positive + 2) / 4)%Z.
