Require Import QArith.

Definition Rfun := positive -> Z.

Definition is_valid_Rfun f :=
  forall x y, (f x - 1) # x < (f y + 1) # y.

Definition R := {f | is_valid_Rfun f}.
