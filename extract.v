Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import ZArith.
Require Import ToyReals.Reals.

Extraction Language OCaml.

Extract Constant Z.ggcd => "Big_int_Z.(fun x y ->
  let g = gcd_big_int x y in
    if sign_big_int g = 0 then
      (zero_big_int, (zero_big_int, zero_big_int))
    else
      (g, (div_big_int x g, div_big_int y g)))".

Extraction "toyreals" interval make_interval make_Stream R make_R lt_or_dec compare Q2R plus opp minus mult inv div N2Q N2R Z2R nested_RI_int round piecewise abs.
