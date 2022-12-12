Require Coq.extraction.Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import ToyReals.Reals.

Extraction Language OCaml.
Extraction "toyreals" interval make_interval make_Stream R make_R lt_or_dec compare Q2R plus opp minus mult inv div N2Q N2R Z2R nested_RI_int.
