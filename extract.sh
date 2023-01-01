#!/bin/bash
coqc -R . ToyReals Reals.v
coqtop -R . ToyReals -batch -l extract.v
ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml-ppx -package zarith -linkpkg -o toyreals.byte toyreals.mli toyreals.ml export.ml
zsj=$(ocamlfind query zarith_stubs_js)
js_of_ocaml "$zsj/biginteger.js" "$zsj/runtime.js" exportjs.js toyreals.byte
