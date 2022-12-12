#!/bin/bash
coqc -R . ToyReals Reals.v
coqtop -R . ToyReals -batch -l extract.v
ocamlfind ocamlc -package js_of_ocaml -package js_of_ocaml-ppx -package zarith -linkpkg -o toyreals.byte toyreals.mli toyreals.ml export.ml
js_of_ocaml ../zarith_stubs_js/biginteger.js ../zarith_stubs_js/runtime.js exportjs.js toyreals.byte
