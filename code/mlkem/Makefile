HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all:
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.Minimal Hacl.Spec.Minimal.fst --warn_error -276 --include ../../lib
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib $(HACL_HOME)/code/mlkem/Hacl_Spec_Minimal.cmxa
	ocamlopt -verbose -I _build/hacl-star/code/mlkem -o $(HACL_HOME)/code/mlkem/timing _build/hacl-star/code/mlkem/Hacl_Spec_Minimal.cmxa $(HACL_HOME)/code/mlkem/timing.ml

clean:
	.$(HACL_HOME)/code/mlkem/_build/sanitize.sh