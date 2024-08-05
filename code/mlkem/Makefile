HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all:
	ocamlfind ocamlopt -verbose -I _build -I ${FSTAR_HOME}/lib/fstar/lib -o $(HACL_HOME)/code/mlkem/timing \
		-package zarith,batteries,ppx_deriving_yojson \
		${FSTAR_HOME}/lib/fstar/lib/fstar_lib.cmxa \
		$(HACL_HOME)/code/mlkem/_build/Lib_Sequence.cmxa \
		$(HACL_HOME)/code/mlkem/_build/Hacl_Spec_MLkem_Zq.cmxa \
		$(HACL_HOME)/code/mlkem/_build/Hacl_Spec_MLkem_NTT.cmxa \
		$(HACL_HOME)/code/mlkem/_build/Hacl_Spec_NTT_Fast.cmxa \
		$(HACL_HOME)/code/mlkem/timing.ml \
		-linkpkg

extract:
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.MLkem.NTT Hacl.Spec.MLkem.NTT.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.NTT.CT Hacl.Spec.NTT.CT.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.NTT.GS Hacl.Spec.NTT.GS.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.MLkem.Poly Hacl.Spec.MLkem.Poly.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.MLkem.PowModInt Hacl.Spec.MLkem.PowModInt.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.MLkem.Sums Hacl.Spec.MLkem.Sums.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.MLkem.Unity Hacl.Spec.MLkem.Unity.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Hacl.Spec.MLkem.Zq Hacl.Spec.MLkem.Zq.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Lib.Exponentiation.Definition Lib.Exponentiation.Definition.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Lib.Exponentiation Lib.Exponentiation.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Lib.LoopCombinators Lib.LoopCombinators.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Lib.NatMod Lib.NatMod.fst --warn_error -276 --include ../../lib
	fstar.exe --codegen OCaml --extract_module Lib.Sequence Lib.Sequence.fst --warn_error -276 --include ../../lib

compile_lib:
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_Minimal.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Lib_Exponentiation_Definition.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Lib_Exponentiation.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Lib_LoopCombinators.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Lib_NatMod.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Lib_Sequence.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_MLkem_Zq.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_MLkem_Poly.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_MLkem_Sums.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_MLkem_PowModInt.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_MLkem_Unity.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_MLkem_NTT.cmxa
	OCAMLPATH=${FSTAR_HOME}/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Hacl_Spec_NTT_Fast.cmxa

clean:
	.$(HACL_HOME)/code/mlkem/_build/sanitize.sh