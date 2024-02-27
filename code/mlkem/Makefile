HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all:
	fstar.exe --codegen krml --extract_module Hacl.MLkem.Poly Hacl.MLKem.Poly.fst --include ../../lib
	krml -skip-compilation Hacl_MLkem_Poly.krml -warn-error @4@5@18 \
    -fparentheses \
    -bundle 'LowStar.*,Prims' \
    -minimal \
    -bundle 'FStar.*' \
    -add-include '<stdint.h>' \
    -add-include '"krml/internal/target.h"'
