Using the crypto library
=========================

Picking a distribution
----------------------

Building the full ``hacl-star`` repository verifies the source F* and Vale code,
then proceeds to extract it to C and assembly. However, users do not have to use
this full build process: we provide the generated code in the ``dist/``
directory, under version control to facilitate obtaining the source code.

Each subdirectory corresponds to a *distribution*, i.e. a particular set of
options passed to KaRaMeL (the F*-to-C compiler) that influence how the
generated C code looks like.

There is a total order on distributions:
``msvc-compatible <= gcc-compatible <= gcc64-only``

- The MSVC distribution relies on ``alloca`` to avoid C11 VLA for the sake of
  MSVC; relies on KaRaMeL for tail-call optimizations. It also does not use GCC
  inline assembly for Curve25519 and uses external linkage instead.
- The GCC distribution relies on C11 VLA and therefore does not work with MSVC.
- The GCC64 distribution assumes a native ``unsigned __int128`` type which can be
  manipulated via the standard arithmetic operators. This generates very compact
  code but only works on 64-bit GCC and Clang.

Other distributions are either for distinguished consumers of our code who need
specific KaRaMeL compilation options (e.g. Mozilla, CCF) or for testing (e.g.
portable-gcc-compatible, which compiles without ``-march=native``, to ensure all
our assumptions about CPU targets are explicit in our Makefile).

Compiling a full distribution
-----------------------------

Each distribution comes with its own Makefile. It builds a static object
(libevercrypt.a) and a dynamic object (libevercrypt.{so,dll}) along with the
import library for Windows systems (libevercrypt.dll.a). On Windows, the
Makefile has been tested in a Cygwin environment equipped with the MinGW
cross-compilers. The `dist/compact-msvc` distribution works with the Microsoft
compilers, but we provide no build support (i.e. no Visual Studio project, no
NMake-compatible makefile).

.. note::

  The ``gcc-compatible`` distribution also features OCaml bindings to our code.
  These require a valid OCaml setup, including packages ctypes
  and bigstring, usually obtained via OPAM. You can easily disable building
  these bindings by removing the ``lib_gen`` directory in
  ``dist/gcc-compatible``.

Integrating the code
--------------------

To incorporate our verified crypto code into a C software project, a developer
has two choices.

- Pick a full EverCrypt distribution, along with the
  `dist/karamel` directory, thus giving a "wholesale" integration of
  the EverCrypt library, including all supported algorithms from HACL* and Vale.
- For a more selective integration, cherry-pick the C or assembly
  files for specific versions of specific algorithms.  Each header
  file contains the list of other headers (and implementations) it
  depends on so it's easy to integrate, say, an individual algorithm
  from the HACL API without taking the full library.

The ``dist/karamel`` directory contains all the required headers from
KaRaMeL.  In particular, these headers contain implementations of
FStar.UInt128, the module for 128-bit arithmetic. The
``karamel/include/krml/internal/types.h`` header will attempt to
use C preprocessor macros to pick the right UInt128 implementation for
your platform:

- 64-bit environment with GCC/Clang: hand-written implementation using
  ``unsigned __int128`` (unverified)
- MSVC: hand-written implementation using intrinsics (also unverified)
- every other case, or when ``KRML_VERIFIED_UINT128`` is defined at compile-time:
  verified (slow) implementation extracted from FStar.UInt128


Bindings for Other Languages
----------------------------

HACL* and EverCrypt are designed to primarily be used either within
verification-oriented projects in F* or as part of larger C
developments.  In addition to these use cases, the library developers
and other HACL* users have also developed bindings for other programming languages:

OCaml
^^^^^

OCaml bindings were moved to the `cryspen/hacl-packages` repository.
Documentation is available here: `<https://tech.cryspen.com/hacl-packages/hacl-ocaml/index.html>`.

JavaScript
^^^^^^^^^^

JS bindings were moved to the `cryspen/hacl-packages` repository.
Documentation is available here: `<https://tech.cryspen.com/hacl-packages/hacl-js/index.html>`.

Rust
^^^^

Various users have also published Rust crates for HACL*, but these have not been
vetted by the HACL maintainers.
