## OPAM switches
The pipeline for the `malfunction-*` backends uses programs installed in a variety of OPAM switches,
whose names are configurable via Make variables.
- `PEREGRINE_SWITCH`: in which the `peregrine` tool is installed.
- `MALFUNCTION_NO_FLAMBDA_SWITCH`: in which the `malfunction` executable is installed.
  Used when the Make variable `FLAMBDA` is set to `0` (e.g. when using the backend `malfunction-noflambda`).
  This switch should have an OCaml toolchain without flambda.
- `MALFUNCTION_FLAMBDA_SWITCH`: in which the `malfunction` executable is installed.
  Used when the Make variable `FLAMBDA` is set to `1`.
  This switch should have an OCaml toolchain with flambda.

These four switches are not required to be distinct or have matching OCaml versions.

Each backend uses one switch for `peregrine` and one for `malfunction` switch;
For example, `malfunction-reference` refers to `PEREGRINE_SWITCH` and `MALFUNCTION_FLAMBDA_SWITCH`,
but does not require the switch `MALFUNCTION_NOFLAMBDA_SWITCH` to exist.

## Configuration options
These Make variables control the behavior of the pipeline.
- `UNBOX` (0 or 1 (default)): whether to perform unboxing of single-constructor single-argument inductive types.
- `PRUNE_CONSTRUCTORS` (0 or 1 (default)): whether to remove irrelevant arguments from constructors during erasure.
- `INLINE_AXIOMS` (0 or 1 (default)): whether to use versions of the OCaml axioms providing fast arithmetic with inlining annotations.
- `FLAMBDA` (0 or 1 (default)): whether to use an OCaml toolchain with Flambda optimizations.
- `ARRAYML` ("JCFArray.ml" (default), "SekArray.ml" or "UnsafeArray.ml"): which implementation of the array axioms to use.
  Using `SekArray.ml` requires the OCaml package `Sek` to be installed in the appropriate `MALFUNCTION` switch.
