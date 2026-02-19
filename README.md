# Peregrine project

## Directories
* `peregrine`
   Contains the middleend and extraction backends for $\lambda_\square$
  * `peregrine/cakeml`
   Contains the CakeML extraction backend
  * `peregrine/plugin` Contains Rocq frontend
  * `peregrine/theories` Rocq sources for the middleend
  * `peregrine/src` `peregrine/bin` Standalone executable of Peregrine extracted from the Rocq sources
  * `peregrine/vendor` modified versions of dependencies. See [vendor/README.md](peregrine/vendor/README.md) for details on the modifications.
* `agda_frontend`
   Contains Agda frontend
* `lean_frontend`
   Contains Lean frontend
* `benchmarks`
   Contains benchmarks for frontends and backends

## Installing/checking
### Agda frontend
Requires GHC (tested with `9.10.1`) and cabal
```
cd agda_frontend
make install
```

To translate Agda code to $\lambda_\square$ use:
```
agda2lambox [AGDAFLAGS] [--out-dir DIR] [--typed] [--no-blocks] FILE
```

### Lean frontend
Requires Lean 4.22.0.
Run `cd lean_frontend && lake build` to build.

To translate Lean code to $\lambda_\square$ use:
```
import LeanToLambdaBox

def val_at_false (f: Bool -> Nat): Nat := f .false

#erase val_at_false to "out.ast"
```

### Peregrine middlend/backends
Requires opam.
```
opam switch create . 4.14.2 --repositories default,coq-released=https://coq.inria.fr/opam/released
eval $(opam env)
opam install ./peregrine/cakeml/rocq-cakeml-extraction.opam ./peregrine/vendor/rocq-typed-extraction/rocq-typed-extraction-common.opam ./peregrine/vendor/rocq-typed-extraction/rocq-rust-extraction.opam ./peregrine/vendor/rocq-typed-extraction/rocq-elm-extraction.opam ./peregrine/vendor/rocq-verified-extraction/rocq-verified-extraction.opam ./peregrine/vendor/certicoq/coq-certicoq.opam ./peregrine/vendor/coq-ceres/coq-ceres.opam ./peregrine/rocq-peregrine.opam
```

To extract $\lambda_\square$ to C, Wasm, OCaml, CakeML, Rust, or Elm use:
```
peregrine TARGETLANGUAGE FILE [-o FILE]
```

Valid values for `TARGETLANGUAGE` are:
* `wasm`
* `c`
* `ocaml`
* `cakeml`
* `rust`
* `elm`
