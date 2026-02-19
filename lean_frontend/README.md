# lean_to_lambdabox
An implementation of type and proof erasure from Lean's term language (represented in Lean by the type `Expr`) into the untyped lambda-calculus $\lambda_\square$ (LambdaBox),
using the same syntax as the [`peregrine` tool](../peregrine/).

## Usage
```
import Erasure

def val_at_false (f: Bool -> Nat): Nat := f .false

#erase val_at_false to "out.ast"
```

Elaborating the above Lean code will produce a file `out.ast`
containing $\lambda_\square$ code for the function `val_at_false`.
This can then be converted to Malfunction code
using the `peregrine` tool,
compiled to a `.cmx` object file with the Malfunction compiler,
and linked with other OCaml object files using `ocamlopt`,
following the same steps as Rocq's verified extraction pipeline.

For more details on these postprocessing steps, see the [benchmarks README](benchmarks/README.md).
