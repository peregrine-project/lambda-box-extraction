## Organization
### Benchmarks
Short benchmarks programs are defined in [`FromLeanCommon.lean`](FromLeanCommon.lean),
and more substantial benchmarks,
based on the paper Counting Immutable Beans by Ullrich and de Moura,
are in the directory [`FromLeanCommon`](FromLeanCommon).

The file [`TESTS`](TESTS) contains information about the benchmark programs for use by the Makefiles.
The format for each line is is `<name>:<runner>[:<count>]`, where `<runner>` can be
- `runonce`, for programs of type `Unit -> Unit`: creates an executable which runs the program once and exits.
- `repeat`, for programs of type `Unit -> Unit`:
  creates an executable which takes one command-line argument `n`, runs the program `n` times, and exits.
- `natio`, for programs of type `Nat -> Nat`:
  creates an executable which takes one command-line argument `n`, runs the program with the input value `n`, and prints the result to standard output.
For benchmarks which are to be compiled and run using the `repeat` or `natio` runners,
the corresponding entry in `TESTS` also contains `<count>`,
which is a reasonable value of `n` for which execution takes around 0.1s-1s.

### Backends
The `lean` backend simply compiles the benchmark programs using Lean's compiler; this is handled in the directory [`via_lean`](via_lean).

The various `malfunction-*` backends (see [Makefile](Makefile) for the full list) are various
configurations of the pipeline for erasure to $\lambda_\square$,
extraction to Malfunction,
compilation to a `.cmx` files
and linking into an executable;
these steps are handled in the directory `via_malfunction` by [the Makefile there](via_malfunction/Makefile).
See the [README](via_malfunction/README.md) for information about how to configure OPAM and install dependencies as well as an overview of the available parameters for the Malfunction pipeline.

## Building individual programs
`make bin/<backend>/<benchmark>`

Example: `make bin/malfunction-reference/binarytrees`.

## Running benchmarks
The Make target `wide` will build and run the full suite of all benchmarks × backends.
This uses the [`hyperfine` tool](https://github.com/sharkdp/hyperfine).
Results will be placed as a JSON document in the directory [`results/wide`](results/wide),
and can be visualized as a table using the script `wide_viz.py`.

### CPU isolation
To reduce noise added by the OS scheduler, the measurements given in the report
were performed on a Linux system booted with the parameter `isolcpus=1,3`,
isolating the logical processors 1 and 3
(which form a hyperthreading pair on the processor used).
This stops the kernel from automatically scheduling execution of processes on these CPUs,
which allows the benchmark executables to be executed without interruption.
The `wide` Make target prefixes the `hyperfine` invocations with `taskset -c 3`
in order to ensure that the benchmarked executables are run on the isolated CPU 3.

Instead of using the [deprecated `isolcpus` parameter](https://www.kernel.org/doc/html/latest/admin-guide/kernel-parameters.html#:~:text=Isolate,disturbance), 
it should also be possible to isolate CPUs using cpusets.
If isolating a CPU other than CPU 3, adapt the `taskset` invocations in the [Makefile](Makefile) accordingly.
The call to `taskset` may be removed if not bothering with CPU isolation, but this is not necessary.

In addition to CPU isolation,
a number of other CPU settings may be modified
(see the scripts [`setup.sh`](setup.sh), [`status.sh`](status.sh) and [`unsetup.sh`](unsetup.sh) for inspiration),
but these were found to not further reduce noise on the hardware tested
(one laptop from 2017, so your mileage may vary).
