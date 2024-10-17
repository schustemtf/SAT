# BabySAT DPLL SAT Solver Template

This is a template for a DPLL SAT solver.  It does not work yet.
Your task is to first change the LICENSE and add your name there
and in addition get it working.

For that you need to implement are the following:

 - adding clauses (`add_clause`)
 - assigning literals (`assign`)
 - propagation of literals (`propagate`)
 - figuring out when your formula is satisfied (`satisfied`)
 - variable section heuristics (`decide`)
 - unassigning literals (`unassign`)
 - backtracking (`backtrack`)
 - the DPLL code (`dpll`)

Afterwards remove this text.

To compile run `./configure && make` for optimized compilation and
`./configure --debug && make` if you want to include symbols and disable
assertion checking.  See `./configure -l` for more options.

The code is supposed to be kept formatted with `clang-format` for which
you need to install it first and then issue `make format`.

There are regression tests included and `make test` should eventually pass.

- `babysat`         : the executable binary after compilation.
- `babysat.cpp`     : the self-contained actual C++ solver code.
- `cnfs`            : test files in DIMACS format and test runner `test/run.sh`.
- `config.hpp`      : generated by `generate` to capture build information.
- `configure`       : the `configure` script generates `makefile`.
- `generate`        : the `generate` script generates `config.hpp`.
- `LICENSE`         : the license file (currently MIT license).
- `makefile`        : the actual makefile generated from `makefile.in`.
- `makefile.in`     : the makefile template instantiated to `makefile`.
- `README.md`       : this overview file.
- `VERSION`         : the version number.
