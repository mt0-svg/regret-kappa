# Code

The two PARI/GP programs of the release, and the records of the checks of the formal proof. The proof does not trust the first program: the Lean kernel checks what it writes. No proof uses the second: it evaluates the instance printed after Theorem 1.1.

## Directories

| Directory       | Content | Run | Time |
| --------------- | ------- | --- | ---- |
| `drift-cells/`  | `drift_cells.gp` writes `RegretKappa/LowerSharp/DriftCells.lean`: the move table of Section 4.2 and, for each of its 28 cells, the subdivision of the drift certificate of Computation B.2, from the bisection trees of `drift_tree_lib.gp`, in exact rational arithmetic (written with PARI/GP 2.17.4; CI runs it again with 2.17.2) | `cd drift-cells && gp -q drift_cells.gp < /dev/null`, which writes the shipped module again, byte for byte (`out/drift_cells.txt`) | under a second |
| `instance/`     | `bounds.gp` evaluates at $`T=10^6`$ the two bounds of Theorem 1.1 and the bounds $`b(T)`$ of Theorem 4.1 and $`u(T)`$ of Theorem 3.1, in floating point with 100 significant digits, the lower bounds rounded down and the upper bounds up to two decimals | `cd instance && gp -q bounds.gp < /dev/null`, which prints `out/bounds.txt` | under a second |
| `formal-proof/` | a clean build of the Lean package (`clean_build.out`), the axioms of the theorems of `config.json` (`main_axioms.out`), and a Comparator run with nanoda (`comparator.out`) | `bash formal-proof/clean_build.sh` | 12 min, Mathlib built; Comparator 4 min |
