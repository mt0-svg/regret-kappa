<h1 align="center">The constant of doubly uniform regret in one-dimensional online linear regression is three</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/regret-kappa/releases/latest/download/regret-kappa.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23095139"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23095139.svg"></a>
  <a href="https://mt0-svg.github.io/regret-kappa/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fregret-kappa%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/regret-kappa/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fregret-kappa%2Fbadges%2Fcomparator.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

We consider online linear regression in dimension one when the features are revealed one at a time, with no bound known in advance, and the regret is measured against every linear predictor, with no bound on its parameter. For outcomes bounded by $`B`$ and a horizon $`T\ge355713`$, both known to the learner, the minimax regret lies between $`B^2(3\log T-2\log\log T-15.2)`$ and $`B^2(3\log T+0.37)`$. The upper bound is the regret of an explicit deterministic learner; the lower bound is forced by an explicit randomized adversary, whose features can be taken in $`[0,1]`$. Lean 4 proves both bounds. Chen, Qian, Rakhlin and Zhivotovskiy (COLT 2026) showed that this regret is of order $`\log T`$, which answers a question of Gaillard et al. (ALT 2019); we find its constant, $`3`$. With the features known in advance the constant is $`1`$, so revealing them on the fly triples it.

The order $`\log T`$ is Theorem 5 and Proposition 6 of Chen, Qian, Rakhlin and Zhivotovskiy, *Self-Normalized Martingales and Uniform Regret Bounds for Linear Regression* ([COLT 2026, PMLR 336](https://proceedings.mlr.press/v336/chen26f.html); [arXiv:2605.01628](https://arxiv.org/abs/2605.01628)). The question is in Section 4.1 of Gaillard et al., *Uniform regret bounds over $`\mathbb{R}^d`$ for the sequential linear regression problem with the square loss* ([ALT 2019, PMLR 98](https://proceedings.mlr.press/v98/gaillard19a.html); [arXiv:1805.11386](https://arxiv.org/abs/1805.11386)).

```lean
def RegretKappa.MainTheorem : Prop :=
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, LowerSharp.T0 ≤ T →
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ minimaxRegret T B ∧
      minimaxRegret T B ≤ ((B ^ 2 * (3 * log T + 0.37) : ℝ) : EReal)) ∧
  KappaEqThree

theorem RegretKappa.main : RegretKappa.MainTheorem
theorem RegretKappa.mainBoundedFeatures : RegretKappa.MainBoundedFeatures
theorem RegretKappa.randLowerBound : RegretKappa.Corollaries.RandLowerBound
```

## What is checked

- **Lean 4.** `RegretKappa.main` is Theorem 1.1 with its constants: for every $`B>0`$ and every integer $`T\ge355713`$, $`B^2(3\log T-2\log\log T-15.2)\le\mathrm{Reg}^*_T(B)\le B^2(3\log T+0.37)`$, where $`\mathrm{Reg}^*_T(B)`$ is the minimax regret of deterministic learners, taken in the extended real numbers, and $`\mathrm{Reg}^*_T(B)/(B^2\log T)\to3`$. It follows from `RegretKappa.mainChain`, the same with the bounds $`B^2b(T)`$ of Theorem 4.1 and $`B^2u(T)`$ of Theorem 3.1 in between, and from `RegretKappa.boundU_le`, $`u(T)\le3\log T+0.37`$ for $`T\ge355713`$. Its proof goes through Theorem 3.1, the learner (`RegretKappa.UpperSharp.theoremU` and `theoremULog`), and Theorem 4.1, the adversary (`RegretKappa.LowerSharp.lowerSharpAdv`, `lowerSharpSimplified` and `lowerSharpBound`); it derives the limit from the two bounds of Theorem 1.1 (`RegretKappa.kappaEqThree_squeeze`). `RegretKappa.mainBoundedFeatures` is Corollary 5.1 (features in $`[0,1]`$, outcomes in $`\{-B,0,B\}`$, randomized learners) and `RegretKappa.mainBoundedFeaturesChain` the same with the bounds $`B^2b(T)`$ and $`B^2u(T)`$ of Theorems 4.1 and 3.1. `RegretKappa.randLowerBound` is Remark 5.2, proved from Corollary 5.1. The theorems have no hypothesis and use only the axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, no `native_decide`. Every numerical step is an inequality between rational numbers checked in Lean, and Lean's kernel evaluates the drift certificate of Computation B.2. Without its measurability hypothesis, with the Bochner integral of the regret as the expected regret, Remark 5.2 is false (`RegretKappa.CorollariesCheck.V42b.not_randLowerBound`). Comparator checks the ten theorems of `config.json` against `RegretKappa/Challenge.lean` and `RegretKappa/Challenge/`, copies of the definitions with `sorry` proofs, replays their proofs in the type checker nanoda, and rejects a challenge in which one term of $`b(T)`$ is changed, and one in which the constant $`0.37`$ of the upper bound of `MainTheorem` is changed to $`0.36`$ (`.github/comparator-controls.tsv`).
- **Data.** The subdivisions of the drift certificate of Computation B.2 were written into `RegretKappa/LowerSharp/DriftCells.lean` by a PARI/GP program (`code/drift-cells/`), which the proof does not trust: the kernel checks what it writes.
- **Cited.** The constant $`1`$ for features known in advance is Theorems 4 and 7 of Gaillard et al.; it is not checked here.

[`STATEMENTS.md`](STATEMENTS.md) maps each numbered statement of the paper to its Lean declarations, and Computation B.2 to the program that wrote its data.

`ci.yml` builds the package, fails on any axiom other than these three, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator with its two negative controls. `release.yml` attaches the PDF, the logs of the checks and the build Comparator checked to each release, from the green CI run, without compiling again.

## Layout

| Path                                                                                               | Content                                                                                                                                                                           |
| -------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `RegretKappa/Statement.lean`, `RegretKappa/MainStatement.lean`                                     | the definitions (learners, regret, minimax regret) and the statements of Theorem 1.1 and Corollary 5.1                                                                            |
| `RegretKappa/UpperSharp/`                                                                          | Theorem 3.1: the learner and its constants                                                                                                                                        |
| `RegretKappa/LowerSharp/`                                                                          | Theorem 4.1: the adversary and its constants, with the drift certificate of Computation B.2                                                                                       |
| `RegretKappa/Corollaries/`, `RegretKappa/Main.lean`                                                | randomized learners and bounded features, Corollary 5.1 and Remark 5.2; Theorem 1.1                                                                                               |
| `RegretKappa/Upper/`, `RegretKappa/Lower/`                                                         | definitions and lemmas that `RegretKappa/UpperSharp/` and `RegretKappa/LowerSharp/` build on                                                                                      |
| `RegretKappa/CorollariesCheck/`                                                                    | Remark 5.2 read with the Bochner integral and no measurability, and the proof that it is false                                                                                    |
| `RegretKappa/Challenge.lean`, `RegretKappa/Challenge/`, `RegretKappa/Solution.lean`, `config.json` | the statements with `sorry`, their proofs, and the Comparator configuration                                                                                                       |
| `paper/`                                                                                           | the TeX source and `statement_map.sh`, which writes `STATEMENTS.md`                                                                                                               |
| `code/`                                                                                            | the program that wrote the subdivisions of the drift certificate, and the records of the checks of the formal proof; [`code/README.md`](code/README.md) gives the command of each |

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -rf .lake/build/lib/lean/RegretKappa/Challenge .lake/build/lib/lean/RegretKappa/Challenge.* \
  .lake/build/ir/RegretKappa/Challenge .lake/build/ir/RegretKappa/Challenge.*
# then Comparator, as .github/workflows/ci.yml runs it
```

Full check, from source (a few minutes for the 56 modules of the package on four cores of an AMD Ryzen 9 5900X (12 cores, 24 threads), 64 GB of memory, once Mathlib is built; `code/formal-proof/clean_build.out`):

```sh
lake exe cache get && lake build
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "regret-kappa"
git = "https://github.com/mt0-svg/regret-kappa"
rev = "v1.1.0"
```

then `lake update regret-kappa`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

The program that wrote the subdivisions of the drift certificate: [`code/README.md`](code/README.md) gives its command, which writes `RegretKappa/LowerSharp/DriftCells.lean` again, identical to the shipped file, in under a second (`code/drift-cells/out/drift_cells.txt`).

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export), [nanoda](https://github.com/ammkrn/nanoda_lib) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [PARI/GP](https://pari.math.u-bordeaux.fr/): the program that wrote the subdivisions of the drift certificate.

## Citation

```bibtex
@misc{regret-kappa,
  title     = {The constant of doubly uniform regret in one-dimensional online linear regression is three},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23095139},
  url       = {https://doi.org/10.5281/zenodo.23095139}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/regret-kappa/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
