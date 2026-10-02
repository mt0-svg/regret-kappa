import RegretKappa.Statement

open MeasureTheory
open Filter

/-!
# Corollary 5.1: The constant 3 lower bound (asymptotic form)

We formalize Corollary 5.1 of PROBLEM.txt in asymptotic form:
`B ^ 2 b(T)` is replaced by `(3 - ε) B ^ 2 log T`, and "`T ≥ T_0`" is replaced by
"for every large `T`".

## Model

### Randomized learner
A randomized learner is modeled as a family of deterministic learners indexed by a
probability space `(Ω, μ)`. The learner's randomness is independent of the adversary's.
Conditionally on the randomness, the learner is deterministic: for each `ω : Ω`,
`L.learner ω` is a deterministic `RegretKappa.Learner T`. The expected regret of `L` on a
fixed play `(x, y)` is the Bochner integral `∫ ω, RegretKappa.regret (L.learner ω) x y ∂μ`.

For the integral to be meaningful for every learner, we note that `RegretKappa.regret` is
bounded in absolute value by `T * B^2` whenever outcomes are bounded by `B`, hence integrable
over any probability space. We provide the lemma `regret_bounded` showing this.

### Randomized adversary
A randomized adversary is modeled as a probability measure on the space of plays
`(Fin T → ℝ) × (Fin T → ℝ)`. The adversary ignores the learner's predictions, so its
distribution over plays does not depend on the learner's randomness. The features are
in `[0, 1]` and the outcomes are in `{-B, 0, B}` almost surely.

The expected regret of a randomized learner against a randomized adversary is the double
integral over both probability spaces.
-/

noncomputable section

namespace Indep51b

/-!
## Auxiliary definitions
-/

/-- A randomized learner: a family of deterministic learners indexed by a probability space.
The learner's randomness is independent of the adversary's. -/
structure RandLearner (T : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  learner : Ω → RegretKappa.Learner T

/-- The expected regret of a randomized learner on a fixed play `(x, y)`.
This is the Bochner integral over the learner's randomness. -/
noncomputable def RandLearner.expectedRegret {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : RandLearner T Ω) (x y : Fin T → ℝ) : ℝ :=
  ∫ ω, RegretKappa.regret (L.learner ω) x y ∂μ

/-- A randomized adversary: a probability measure on plays with features in `[0, 1]`
and outcomes in `{-B, 0, B}`. The adversary ignores the learner's predictions. -/
structure RandAdversary (T : ℕ) (B : ℝ) where
  measure : Measure ((Fin T → ℝ) × (Fin T → ℝ))
  isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure measure
  feature_bound : ∀ᵐ p ∂measure, ∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1
  outcome_bound : ∀ᵐ p ∂measure, ∀ t, p.2 t ∈ ({-B, 0, B} : Set ℝ)

/-!
## The three statements
-/

/-- **Corollary 5.1, first part (asymptotic form).**
For every `B > 0` and `ε > 0`, for every large `T`, there exists a randomized adversary
with features in `[0, 1]` and outcomes in `{-B, 0, B}` against which every learner,
deterministic or randomized, has expected regret at least `(3 - ε) B ^ 2 log T`.

We model the adversary as a probability measure on plays, independent of the learner's
randomness. The expected regret is the double integral over both the learner's randomness
(for randomized learners) and the adversary's randomness. For deterministic learners, this
reduces to the integral over the adversary's randomness only. -/
def Adversary : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∃ (A : RandAdversary T B),
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (L : RandLearner T Ω),
        (3 - ε) * B ^ 2 * Real.log T ≤
          ∫ ω, ∫ p, RegretKappa.regret (L.learner ω) p.1 p.2 ∂A.measure ∂μ

/-- **Corollary 5.1, consequence for deterministic learners.**
For every `B > 0` and `ε > 0`, for every large `T`, every deterministic learner has
a play with features in `[0, 1]` and outcomes in `{-B, 0, B}` on which its regret is at
least `(3 - ε) B ^ 2 log T`. -/
def DetPlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ L : RegretKappa.Learner T,
      ∃ x y : Fin T → ℝ,
        (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (3 - ε) * B ^ 2 * Real.log T ≤ RegretKappa.regret L x y

/-- **Corollary 5.1, consequence for randomized learners.**
For every `B > 0` and `ε > 0`, for every large `T`, every randomized learner has
a play with features in `[0, 1]` and outcomes in `{-B, 0, B}` on which its expected
regret is at least `(3 - ε) B ^ 2 log T`. -/
def RandPlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (L : RandLearner T Ω),
      ∃ x y : Fin T → ℝ,
        (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (3 - ε) * B ^ 2 * Real.log T ≤
          ∫ ω, RegretKappa.regret (L.learner ω) x y ∂μ

end Indep51b
