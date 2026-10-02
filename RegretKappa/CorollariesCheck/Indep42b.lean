import RegretKappa.Statement

open Filter Topology
open MeasureTheory
open RegretKappa

namespace Indep42b

/-!
# Corollary 4.2 for randomized learners (asymptotic form)

Restricted to adversaries that play a fixed pair of sequences `(x, y)` (each such pair is
an adaptive adversary that ignores the predictions), in asymptotic form:
`B^2 b(T)` is replaced by `(3 - ε) B^2 log T`, and "for every `T ≥ T_0`" by
"for every `ε > 0`, for every large `T`".

We model a randomized learner as a probability space `Ω` and a measurable map from `Ω` to
deterministic learners (`RegretKappa.Learner T`).  Conditionally on the realized `ω`, the learner
is deterministic.  The expected regret on a play `(x, y)` is the Bochner integral of the regret
over `Ω` with respect to the probability measure.
-/

/-- A randomized learner for horizon `T`.
It consists of a probability space `Ω` and a map from `Ω` to deterministic learners.
The randomness is independent of the adversary's; conditionally on `ω`, the learner is deterministic.
The map `learner` need not be measurable; the Bochner integral is defined as `0` for non-measurable
functions, which is a valid real number in Mathlib. -/
structure RandLearner (T : ℕ) where
  Ω : Type
  [hΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [hμ : IsProbabilityMeasure μ]
  learner : Ω → Learner T

/-- The expected regret of a randomized learner on a play `(x, y)`.
This is the Bochner integral of the regret over the learner's internal randomness `ω`.
Since the regret is real-valued, the integral is defined as a real number
(and equals `0` for non-integrable functions, by the Mathlib convention for the Bochner integral). -/
noncomputable def RandLearner.expectedRegret {T : ℕ} (L : RandLearner T) (x y : Fin T → ℝ) : ℝ :=
  ∫ ω, regret (L.learner ω) x y ∂(L.μ)

/-- The randomized lower bound (Corollary 4.2, asymptotic form).
For every `B > 0` and `ε > 0`, for every sufficiently large horizon `T`,
every randomized learner has a play `(x, y)` with `|y t| ≤ B` for all `t`
on which its expected regret is at least `(3 - ε) B ^ 2 log T`. -/
def RandLowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ L : RandLearner T, ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧
      (3 - ε) * B ^ 2 * Real.log (T : ℝ) ≤ L.expectedRegret x y

/-- The expected regret equals the Bochner integral by definition. -/
lemma expectedRegret_eq_integral {T : ℕ} (L : RandLearner T) (x y : Fin T → ℝ) :
    L.expectedRegret x y = ∫ ω, regret (L.learner ω) x y ∂(L.μ) := rfl

end Indep42b
