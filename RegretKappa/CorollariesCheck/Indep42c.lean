import RegretKappa.Statement

/-!
# Corollary 4.2 for randomized learners

Restricted to fixed pairs of sequences `(x, y)` (adaptive adversaries that ignore predictions),
asymptotic form: `B^2 b(T)` replaced by `(3 - ε) B^2 log T`, and `"for every T ≥ T_0"` by
`"for every ε > 0, for every large T"`.

We model a randomized learner as a probability space `Ω` and a measurable map `L : Ω → Learner T`
(`conditionally on the randomness, the learner is deterministic`). The expected regret is the
`EReal`-valued integral of the regret over `Ω`, defined as the difference of the positive and
negative parts via `ENNReal` lintegrals. This avoids the junk-value issues of the Bochner
integral (which returns 0 for non-integrable functions) and of `lintegral` (which drops the
negative part).
-/

namespace Indep42c

open MeasureTheory
open Set
open Filter

/-! ## Measurable space on `Learner T` -/

instance {T : ℕ} : MeasurableSpace (RegretKappa.Learner T) :=
  MeasurableSpace.comap RegretKappa.Learner.predict inferInstance

/-! ## Randomized learner -/

/-- A randomized learner for horizon `T`: a probability space `Ω` and a measurable map
`L : Ω → Learner T`. Conditionally on `ω`, the learner is deterministic (`L ω`). -/
structure RandomizedLearner (T : ℕ) where
  Ω : Type
  [measurableSpaceΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [isProbabilityMeasureμ : IsProbabilityMeasure μ]
  L : Ω → RegretKappa.Learner T
  measurable_L : Measurable L

/-! ## Expected regret -/

/-- The expected regret of a randomized learner on a play `(x, y)`.
Defined as the `EReal`-valued integral:
`E[regret] = ∫⁻ max(regret, 0) dμ - ∫⁻ max(-regret, 0) dμ`.
This equals the true expectation whenever the regret is integrable, and is otherwise
`⊤`, `⊥`, or `0` (when both parts are infinite) -- all well-defined `EReal` values
with no junk in the integrable case. -/
noncomputable def expectedRegret {T : ℕ} (R : RandomizedLearner T) (x y : Fin T → ℝ) : EReal :=
  let pos := ∫⁻ ω, ENNReal.ofReal (RegretKappa.regret (R.L ω) x y) ∂(R.μ)
  let neg := ∫⁻ ω, ENNReal.ofReal (-RegretKappa.regret (R.L ω) x y) ∂(R.μ)
  (pos : EReal) - (neg : EReal)

/-! ## Sanity-check lemmas -/

section SanityCheck

variable {T : ℕ} (R : RandomizedLearner T) (x y : Fin T → ℝ)

/-- If the regret is nonnegative everywhere, the expected regret is nonnegative. -/
lemma expectedRegret_nonneg_of_nonneg (h_regret : ∀ ω, 0 ≤ RegretKappa.regret (R.L ω) x y) :
    0 ≤ expectedRegret R x y := by
  dsimp [expectedRegret]
  have h_pos : 0 ≤ (∫⁻ ω, ENNReal.ofReal (RegretKappa.regret (R.L ω) x y) ∂(R.μ) : EReal) := by
    exact_mod_cast zero_le
  have h_neg : (∫⁻ ω, ENNReal.ofReal (-RegretKappa.regret (R.L ω) x y) ∂(R.μ) : EReal) = 0 := by
    have hzero : ∀ ω, ENNReal.ofReal (-RegretKappa.regret (R.L ω) x y) = ENNReal.ofReal (0 : ℝ) := by
      intro ω; simp [h_regret ω]
    rw [lintegral_congr hzero]
    simp
  rw [h_neg, sub_zero]
  exact h_pos

/-- If the regret is zero everywhere, the expected regret is zero. -/
lemma expectedRegret_zero_of_regret_zero (h_regret : ∀ ω, RegretKappa.regret (R.L ω) x y = 0) :
    expectedRegret R x y = 0 := by
  dsimp [expectedRegret]
  have hzero : ∀ ω, ENNReal.ofReal (RegretKappa.regret (R.L ω) x y) = ENNReal.ofReal (0 : ℝ) := by
    intro ω; simp [h_regret ω]
  rw [lintegral_congr hzero]
  have hzero2 : ∀ ω, ENNReal.ofReal (-RegretKappa.regret (R.L ω) x y) = ENNReal.ofReal (0 : ℝ) := by
    intro ω; simp [h_regret ω]
  rw [lintegral_congr hzero2]
  simp

/-- If the measure is zero, the expected regret is zero. -/
lemma expectedRegret_zero_of_measure_zero (hμ : R.μ = 0) : expectedRegret R x y = 0 := by
  dsimp [expectedRegret]
  rw [hμ]
  simp

end SanityCheck

/-! ## Asymptotic lower bound for randomized learners -/

/-- **Corollary 4.2 for randomized learners, asymptotic form.**
For every `B > 0` and `ε > 0`, for every sufficiently large horizon `T`,
every randomized learner has a play `(x, y)` with `|y t| ≤ B` for all `t` on which its
expected regret is at least `(3 - ε) B ^ 2 log T`. -/
def RandLowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (R : RandomizedLearner T),
      ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ (3 - ε) * B ^ 2 * Real.log T ≤ expectedRegret R x y

end Indep42c
