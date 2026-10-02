import RegretKappa.Corollaries.Expectation
import RegretKappa.CorollariesCheck.Junk
import RegretKappa.CorollariesCheck.Indep42c

/-!
# The third separate formalization of Remark 5.2 (randomized learners on one play): equivalent

`Indep42c` calls it Corollary 4.2, its number in the text it was written from.

Written after the pitfalls of the first round had been pointed out. `Indep42c` models a randomized
learner as a probability space `Ω : Type` with a map `L : Ω → Learner T`, measurable for the
σ-algebra on `Learner T` induced by `Learner.predict`, and its expected regret as
`E (Reg⁺) - E (Reg⁻)`, two lintegrals subtracted in `EReal`.

* Measurability of `L` for that σ-algebra is measurability of every prediction for every fixed
  history (`measurable_learner_iff`), the condition of `IsRandLearner`.
* Under it the regret is measurable, its negative part is at most `∑ y_t ^ 2`, and the two
  expected regrets agree (`expectedRegret_eq`).

So `Indep42c.RandLowerBound` is `RandLowerBound` at universe `0` (`randLowerBound_iff`).
-/

namespace RegretKappa.CorollariesCheck.V42c

open MeasureTheory Filter RegretKappa.Corollaries

attribute [local instance] Indep42c.RandomizedLearner.measurableSpaceΩ
  Indep42c.RandomizedLearner.isProbabilityMeasureμ

theorem measurable_learner_iff {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} (L : Ω → Learner T) :
    Measurable L ↔ ∀ (t : Fin T) (xs : Fin (t + 1) → ℝ) (ys : Fin t → ℝ),
      Measurable fun ω => (L ω).predict t xs ys := by
  rw [measurable_comap_iff]
  simp only [measurable_pi_iff]
  rfl

theorem expectedRegret_eq {T : ℕ} (R : Indep42c.RandomizedLearner T) (x y : Fin T → ℝ) :
    Indep42c.expectedRegret R x y = expRegret R.μ R.L x y := by
  rw [expRegret_eq_pos_sub_neg R.μ R.L x y
    (measurable_regret ((measurable_learner_iff R.L).1 R.measurable_L) x y)]
  rfl

theorem randLowerBound_iff : Indep42c.RandLowerBound ↔ RandLowerBound.{0} := by
  constructor
  · intro h B hB ε hε
    filter_upwards [h B hB ε hε] with T hT
    intro Ω _ μ L hL
    have := hL.1
    obtain ⟨x, y, hy, hc⟩ := hT ⟨Ω, μ, L, (measurable_learner_iff L).2 hL.2⟩
    rw [coe_bound, expectedRegret_eq] at hc
    exact ⟨x, y, hy, hc⟩
  · intro h B hB ε hε
    filter_upwards [h B hB ε hε] with T hT
    intro R
    obtain ⟨x, y, hy, hc⟩ := @hT R.Ω R.measurableSpaceΩ R.μ R.L
      ⟨R.isProbabilityMeasureμ, (measurable_learner_iff R.L).1 R.measurable_L⟩
    rw [← expectedRegret_eq, ← coe_bound] at hc
    exact ⟨x, y, hy, hc⟩

end RegretKappa.CorollariesCheck.V42c
