import RegretKappa.UpperSharp.Main
import RegretKappa.Corollaries.Transfer
import RegretKappa.Corollaries.Statement

/-!
# The explicit upper half over bounded features

The learner of `RegretKappa.UpperSharp`, run on the outcomes divided by `B` with its predictions
multiplied by `B` (`Lower.rescale (learnerU T) B⁻¹`), has regret `B ^ 2` times that of
`learnerU T` on outcomes in `[-1, 1]` (`regret_rescale_inv`), so at most `B ^ 2 U(T)` on every
play with `|y t| ≤ B` and any real features (`regret_rescale_learnerU_le`, the paper, Theorem 3.1,
last sentence). In particular this holds on the plays with features in `[0, 1]` and outcomes in
`[-B, B]` (`boundedFeaturesUpperUI`) or in `{-B, 0, B}` (`boundedFeaturesUpperU`).
-/

namespace RegretKappa.Corollaries

open Real RegretKappa.Lower

/-- **The paper, Theorem 3.1, last sentence.** The learner of `UpperSharp` rescaled to outcomes in
`[-B, B]` has regret at most `B ^ 2 U(T)` on every play with `|y t| ≤ B`. -/
theorem regret_rescale_learnerU_le {B : ℝ} (hB : 0 < B) (T : ℕ) (x y : Fin T → ℝ)
    (hy : ∀ t, |y t| ≤ B) :
    regret (rescale (UpperSharp.learnerU T) B⁻¹) x y ≤
      B ^ 2 * (2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))) := by
  rw [regret_rescale_inv _ hB.ne']
  have h1 : ∀ t, |y t / B| ≤ 1 := fun t => by
    rw [abs_div, abs_of_pos hB, div_le_one hB]
    exact hy t
  exact mul_le_mul_of_nonneg_left (UpperSharp.theoremU T x _ h1) (sq_nonneg B)

/-- **The explicit upper half over bounded features, outcomes in `[-B, B]`.** -/
theorem boundedFeaturesUpperUI : BoundedFeaturesUpperUI := by
  intro B hB T
  refine iInf_le_of_le (rescale (UpperSharp.learnerU T) B⁻¹) (iSup₂_le fun x y => ?_)
  exact iSup₂_le fun _ hy => EReal.coe_le_coe_iff.2 (regret_rescale_learnerU_le hB T x y hy)

/-- **The explicit upper half over bounded features, outcomes in `{-B, 0, B}`.** -/
theorem boundedFeaturesUpperU : BoundedFeaturesUpperU := fun B hB T =>
  (minimaxRegretBF_le_BFI T hB).trans (boundedFeaturesUpperUI B hB T)

end RegretKappa.Corollaries
