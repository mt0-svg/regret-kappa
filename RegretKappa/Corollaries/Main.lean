import RegretKappa.Corollaries.Mixture
import RegretKappa.Upper.Assembly
import RegretKappa.Corollaries.UpperU
import RegretKappa.Kappa
import RegretKappa.Corollaries.Explicit

/-!
# Corollary 5.1 and Remark 5.2

The targets of `RegretKappa/Corollaries/Statement.lean`. `boundedFeaturesAdv`
(`RegretKappa/Corollaries/Mixture.lean`) is the main theorem; the others follow from it.
`boundedFeaturesRand_of_adv`: against a randomized learner, the expected regret against a finite
mixture of plays is the weighted sum of its expected regrets on the plays (`advRegret_eq_sum`, which
needs the measurability of `IsRandLearner`), so some play does at least as well as the mixture
(`exists_le_of_le_sum`). The upper half over bounded features is `Upper.upperBound`, which holds
for every real feature, and with `boundedFeatures` it gives the constant `3` over bounded features
(`kappaEqThreeBF`). Over features in `[0, 1]` and outcomes in `[-B, B]` the minimax regret lies
between that over `{-B, 0, B}` and that over all plays, so it has the constant `3` too
(`kappaEqThreeBFI`). The explicit upper halves are in `RegretKappa/Corollaries/UpperU.lean`; the
transfer of an explicit lower bound against a finite family of plays is
`boundedFeatures_of_mixture` (`RegretKappa/Corollaries/Explicit.lean`).
-/

namespace RegretKappa.Corollaries

universe u

/-- The adversary form implies the play form: against a randomized learner, some play of the
adversary does at least as well as the adversary. -/
theorem boundedFeaturesRand_of_adv (h : BoundedFeaturesAdv.{u}) : BoundedFeaturesRand.{u} := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  intro Ω _ μ L hL
  obtain ⟨ι, _, w, x, y, hw, hs, hx, hy, hadv⟩ := hT
  have hc := hadv Ω μ L hL
  rw [advRegret_eq_sum μ hL.2] at hc
  obtain ⟨i, hi⟩ := exists_le_of_le_sum w hw hs _ _ _ hc
  exact ⟨x i, y i, hx i, hy i, hi⟩

/-- **The paper, Corollary 5.1, randomized learners.** -/
theorem boundedFeaturesRand : BoundedFeaturesRand.{u} :=
  boundedFeaturesRand_of_adv boundedFeaturesAdv

/-- **The paper, Corollary 5.1, deterministic learners.** -/
theorem boundedFeatures : BoundedFeatures :=
  boundedFeatures_of_rand boundedFeaturesRand

/-- **The upper half over bounded features.** The learner of `Upper` has regret at most
`(3 + ε) B ^ 2 log T` on every play with `|y t| ≤ B`, whatever the features. -/
theorem boundedFeaturesUpper : BoundedFeaturesUpper :=
  boundedFeaturesUpper_of_upperBound Upper.upperBound

/-- **The constant over bounded features.** For every `B > 0`, the minimax regret over the plays
with features in `[0, 1]` and outcomes in `{-B, 0, B}`, divided by `B ^ 2 log T`, tends to `3`. -/
theorem kappaEqThreeBF : KappaEqThreeBF :=
  kappaEqThreeBF_of_bounds boundedFeaturesUpper boundedFeatures

/-- **The constant over bounded features, outcomes in `[-B, B]`.** For every `B > 0`, the minimax
regret over the plays with features in `[0, 1]` and outcomes in `[-B, B]`, divided by
`B ^ 2 log T`, tends to `3`. -/
theorem kappaEqThreeBFI : KappaEqThreeBFI :=
  kappaEqThreeBFI_of kappaEqThreeBF kappaEqThree

/-- **The paper, Remark 5.2, randomized learners on one play.** -/
theorem randLowerBound : RandLowerBound.{u} :=
  randLowerBound_of_rand boundedFeaturesRand

end RegretKappa.Corollaries
