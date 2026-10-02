import RegretKappa.CorollariesCheck.Indep51u
import RegretKappa.Corollaries.Statement

/-!
# The separate formalization of the constant over bounded features: identical

`Indep51u` was written from the wording "for every `B > 0`, the minimax regret over the plays with
features in `[0, 1]` and outcomes in `{-B, 0, B}`, divided by `B ^ 2 log T`, tends to `3`", with
its two halves. Its four definitions are ours, by definition (`minimaxBF_eq`, `kappaBF_iff`,
`upperBF_iff`, `lowerBF_iff`).
-/

namespace RegretKappa.CorollariesCheck.V51u

theorem minimaxBF_eq (T : ℕ) (B : ℝ) :
    Indep51u.minimaxBF T B = Corollaries.minimaxRegretBF T B := rfl

theorem kappaBF_iff : Indep51u.KappaBF ↔ Corollaries.KappaEqThreeBF := Iff.rfl

theorem upperBF_iff : Indep51u.UpperBF ↔ Corollaries.BoundedFeaturesUpper := Iff.rfl

theorem lowerBF_iff : Indep51u.LowerBF ↔ Corollaries.BoundedFeatures := Iff.rfl

end RegretKappa.CorollariesCheck.V51u
