import RegretKappa.Statement

/-!
# Rescaling the features

For `M ≠ 0`, the learner `scaleX M L` divides the features by `M` before it passes them to `L`.
Its regret on a play `(x, y)` is the regret of `L` on `(x / M, y)` (`regret_scaleX`): the
predictions agree, and the best linear loss does not change when the features are divided by `M`
(`bestLinearLoss_div`, by the substitution `θ ↦ θ M`). This is the rescaling step of the paper's
proof of Corollary 5.1.
-/

namespace RegretKappa.Corollaries

/-- The learner that divides the features by `M` and then predicts as `L`. -/
noncomputable def scaleX {T : ℕ} (M : ℝ) (L : Learner T) : Learner T :=
  ⟨fun t xs ys => L.predict t (fun s => xs s / M) ys⟩

/-- Dividing the features by `M ≠ 0` does not change the best linear loss. -/
theorem bestLinearLoss_div {T : ℕ} (x y : Fin T → ℝ) {M : ℝ} (hM : M ≠ 0) :
    bestLinearLoss (fun t => x t / M) y = bestLinearLoss x y := by
  apply le_antisymm
  · refine le_bestLinearLoss x y fun θ => ?_
    refine (bestLinearLoss_le (fun t => x t / M) y (θ * M)).trans_eq ?_
    unfold linearLoss
    refine Finset.sum_congr rfl fun t _ => ?_
    field_simp [hM]
  · refine le_bestLinearLoss (fun t => x t / M) y fun θ => ?_
    refine (bestLinearLoss_le x y (θ / M)).trans_eq ?_
    unfold linearLoss
    refine Finset.sum_congr rfl fun t _ => ?_
    field_simp [hM]

/-- The regret of `L` on the play with the features divided by `M ≠ 0` is the regret of
`scaleX M L` on the play. -/
theorem regret_scaleX {T : ℕ} (L : Learner T) {M : ℝ} (hM : M ≠ 0) (x y : Fin T → ℝ) :
    regret L (fun t => x t / M) y = regret (scaleX M L) x y := by
  unfold regret
  have h_learner : learnerLoss (scaleX M L) x y = learnerLoss L (fun t => x t / M) y := by
    unfold learnerLoss Learner.prediction scaleX
    simp
  have h_best : bestLinearLoss (fun t => x t / M) y = bestLinearLoss x y := by
    apply le_antisymm
    · refine le_bestLinearLoss x y fun θ => ?_
      calc
        bestLinearLoss (fun t => x t / M) y ≤ linearLoss (θ * M) (fun t => x t / M) y :=
          bestLinearLoss_le _ _ _
        _ = linearLoss θ x y := by
          unfold linearLoss
          refine Finset.sum_congr rfl fun t _ => ?_
          field_simp [hM]
    · refine le_bestLinearLoss (fun t => x t / M) y fun θ => ?_
      calc
        bestLinearLoss x y ≤ linearLoss (θ / M) x y := bestLinearLoss_le _ _ _
        _ = linearLoss θ (fun t => x t / M) y := by
          unfold linearLoss
          refine Finset.sum_congr rfl fun t _ => ?_
          field_simp [hM]
  calc
    regret L (fun t => x t / M) y = learnerLoss L (fun t => x t / M) y - bestLinearLoss (fun t => x t / M) y := rfl
    _ = learnerLoss (scaleX M L) x y - bestLinearLoss x y := by rw [h_learner, h_best]
    _ = regret (scaleX M L) x y := rfl

end RegretKappa.Corollaries
