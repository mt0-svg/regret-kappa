import RegretKappa.Statement

/-!
# Lower bound: the regret identity, rescaling, causality

The paper, Lemma 2.2. The closed form of the loss of the best linear predictor is the
one of `RegretKappa.StatementCheck.bestLinearLoss_eq` (StatementCheck/Equiv2.lean), proved again
here (same proof) so that the lower bound imports only the target statement. With Lean's
`a / 0 = 0` the closed form reads `∑ y² - S² / V` in both cases, and the regret is
`∑ (ŷ² - 2 ŷ y) + S² / V`.

Also: the regret scales by `B²` when the outcomes and the learner are rescaled by `B`
(`regret_rescale`), which reduces the lower bound to `B = 1`; and a prediction depends only on the
features up to its round and the outcomes before it (`prediction_congr`).
-/

namespace RegretKappa.Lower

open Finset

theorem linearLoss_expand {T : ℕ} (θ : ℝ) (x y : Fin T → ℝ) :
    linearLoss θ x y = θ ^ 2 * ∑ t, x t ^ 2 - 2 * θ * ∑ t, x t * y t + ∑ t, y t ^ 2 := by
  unfold linearLoss
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The paper, Lemma 2.2: the infimum over `θ` in closed form. -/
theorem bestLinearLoss_closed {T : ℕ} (x y : Fin T → ℝ) :
    bestLinearLoss x y =
      if ∑ t, x t ^ 2 = 0 then ∑ t, y t ^ 2
      else ∑ t, y t ^ 2 - (∑ t, x t * y t) ^ 2 / ∑ t, x t ^ 2 := by
  split_ifs with h
  · have hx : ∀ t, x t = 0 := fun t =>
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i)).1 h t (Finset.mem_univ t))
    have hc : ∀ θ : ℝ, linearLoss θ x y = ∑ t, y t ^ 2 := fun θ => by
      unfold linearLoss
      simp [hx]
    unfold bestLinearLoss
    simp_rw [hc]
    exact ciInf_const
  · have hV : 0 < ∑ t, x t ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun t _ => sq_nonneg _) (Ne.symm h)
    refine le_antisymm ?_ (le_bestLinearLoss x y fun θ => ?_)
    · refine (bestLinearLoss_le x y ((∑ t, x t * y t) / ∑ t, x t ^ 2)).trans_eq ?_
      rw [linearLoss_expand]
      field_simp
      ring
    · rw [linearLoss_expand]
      have hsq : θ ^ 2 * ∑ t, x t ^ 2 - 2 * θ * ∑ t, x t * y t + ∑ t, y t ^ 2 -
          (∑ t, y t ^ 2 - (∑ t, x t * y t) ^ 2 / ∑ t, x t ^ 2) =
          (∑ t, x t ^ 2) * (θ - (∑ t, x t * y t) / ∑ t, x t ^ 2) ^ 2 := by
        field_simp
        ring
      nlinarith [mul_nonneg hV.le (sq_nonneg (θ - (∑ t, x t * y t) / ∑ t, x t ^ 2))]

/-- The closed form in one line: `bestLinearLoss = ∑ y² - S² / V` (with `S² / 0 = 0`). -/
theorem bestLinearLoss_eq_sub {T : ℕ} (x y : Fin T → ℝ) :
    bestLinearLoss x y = ∑ t, y t ^ 2 - (∑ t, x t * y t) ^ 2 / ∑ t, x t ^ 2 := by
  rw [bestLinearLoss_closed]
  split_ifs with h
  · rw [h, div_zero, sub_zero]
  · rfl

-- TARGET

/-- The paper, Lemma 2.2: `Regret = ∑ (ŷ² - 2 ŷ y) + S² / V`. -/
theorem regret_eq {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) :
    regret L x y = ∑ t, (L.prediction x y t ^ 2 - 2 * L.prediction x y t * y t) +
      (∑ t, x t * y t) ^ 2 / ∑ t, x t ^ 2 := by
  unfold regret learnerLoss
  rw [bestLinearLoss_eq_sub x y]
  have h : ∀ a b : ℝ, (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
    intro a b; ring
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The learner `L` run on outcomes multiplied by `B`, its predictions divided by `B`. -/
noncomputable def rescale {T : ℕ} (L : Learner T) (B : ℝ) : Learner T :=
  ⟨fun t xs ys => L.predict t xs (fun s => B * ys s) / B⟩

-- TARGET

/-- Rescaling the outcomes by `B ≠ 0` multiplies the regret by `B²`. -/
theorem regret_rescale {T : ℕ} (L : Learner T) {B : ℝ} (hB : B ≠ 0) (x y : Fin T → ℝ) :
    regret L x (fun t => B * y t) = B ^ 2 * regret (rescale L B) x y := by
  have hpred (t : Fin T) : (rescale L B).prediction x y t = L.prediction x (fun s => B * y s) t / B := by
    unfold rescale Learner.prediction
    simp
  have hlearner : learnerLoss L x (fun t => B * y t) = B ^ 2 * learnerLoss (rescale L B) x y := by
    unfold learnerLoss
    calc
      ∑ t : Fin T, (L.prediction x (fun t => B * y t) t - B * y t) ^ 2
          = ∑ t : Fin T, B ^ 2 * ((L.prediction x (fun s => B * y s) t / B) - y t) ^ 2 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        field_simp [hB]
      _ = B ^ 2 * ∑ t : Fin T, ((L.prediction x (fun s => B * y s) t / B) - y t) ^ 2 := by
        simp [Finset.mul_sum]
      _ = B ^ 2 * ∑ t : Fin T, ((rescale L B).prediction x y t - y t) ^ 2 := by
        simp [hpred]
      _ = B ^ 2 * learnerLoss (rescale L B) x y := rfl
  have hbest : bestLinearLoss x (fun t => B * y t) = B ^ 2 * bestLinearLoss x y := by
    rw [bestLinearLoss_closed x (fun t => B * y t), bestLinearLoss_closed x y]
    by_cases hV : ∑ t : Fin T, x t ^ 2 = 0
    · simp [hV, mul_pow, Finset.mul_sum]
    · simp [hV]
      have hsum1 : ∑ t : Fin T, (B * y t) ^ 2 = B ^ 2 * ∑ t : Fin T, y t ^ 2 := by
        simp [mul_pow, Finset.mul_sum]
      have hsum2 : ∑ t : Fin T, x t * (B * y t) = B * ∑ t : Fin T, x t * y t := by
        simp [Finset.mul_sum, mul_left_comm]
      simp [hsum1, hsum2]
      ring
  unfold regret
  rw [hlearner, hbest]
  ring

/-- Causality: the prediction in round `t` depends only on the features up to round `t` and the
outcomes before round `t`. -/
theorem prediction_congr {T : ℕ} (L : Learner T) {x x' y y' : Fin T → ℝ} (t : Fin T)
    (hx : ∀ s : Fin T, s ≤ t → x s = x' s) (hy : ∀ s : Fin T, s < t → y s = y' s) :
    L.prediction x y t = L.prediction x' y' t := by
  unfold Learner.prediction
  congr 1
  · funext s
    exact hx _ (Fin.le_iff_val_le_val.2 (by simp; omega))
  · funext s
    exact hy _ (Fin.lt_def.2 (by simp))

end RegretKappa.Lower
