import RegretKappa.Statement

/-!
# Upper bound: the regret identity

The regret identity and the bound `|ρ_t| ≤ √t`. With the closed form of the loss of the best
linear predictor,
`∑ y² - bestLinearLoss = (S/√V)²`, and `bestLinearLoss` scales by `B²` with the outcomes.
-/

namespace RegretKappa.Upper

open Finset

theorem linearLoss_expand {T : ℕ} (θ : ℝ) (x y : Fin T → ℝ) :
    linearLoss θ x y = θ ^ 2 * ∑ t, x t ^ 2 - 2 * θ * ∑ t, x t * y t + ∑ t, y t ^ 2 := by
  unfold linearLoss
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The regret identity: the infimum over `θ` in closed form. -/
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

/-- `∑ y² - bestLinearLoss = (S/√V)²` (both sides vanish when `V = 0`). -/
theorem sum_sq_sub_bestLinearLoss {T : ℕ} (x y : Fin T → ℝ) :
    ∑ t, y t ^ 2 - bestLinearLoss x y = ((∑ t, x t * y t) / √(∑ t, x t ^ 2)) ^ 2 := by
  rw [bestLinearLoss_closed]
  split_ifs with h
  · rw [h, Real.sqrt_zero, div_zero]
    ring
  · rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun t _ => sq_nonneg (x t))]
    ring

/-- The loss of the best linear predictor scales by `B²` with the outcomes. -/
theorem bestLinearLoss_mul {T : ℕ} (x y : Fin T → ℝ) (B : ℝ) :
    bestLinearLoss x (fun t => B * y t) = B ^ 2 * bestLinearLoss x y := by
  rw [bestLinearLoss_closed, bestLinearLoss_closed]
  have h1 : ∑ t, (B * y t) ^ 2 = B ^ 2 * ∑ t, y t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have h2 : ∑ t, x t * (B * y t) = B * ∑ t, x t * y t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  split_ifs with h
  · exact h1
  · rw [h1, h2]
    ring

/-- Cauchy-Schwarz for outcomes in `[-1, 1]`: `S_n² ≤ n V_n`. -/
theorem sq_sum_mul_le (X Y : ℕ → ℝ) (hY : ∀ i, |Y i| ≤ 1) (n : ℕ) :
    (∑ i ∈ range n, X i * Y i) ^ 2 ≤ n * ∑ i ∈ range n, X i ^ 2 := by
  have hY2 : ∑ i ∈ range n, Y i ^ 2 ≤ n := by
    have := Finset.sum_le_sum (s := range n) fun i _ => (sq_le_one_iff_abs_le_one (Y i)).2 (hY i)
    simpa using this
  calc (∑ i ∈ range n, X i * Y i) ^ 2 ≤ (∑ i ∈ range n, X i ^ 2) * ∑ i ∈ range n, Y i ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i ∈ range n, X i ^ 2) * n :=
        mul_le_mul_of_nonneg_left hY2 (Finset.sum_nonneg fun i _ => sq_nonneg (X i))
    _ = n * ∑ i ∈ range n, X i ^ 2 := mul_comm _ _

end RegretKappa.Upper
