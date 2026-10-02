import RegretKappa.Upper.Gamma

/-!
# Upper bound: terminal condition

The paper, Lemma 3.12, with a cruder constant: `Φ₀(ρ) ≥ ρ²` for `ρ² ≤ T`, where
`Φ₀(ρ) = 2 log(C (λ₀ + G ρ))`, `C = 4 (√T + 1)`, `λ₀ = 2 / C`. For `|ρ| ≤ 1` the level `C λ₀ = 2`
suffices; for `|ρ| ≥ 1` the window bound `G |ρ| ≥ e^{ρ²/2 - 1/2} / (2 (|ρ| + 1))` does.
-/

namespace RegretKappa.Upper

open Real

theorem Cst_pos (T : ℕ) : 0 < Cst T := by
  unfold Cst
  positivity

theorem lam0_pos (T : ℕ) : 0 < lam0 T := by
  unfold lam0
  exact div_pos two_pos (Cst_pos T)

theorem terminal {T : ℕ} {ρ : ℝ} (hρ : ρ ^ 2 ≤ T) : ρ ^ 2 ≤ 2 * log (Cst T * (lam0 T + G ρ)) := by
  have hCst_pos : 0 < Cst T := Cst_pos T
  have hCst_nonneg : 0 ≤ Cst T := by linarith
  have hG_nonneg : 0 ≤ G ρ := G_nonneg ρ
  -- exp(1/2) ≤ 2
  have hexp_half_le_two : Real.exp (1/2 : ℝ) ≤ 2 := by
    have hsq : Real.exp (1/2 : ℝ) ^ 2 = Real.exp 1 := by
      calc
        Real.exp (1/2 : ℝ) ^ 2 = Real.exp (1/2 : ℝ) * Real.exp (1/2 : ℝ) := by ring
        _ = Real.exp ((1/2 : ℝ) + (1/2 : ℝ)) := by rw [Real.exp_add]
        _ = Real.exp 1 := by norm_num
    by_contra! hgt
    have hsq_gt : Real.exp (1/2 : ℝ) ^ 2 > 4 := by nlinarith
    rw [hsq] at hsq_gt
    linarith [Real.exp_one_lt_three, hsq_gt]
  -- Identity: Cst T * (lam0 T + G ρ) = 2 + Cst T * G ρ
  have hCst_ne : Cst T ≠ 0 := by linarith
  have h_eq : Cst T * (lam0 T + G ρ) = 2 + Cst T * G ρ := by
    dsimp [lam0]
    calc
      Cst T * (2 / Cst T + G ρ) = Cst T * (2 / Cst T) + Cst T * G ρ := by ring
      _ = 2 + Cst T * G ρ := by field_simp [hCst_ne]
  -- Main inequality: exp(ρ²/2) ≤ 2 + Cst T * G ρ
  have h_main : Real.exp (ρ ^ 2 / 2) ≤ 2 + Cst T * G ρ := by
    by_cases h_abs_le : |ρ| ≤ 1
    · -- Case 1: |ρ| ≤ 1
      rcases abs_le.mp h_abs_le with ⟨h_left, h_right⟩
      have h_rho_sq_le_one : ρ ^ 2 ≤ 1 := by nlinarith
      have h_exp_le : Real.exp (ρ ^ 2 / 2) ≤ Real.exp (1/2 : ℝ) := by
        apply Real.exp_le_exp_of_le
        nlinarith
      have h_nonneg_prod : 0 ≤ Cst T * G ρ := by nlinarith
      nlinarith
    · -- Case 2: |ρ| ≥ 1
      have h_one_le_abs : 1 ≤ |ρ| := by linarith
      have h_abs_le_sqrt : |ρ| ≤ √(T : ℝ) := Real.abs_le_sqrt hρ
      have h_Cst_ge : 4 * (|ρ| + 1) ≤ Cst T := by
        dsimp [Cst]
        nlinarith
      have h_G_lower : Real.exp (|ρ| ^ 2 / 2 - 1 / 2) / (2 * (|ρ| + 1)) ≤ G |ρ| :=
        G_lower h_one_le_abs
      have h_G_abs : G |ρ| = G ρ := G_abs ρ
      rw [h_G_abs] at h_G_lower
      have h_sq_abs : |ρ| ^ 2 = ρ ^ 2 := sq_abs ρ
      rw [h_sq_abs] at h_G_lower
      have h_prod_ge : Real.exp (ρ ^ 2 / 2) ≤ Cst T * G ρ := by
        have h_init : Real.exp (ρ ^ 2 / 2) ≤ 2 * Real.exp (ρ ^ 2 / 2 - 1 / 2) := by
          calc
            Real.exp (ρ ^ 2 / 2) = Real.exp ((ρ ^ 2 / 2 - 1 / 2) + (1/2 : ℝ)) := by ring_nf
            _ = Real.exp (ρ ^ 2 / 2 - 1 / 2) * Real.exp (1/2 : ℝ) := by rw [Real.exp_add]
            _ ≤ Real.exp (ρ ^ 2 / 2 - 1 / 2) * 2 := by
              apply mul_le_mul_of_nonneg_left hexp_half_le_two
              positivity
            _ = 2 * Real.exp (ρ ^ 2 / 2 - 1 / 2) := by ring
        have h_mid : 2 * Real.exp (ρ ^ 2 / 2 - 1 / 2) ≤ Cst T * G ρ := by
          have h_eq2 : 2 * Real.exp (ρ ^ 2 / 2 - 1 / 2) =
              (4 * (|ρ| + 1)) * (Real.exp (ρ ^ 2 / 2 - 1 / 2) / (2 * (|ρ| + 1))) := by
            field_simp [show |ρ| + 1 ≠ 0 from by
              have h_abs_nonneg : 0 ≤ |ρ| := abs_nonneg _
              nlinarith]
            ring
          rw [h_eq2]
          have h_Cst_mul : (4 * (|ρ| + 1)) * (Real.exp (ρ ^ 2 / 2 - 1 / 2) / (2 * (|ρ| + 1))) ≤
              Cst T * (Real.exp (ρ ^ 2 / 2 - 1 / 2) / (2 * (|ρ| + 1))) := by
            have h_div_nonneg : 0 ≤ Real.exp (ρ ^ 2 / 2 - 1 / 2) / (2 * (|ρ| + 1)) := by
              positivity
            nlinarith
          have h_mul_G : Cst T * (Real.exp (ρ ^ 2 / 2 - 1 / 2) / (2 * (|ρ| + 1))) ≤ Cst T * G ρ := by
            apply mul_le_mul_of_nonneg_left h_G_lower
            exact hCst_nonneg
          linarith
        linarith
      nlinarith
  -- Convert to log inequality: ρ²/2 ≤ log(2 + Cst T * G ρ)
  have hpos_sum : 0 < 2 + Cst T * G ρ := by nlinarith
  have h_log : ρ ^ 2 / 2 ≤ Real.log (2 + Cst T * G ρ) :=
    (Real.le_log_iff_exp_le hpos_sum).mpr h_main
  -- Multiply by 2 to get the goal
  rw [h_eq]
  linarith

end RegretKappa.Upper
