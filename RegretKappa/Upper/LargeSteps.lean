import RegretKappa.Upper.Gamma

/-!
# Upper bound: large steps, `b² ≥ 3/4`

The paper, Lemma 3.11, with a cruder constant: with `c = √(1 - b²) ≤ 1/2`, either
`|ρ| c + |b| ≤ |ρ|` (then the step does not move up the potential), or `|ρ| < √3` and
`|ρ| c + |b| ≤ √(ρ² + 1) < 2` by Cauchy-Schwarz; so `G(ρ c ± b) ≤ G ρ + G 2`.
-/

namespace RegretKappa.Upper

open Real

theorem large_geom {ρ b : ℝ} (hρ : 0 ≤ ρ) (hb1 : 3 / 4 ≤ b ^ 2) (hb2 : b ^ 2 ≤ 1) :
    ρ * √(1 - b ^ 2) + |b| ≤ ρ ∨ ρ * √(1 - b ^ 2) + |b| ≤ 2 := by
  set c := √(1 - b ^ 2) with hc_def
  have hc_sq : c ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by linarith)
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have h_sq_sum : c ^ 2 + b ^ 2 = 1 := by linarith
  have habs_sq : |b| ^ 2 = b ^ 2 := sq_abs b
  have hb_abs_nonneg : 0 ≤ |b| := abs_nonneg _
  by_cases h : ρ * c + |b| ≤ ρ
  · left; exact h
  · right
    have h_lt : ρ < ρ * c + |b| := by linarith
    have h_mul : ρ * (1 - c) < |b| := by linarith
    have hc_le_half : c ≤ 1/2 := by
      have hc_sq_le : c ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
        rw [hc_sq]
        linarith
      nlinarith
    have h_one_plus_c_pos : 0 < 1 + c := by linarith
    have h_mul2 : ρ * b ^ 2 < |b| * (1 + c) := by
      have h_eq : (1 - c) * (1 + c) = b ^ 2 := by
        nlinarith
      calc
        ρ * b ^ 2 = ρ * ((1 - c) * (1 + c)) := by rw [h_eq]
        _ = (ρ * (1 - c)) * (1 + c) := by ring
        _ < |b| * (1 + c) := mul_lt_mul_of_pos_right h_mul h_one_plus_c_pos
    have h_rho_sq_lt_three : ρ ^ 2 < 3 := by
      by_cases hb_abs_pos : |b| > 0
      · have h_rho_abs_nonneg : 0 ≤ ρ * |b| := mul_nonneg hρ hb_abs_nonneg
        have h_rho_abs_lt : ρ * |b| < 1 + c := by
          have htemp : ρ * (|b| ^ 2) < |b| * (1 + c) := by
            rw [habs_sq]; exact h_mul2
          have htemp2 : |b| * (ρ * |b|) < |b| * (1 + c) := by
            calc
              |b| * (ρ * |b|) = ρ * (|b| * |b|) := by ring
              _ = ρ * (|b| ^ 2) := by ring
              _ < |b| * (1 + c) := htemp
          exact lt_of_mul_lt_mul_left htemp2 hb_abs_nonneg
        have h_rho_abs_lt_three_half : ρ * |b| < 3/2 := by
          linarith
        have h_sq_lt : (ρ * |b|) ^ 2 < (9/4 : ℝ) := by
          nlinarith
        have h_rho_sq_abs_sq_lt : ρ ^ 2 * (|b| ^ 2) < 9/4 := by
          nlinarith
        have h_abs_sq_ge : 3/4 ≤ |b| ^ 2 := by
          rw [habs_sq]
          exact hb1
        nlinarith
      · have hb_abs_zero : |b| = 0 := by linarith
        have hb_sq_zero : b ^ 2 = 0 := by
          rw [← habs_sq, hb_abs_zero]
          simp
        linarith
    have h_key : (ρ * c + |b|) ^ 2 ≤ ρ ^ 2 + 1 := by
      have h_nonneg : 0 ≤ (ρ * |b| - c) ^ 2 := pow_two_nonneg _
      have h_eq : (ρ * c + |b|) ^ 2 + (ρ * |b| - c) ^ 2 = ρ ^ 2 + 1 := by
        nlinarith
      linarith
    have h_final_sq_lt_four : (ρ * c + |b|) ^ 2 < 4 := by
      nlinarith
    have h_nonneg_sum : 0 ≤ ρ * c + |b| := by
      nlinarith
    nlinarith

theorem large_step (ρ : ℝ) {b : ℝ} (hb1 : 3 / 4 ≤ b ^ 2) (hb2 : b ^ 2 ≤ 1) :
    max (G (ρ * √(1 - b ^ 2) + b)) (G (ρ * √(1 - b ^ 2) - b)) ≤ G ρ + G 2 := by
  set c := √(1 - b ^ 2) with hc
  have hc_nonneg : 0 ≤ c := by
    rw [hc]
    exact Real.sqrt_nonneg _
  set m := |ρ| * c + |b| with hm
  have hm_nonneg : 0 ≤ m := by
    rw [hm]
    have hρ := abs_nonneg ρ
    have hb := abs_nonneg b
    nlinarith
  have h1 : |ρ * c + b| ≤ m := by
    calc
      |ρ * c + b| ≤ |ρ * c| + |b| := abs_add_le _ _
      _ = |ρ| * |c| + |b| := by rw [abs_mul]
      _ = |ρ| * c + |b| := by rw [abs_of_nonneg hc_nonneg]
      _ = m := by rw [hm]
  have h2 : |ρ * c - b| ≤ m := by
    calc
      |ρ * c - b| ≤ |ρ * c| + |-b| := abs_add_le _ _
      _ = |ρ| * |c| + |b| := by rw [abs_mul, abs_neg]
      _ = |ρ| * c + |b| := by rw [abs_of_nonneg hc_nonneg]
      _ = m := by rw [hm]
  have hG1 : G (ρ * c + b) ≤ G m := by
    apply G_mono
    calc
      |ρ * c + b| ≤ m := h1
      _ = |m| := by rw [abs_of_nonneg hm_nonneg]
  have hG2 : G (ρ * c - b) ≤ G m := by
    apply G_mono
    calc
      |ρ * c - b| ≤ m := h2
      _ = |m| := by rw [abs_of_nonneg hm_nonneg]
  have hmax : max (G (ρ * c + b)) (G (ρ * c - b)) ≤ G m :=
    max_le hG1 hG2
  have hGm_le : G m ≤ G ρ + G 2 := by
    have hlarge := large_geom (abs_nonneg ρ) hb1 hb2
    rcases hlarge with (hm_le_rho | hm_le_2)
    · -- case m ≤ |ρ|
      have hGm : G m ≤ G (|ρ|) := by
        apply G_mono
        -- need |m| ≤ |(|ρ|)|, i.e. m ≤ |ρ| (since m ≥ 0, |ρ| ≥ 0)
        simpa [abs_of_nonneg hm_nonneg, abs_of_nonneg (abs_nonneg ρ)] using hm_le_rho
      have hGrho : G (|ρ|) = G ρ := G_abs ρ
      have hGrho_le : G ρ ≤ G ρ + G 2 := by
        have h := G_nonneg 2
        nlinarith
      calc
        G m ≤ G (|ρ|) := hGm
        _ = G ρ := hGrho
        _ ≤ G ρ + G 2 := hGrho_le
    · -- case m ≤ 2
      have hGm : G m ≤ G 2 := by
        apply G_mono
        -- need |m| ≤ |2|, i.e. m ≤ 2 (since m ≥ 0, 2 ≥ 0)
        simpa [abs_of_nonneg hm_nonneg, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using hm_le_2
      have hG2_le : G 2 ≤ G ρ + G 2 := by
        have h := G_nonneg ρ
        nlinarith
      calc
        G m ≤ G 2 := hGm
        _ ≤ G ρ + G 2 := hG2_le
  calc
    max (G (ρ * √(1 - b ^ 2) + b)) (G (ρ * √(1 - b ^ 2) - b)) = max (G (ρ * c + b)) (G (ρ * c - b)) := by
      simp [hc]
    _ ≤ G m := hmax
    _ ≤ G ρ + G 2 := hGm_le

end RegretKappa.Upper
