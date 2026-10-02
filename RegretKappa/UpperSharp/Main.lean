import RegretKappa.UpperSharp.Assembly

/-!
# Theorem 3.1 with the paper's constants: the two targets

The proofs of the targets of `RegretKappa/UpperSharp/Statement.lean`. `theoremU` is
`Regret_T ≤ Φ_T(0)` (`regret_leU`, `PhiU_T_zero`). For `theoremULog` (the paper, proof of
Theorem 3.1), with `X = 3T^{3/2}/√(2π)`, the argument of the logarithm is at most
`X (1 + T^{-1/2})(1 + Γ(0)/(3T))(1 + e²/X)` (`arg_le`), `2 log X = 3 log T + 2 log(3/√(2π))`
(`log_X_eq`), `log(1 + a) ≤ a` three times, `4e^{-1/2}/3 ≤ 0.81` and `2√(2π)e²/3 ≤ 12.35`
(`const_c_le`).
-/

namespace RegretKappa.UpperSharp

open Real

theorem exp_two_lt : exp 2 < 7.3890561 := by
  have hsq : exp 2 = (exp 1) ^ 2 := by
    calc
      exp 2 = exp (1 + 1) := by norm_num
      _ = exp 1 * exp 1 := by rw [Real.exp_add 1 1]
      _ = (exp 1) ^ 2 := by ring
  rw [hsq]
  have hpos : 0 < exp 1 := Real.exp_pos 1
  have hsq_bound : (2.7182818286 : ℝ) ^ 2 < 7.3890561 := by norm_num
  nlinarith [Real.exp_one_lt_d9, hpos]

theorem const_c_le : 2 * √(2 * π) * exp 2 / 3 ≤ 12.35 := by
  rcases sqrt_two_pi_bounds with ⟨_, h_sqrt⟩
  have h_sqrt_nonneg : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  have h_exp_nonneg : 0 ≤ exp 2 := by linarith [Real.exp_pos 2]
  have h_mul : √(2 * π) * exp 2 ≤ (2.506629 : ℝ) * (7.3890561 : ℝ) :=
    mul_le_mul h_sqrt (le_of_lt exp_two_lt) h_exp_nonneg (by norm_num : (0 : ℝ) ≤ 2.506629)
  have h_bound : 2 * √(2 * π) * exp 2 / 3 ≤ 2 * (2.506629 : ℝ) * (7.3890561 : ℝ) / 3 := by
    nlinarith
  have h_arith : 2 * (2.506629 : ℝ) * (7.3890561 : ℝ) / 3 ≤ 12.35 := by
    norm_num
  exact le_trans h_bound h_arith

theorem log_X_eq {T : ℝ} (hT : 0 < T) :
    2 * log (3 * T * √T / √(2 * π)) = 3 * log T + 2 * log (3 / √(2 * π)) := by
  have hT' : T ≠ 0 := by linarith
  have h_sqrt_T_pos : √T > 0 := Real.sqrt_pos.mpr hT
  have h_sqrt_T_ne_zero : √T ≠ 0 := by linarith
  have h_2pi_pos : 0 < 2 * π := by nlinarith [Real.pi_pos]
  have h_sqrt_2pi_pos : √(2 * π) > 0 := Real.sqrt_pos.mpr h_2pi_pos
  have h_sqrt_2pi_ne_zero : √(2 * π) ≠ 0 := by linarith
  calc
    2 * log (3 * T * √T / √(2 * π))
        = 2 * (log (3 * T * √T) - log (√(2 * π))) := by
          rw [Real.log_div (by nlinarith) (by nlinarith)]
    _ = 2 * (log (3 * T) + log (√T) - log (√(2 * π))) := by
          rw [Real.log_mul (by nlinarith) (by nlinarith)]
    _ = 2 * ((log 3 + log T) + log (√T) - log (√(2 * π))) := by
          rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hT']
    _ = 2 * ((log 3 + log T) + (log T / 2) - log (√(2 * π))) := by
          rw [Real.log_sqrt (by linarith : 0 ≤ T)]
    _ = 2 * (log 3 + log T + (log T / 2) - log (√(2 * π))) := by ring
    _ = 2 * log 3 + 2 * log T + log T - 2 * log (√(2 * π)) := by ring
    _ = 3 * log T + 2 * log 3 - 2 * log (√(2 * π)) := by ring
    _ = 3 * log T + 2 * (log 3 - log (√(2 * π))) := by ring
    _ = 3 * log T + 2 * log (3 / √(2 * π)) := by
          rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) h_sqrt_2pi_ne_zero]

theorem arg_le {T E : ℝ} (hT : 1 ≤ T) (hE : 0 ≤ E) :
    exp 2 + (√T + 1) * (3 * T + 2 * E) / √(2 * π) ≤
      3 * T * √T / √(2 * π) *
        ((1 + 1 / √T) * (1 + 2 * E / (3 * T)) * (1 + exp 2 / (3 * T * √T / √(2 * π)))) := by
  have hT_pos : 0 < T := by linarith
  have hr_pos : 0 < √T := Real.sqrt_pos.mpr hT_pos
  have hq_pos : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity : 0 < 2 * π)
  have hX_pos : 0 < 3 * T * √T / √(2 * π) := by positivity
  set X := 3 * T * √T / √(2 * π) with hX_def
  set a := 1 / √T with ha_def
  set b := 2 * E / (3 * T) with hb_def
  set c := exp 2 / X with hc_def
  set R := X * (1 + a) * (1 + b) with hR_def
  have ha_nonneg : 0 ≤ a := div_nonneg (by norm_num) (by linarith)
  have hb_nonneg : 0 ≤ b := div_nonneg (by linarith) (by nlinarith)
  have hc_nonneg : 0 ≤ c := div_nonneg (by positivity) (by linarith)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have h_main_id : R = (√T + 1) * (3 * T + 2 * E) / √(2 * π) := by
    dsimp [R, X, a, b]
    field_simp [hr_pos.ne.symm, hT_pos.ne.symm, hq_pos.ne.symm]
  have h_Rc_eq : R * c = (1 + a) * (1 + b) * exp 2 := by
    dsimp [R, c, X]
    field_simp [hX_pos.ne.symm]
  have h_prod_ge_one : 1 ≤ (1 + a) * (1 + b) := by
    nlinarith
  have h_ineq : exp 2 ≤ R * c := by
    rw [h_Rc_eq]
    have h_exp_pos : 0 < exp 2 := Real.exp_pos 2
    nlinarith
  calc
    exp 2 + (√T + 1) * (3 * T + 2 * E) / √(2 * π)
        = exp 2 + R := by rw [h_main_id]
    _ ≤ R + R * c := by nlinarith
    _ = R * (1 + c) := by ring
    _ = (X * (1 + a) * (1 + b)) * (1 + c) := by rw [hR_def]
    _ = X * (1 + a) * (1 + b) * (1 + c) := by ring
    _ = 3 * T * √T / √(2 * π) *
        ((1 + 1 / √T) * (1 + 2 * E / (3 * T)) * (1 + exp 2 / (3 * T * √T / √(2 * π)))) := by
      dsimp [X, a, b, c]
      ring

theorem ulog_bound {T : ℝ} (hT : 1 ≤ T) :
    2 * log (exp 2 + (√T + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π)) ≤
      3 * log T + 2 * log (3 / √(2 * π)) + 2 / √T + 0.81 / T + 12.35 / (T * √T) := by
  have hTpos : 0 < T := by linarith
  have hsqrtTpos : 0 < √T := by positivity
  have hEpos : 0 < exp (-1 / 2) := Real.exp_pos _
  have hE : 0 ≤ exp (-1 / 2) := le_of_lt hEpos
  have hpos_exp2 : 0 < exp 2 := Real.exp_pos 2
  have hpos_sqrt2pi : 0 < √(2 * π) := by positivity
  set E := exp (-1 / 2) with hEdef
  set X := 3 * T * √T / √(2 * π) with hXdef
  set a := 1 / √T with hadef
  set b := 2 * E / (3 * T) with hbdef
  set c := exp 2 / X with hcdef
  have hpos_LHS : 0 < exp 2 + (√T + 1) * (3 * T + 2 * E) / √(2 * π) := by
    positivity
  have hpos_X : 0 < X := by
    dsimp [X]
    positivity
  have hpos_1a : 0 < 1 + a := by
    dsimp [a]
    positivity
  have hpos_1b : 0 < 1 + b := by
    dsimp [b, E]
    positivity
  have hpos_1c : 0 < 1 + c := by
    dsimp [c, X]
    positivity
  have h_arg := arg_le hT hE
  have h_log_arg_le_log_prod : log (exp 2 + (√T + 1) * (3 * T + 2 * E) / √(2 * π)) ≤
      log (X * ((1 + a) * (1 + b) * (1 + c))) :=
    Real.log_le_log hpos_LHS h_arg
  have h_log_prod_eq : log (X * ((1 + a) * (1 + b) * (1 + c))) =
      log X + log (1 + a) + log (1 + b) + log (1 + c) := by
    have hprod_pos : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
    have hprod_ne_zero : (1 + a) * (1 + b) * (1 + c) ≠ 0 := by linarith
    have hprod23_pos : 0 < (1 + b) * (1 + c) := by positivity
    have hprod23_ne_zero : (1 + b) * (1 + c) ≠ 0 := by linarith
    calc
      log (X * ((1 + a) * (1 + b) * (1 + c))) = log X + log ((1 + a) * (1 + b) * (1 + c)) :=
        Real.log_mul (ne_of_gt hpos_X) hprod_ne_zero
      _ = log X + log ((1 + a) * ((1 + b) * (1 + c))) := by rw [mul_assoc]
      _ = log X + (log (1 + a) + log ((1 + b) * (1 + c))) := by
        rw [Real.log_mul (ne_of_gt hpos_1a) hprod23_ne_zero]
      _ = log X + log (1 + a) + log ((1 + b) * (1 + c)) := by ring
      _ = log X + log (1 + a) + (log (1 + b) + log (1 + c)) := by
        rw [Real.log_mul (ne_of_gt hpos_1b) (ne_of_gt hpos_1c)]
      _ = log X + log (1 + a) + log (1 + b) + log (1 + c) := by ring
  have h_log_1a_le_a : log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos hpos_1a
    linarith
  have h_log_1b_le_b : log (1 + b) ≤ b := by
    have := Real.log_le_sub_one_of_pos hpos_1b
    linarith
  have h_log_1c_le_c : log (1 + c) ≤ c := by
    have := Real.log_le_sub_one_of_pos hpos_1c
    linarith
  have h_log_prod_le : log (X * ((1 + a) * (1 + b) * (1 + c))) ≤ log X + a + b + c := by
    linarith
  have h_main : 2 * log (exp 2 + (√T + 1) * (3 * T + 2 * E) / √(2 * π)) ≤ 2 * log X + 2 * a + 2 * b + 2 * c := by
    nlinarith
  have h_logX_eq : 2 * log X = 3 * log T + 2 * log (3 / √(2 * π)) := by
    dsimp [X]
    exact log_X_eq hTpos
  have h_2a : 2 * a = 2 / √T := by
    dsimp [a]
    ring
  have h_2b_le : 2 * b ≤ 0.81 / T := by
    dsimp [b, E]
    have hEbound := exp_neg_half_bounds
    rcases hEbound with ⟨_, hEup⟩
    have h_4E3_le_081 : 4 * exp (-1 / 2) / 3 ≤ 0.81 := by
      have hcalc : 4 * (0.6065306598 : ℝ) / 3 ≤ 0.81 := by norm_num
      linarith
    calc
      2 * (2 * exp (-1 / 2) / (3 * T)) = (4 * exp (-1 / 2) / 3) / T := by ring
      _ ≤ 0.81 / T := (div_le_div_iff_of_pos_right hTpos).mpr h_4E3_le_081
  have h_2c_le : 2 * c ≤ 12.35 / (T * √T) := by
    dsimp [c, X]
    have hc_le := const_c_le
    have hpos_T_sqrtT : 0 < T * √T := by positivity
    calc
      2 * (exp 2 / (3 * T * √T / √(2 * π))) = (2 * √(2 * π) * exp 2 / 3) / (T * √T) := by
        field_simp
      _ ≤ 12.35 / (T * √T) := (div_le_div_iff_of_pos_right hpos_T_sqrtT).mpr hc_le
  calc
    2 * log (exp 2 + (√T + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))
        ≤ 2 * log X + 2 * a + 2 * b + 2 * c := h_main
    _ = (3 * log T + 2 * log (3 / √(2 * π))) + 2 / √T + 2 * b + 2 * c := by rw [h_logX_eq, h_2a]
    _ ≤ (3 * log T + 2 * log (3 / √(2 * π))) + 2 / √T + 0.81 / T + 2 * c := by nlinarith
    _ ≤ (3 * log T + 2 * log (3 / √(2 * π))) + 2 / √T + 0.81 / T + 12.35 / (T * √T) := by nlinarith

/-- **The paper, Theorem 3.1**, first form. -/
theorem theoremU : TheoremU := by
  intro T x y hy
  rw [← PhiU_T_zero]
  exact regret_leU x y hy

/-- **The paper, Theorem 3.1**, second form. -/
theorem theoremULog : TheoremULog := by
  intro T hT x y hy
  exact (theoremU T x y hy).trans (ulog_bound (by exact_mod_cast hT))

end RegretKappa.UpperSharp
