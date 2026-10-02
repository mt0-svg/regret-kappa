import RegretKappa.LowerSharp.Hitting
import RegretKappa.LowerSharp.Statement

/-!
# Sharp lower bound: the side conditions and the simplified forms

The paper, Lemma 4.3 and the end of the proof of Theorem 4.1, for every integer `T ≥ T₀`:

* (C1) `L ≥ 14.5` (`level_ge`), with the actual `j₀` rather than the paper's `L_low`: `j₀ = 4` on
  `T₀ ≤ T < e^{e⁴/3}`, where `L ≥ 2 log(T₀ / (80 e)) ≥ 14.8`, and where `j₀ = J ≥ 5`,
  `L > 2 e^{J-1}/3 - 2 log(20 e J) ≥ 25`;
* (C2) `j₀ (8.8 e e^{L/2} + 1) ≤ T₁ - 1` (`C2`), since `8.8 e e^{L/2} j₀ = 0.44 T`;
* (C3) `π² e² (a₊ + 2)² ≤ k₀` (`C3`);
* `B₀ ≥ 3 log T - log log T - 2 log(log log T + 2.1) - 13.6` (`B0_ge`), `b(T) ≥ B₀ - 1`
  (`bT_ge`) and `3 log T - 2 log log T - 15.2 ≤ 3 log T - log log T - 2 log(log log T + 2.1) - 14.6`
  (`simplified_two`).
-/

namespace RegretKappa.LowerSharp

open Real

/-- `B₀ = L + log(k₀/(√L + 2)²) - c₁ - log k₀/(2 k₀) - 1/k₀`, so that `b(T) = (1 - e^{-j₀}) B₀`. -/
noncomputable def B0 (T : ℕ) : ℝ :=
  level T + log (k0 T / (√(level T) + 2) ^ 2) - c1 - log (k0 T) / (2 * k0 T) - 1 / k0 T

theorem bT_eq_B0 (T : ℕ) : bT T = (1 - exp (-(j0 T : ℝ))) * B0 T := rfl

theorem j0_pos {T : ℕ} (hT : T0 ≤ T) : 1 ≤ j0 T := by
  unfold j0 T0 at *
  -- hT : 355713 ≤ T
  have hTpos : (0 : ℝ) < T := by
    have : (355713 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have hexp1_lt_T : Real.exp 1 < (T : ℝ) := by
    have h_exp_lt : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h_355713_le : (355713 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have h_lt : (2.7182818286 : ℝ) < (355713 : ℝ) := by norm_num
    linarith
  have h_one_lt_logT : (1 : ℝ) < Real.log (T : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) hexp1_lt_T
    -- h : Real.log (Real.exp 1) < Real.log (T : ℝ)
    -- Real.log (Real.exp 1) = 1
    simpa [Real.log_exp] using h
  have h_one_lt_three_logT : (1 : ℝ) < 3 * Real.log (T : ℝ) := by
    nlinarith
  have h_log_pos : 0 < Real.log (3 * Real.log (T : ℝ)) :=
    Real.log_pos h_one_lt_three_logT
  have h_ceil_pos : 0 < ⌈Real.log (3 * Real.log (T : ℝ))⌉₊ :=
    (Nat.ceil_pos (a := Real.log (3 * Real.log (T : ℝ)))).mpr h_log_pos
  exact Nat.succ_le_of_lt h_ceil_pos

theorem exp_33_4_le : exp (33 / 4) ≤ 4446 := by
  have h_exp_add : exp (33/4) = exp 1 ^ 8 * exp (1/4) := by
    calc
      exp (33/4) = exp ((8 : ℝ) + (1/4)) := by ring_nf
      _ = exp (8 : ℝ) * exp (1/4) := by rw [Real.exp_add]
      _ = exp ((8 : ℕ) * (1 : ℝ)) * exp (1/4) := by norm_num
      _ = (exp 1) ^ (8 : ℕ) * exp (1/4) := by rw [Real.exp_nat_mul]
      _ = exp 1 ^ 8 * exp (1/4) := by norm_num
  rw [h_exp_add]
  have h_exp1_lt : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp1_pos : 0 < exp 1 := Real.exp_pos 1
  have h_exp1_nonneg : 0 ≤ exp 1 := h_exp1_pos.le
  have h_pow8 : exp 1 ^ 8 < 2981 := by
    have h_base : exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by
      refine pow_lt_pow_left₀ h_exp1_lt h_exp1_nonneg (by norm_num : (8 : ℕ) ≠ 0)
    have h_bound : (2.7182818286 : ℝ) ^ 8 < 2981 := by norm_num
    linarith
  have h_exp_quarter_nonneg : 0 ≤ exp (1/4) := by positivity
  have h_13_nonneg : 0 ≤ (1.3 : ℝ) := by norm_num
  have h_exp_quarter_pow4 : exp (1/4) ^ 4 = exp 1 := by
    calc
      exp (1/4) ^ 4 = exp ((4 : ℕ) * (1/4)) := by
        rw [← Real.exp_nat_mul (1/4) 4]
      _ = exp 1 := by norm_num
  have h_exp_quarter_le_13 : exp (1/4) ≤ 1.3 := by
    have h_pow4_lt : exp (1/4) ^ 4 < (1.3 : ℝ) ^ 4 := by
      rw [h_exp_quarter_pow4]
      have h_lt_272 : exp 1 < (2.72 : ℝ) := by linarith
      have h_272_lt : (2.72 : ℝ) < (1.3 : ℝ) ^ 4 := by norm_num
      linarith
    have h_lt : exp (1/4) < 1.3 :=
      ((pow_lt_pow_iff_left₀ h_exp_quarter_nonneg h_13_nonneg (by norm_num : (4 : ℕ) ≠ 0)).mp h_pow4_lt)
    exact h_lt.le
  have h_product : exp 1 ^ 8 * exp (1/4) ≤ 2981 * (1.3 : ℝ) := by
    nlinarith
  have h_final : 2981 * (1.3 : ℝ) ≤ 4446 := by norm_num
  linarith

theorem five_case {J : ℕ} (hJ : 5 ≤ J) :
    29 / 2 + 2 * log (20 * exp 1 * J) ≤ 2 / 3 * exp ((J : ℝ) - 1) := by
  -- convert J to ℝ
  have hj5 : (5 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hjpos : 0 < (J : ℝ) := by linarith
  -- Step 1: log(20 * e * J) ≤ J + 3
  have hlog : log (20 * exp 1 * (J : ℝ)) ≤ (J : ℝ) + 3 := by
    have h20pos : (20 : ℝ) ≠ 0 := by norm_num
    have he1pos : exp 1 ≠ 0 := by positivity
    have h20e1pos : 20 * exp 1 ≠ 0 := by positivity
    calc
      log (20 * exp 1 * (J : ℝ)) = log (20 * exp 1) + log (J : ℝ) :=
        log_mul h20e1pos (by linarith : (J : ℝ) ≠ 0)
      _ = (log 20 + log (exp 1)) + log (J : ℝ) := by rw [log_mul h20pos he1pos]
      _ = (log 20 + 1) + log (J : ℝ) := by rw [log_exp 1]
      _ ≤ (3 + 1) + log (J : ℝ) := by
        have hlog20 : log (20 : ℝ) ≤ 3 := by
          rw [log_le_iff_le_exp (by norm_num : 0 < (20 : ℝ))]
          have h_exp3_gt_20 : (20 : ℝ) < exp 3 := by
            have h_exp1_gt : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
            have h_exp3_eq : exp 3 = (exp 1)^3 := by
              calc
                exp 3 = exp ((3 : ℕ) * 1) := by norm_num
                _ = (exp 1)^(3 : ℕ) := by rw [exp_nat_mul]
                _ = (exp 1)^3 := by norm_num
            rw [h_exp3_eq]
            have h_cube : (20 : ℝ) < (2.7182818283 : ℝ)^3 := by norm_num
            have h_pow_lt : (2.7182818283 : ℝ)^3 < (exp 1)^3 :=
              pow_lt_pow_left₀ h_exp1_gt (by norm_num : 0 ≤ (2.7182818283 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)
            linarith
          exact h_exp3_gt_20.le
        nlinarith
      _ = log (J : ℝ) + 4 := by ring
      _ ≤ ((J : ℝ) - 1) + 4 := by
        have hlogj : log (J : ℝ) ≤ (J : ℝ) - 1 := log_le_sub_one_of_pos hjpos
        nlinarith
      _ = (J : ℝ) + 3 := by ring
  -- Step 2: LHS ≤ 2J + 41/2
  have hLHS : 29 / 2 + 2 * log (20 * exp 1 * (J : ℝ)) ≤ 2 * (J : ℝ) + 41/2 := by
    nlinarith
  -- Step 3: exp(J-1) ≥ (J-4) * exp 4
  have hexp_ineq : ((J : ℝ) - 4) * exp 4 ≤ exp ((J : ℝ) - 1) := by
    have h_add : exp ((J : ℝ) - 1) = exp ((J : ℝ) - 5) * exp 4 := by
      have h_eq : (J : ℝ) - 1 = ((J : ℝ) - 5) + 4 := by ring
      rw [h_eq, exp_add]
    rw [h_add]
    have h_exp_ge : (J : ℝ) - 4 ≤ exp ((J : ℝ) - 5) := by
      have := Real.add_one_le_exp ((J : ℝ) - 5)
      linarith
    have h_exp4_nonneg : 0 ≤ exp 4 := Real.exp_pos 4 |>.le
    nlinarith
  -- Step 4: exp 4 > 54.5
  have hexp4 : (54.5 : ℝ) < exp 4 := by
    have h_exp1_gt : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
    have h_exp4_eq : exp 4 = (exp 1)^4 := by
      calc
        exp 4 = exp ((4 : ℕ) * 1) := by norm_num
        _ = (exp 1)^(4 : ℕ) := by rw [exp_nat_mul]
        _ = (exp 1)^4 := by norm_num
    rw [h_exp4_eq]
    have h_fourth : (54.5 : ℝ) < (2.7182818283 : ℝ)^4 := by norm_num
    have h_pow_lt : (2.7182818283 : ℝ)^4 < (exp 1)^4 :=
      pow_lt_pow_left₀ h_exp1_gt (by norm_num : 0 ≤ (2.7182818283 : ℝ)) (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  -- Step 5: RHS ≥ 2J + 41/2
  have hRHS : 2 * (J : ℝ) + 41/2 ≤ 2/3 * exp ((J : ℝ) - 1) := by
    have h_mid : 2 * (J : ℝ) + 41/2 ≤ 2/3 * (((J : ℝ) - 4) * exp 4) := by
      have h_bound : 2 * (J : ℝ) + 41/2 ≤ (2/3 : ℝ) * (((J : ℝ) - 4) * (54.5 : ℝ)) := by
        nlinarith
      have h_exp4_factor : (2/3 : ℝ) * (((J : ℝ) - 4) * (54.5 : ℝ)) ≤ (2/3 : ℝ) * (((J : ℝ) - 4) * exp 4) := by
        have h_nonneg : 0 ≤ (2/3 : ℝ) * ((J : ℝ) - 4) := by
          nlinarith
        nlinarith
      nlinarith
    have h_final : (2/3 : ℝ) * (((J : ℝ) - 4) * exp 4) ≤ 2/3 * exp ((J : ℝ) - 1) := by
      have h_nonneg : 0 ≤ (2/3 : ℝ) := by norm_num
      nlinarith
    nlinarith
  -- Combine
  linarith

/-- (C1). -/
theorem level_ge {T : ℕ} (hT : T0 ≤ T) : 29 / 2 ≤ level T := by
  set J := j0 T with hJ
  have hT0pos : 0 < T0 := by
    unfold T0
    norm_num
  have hTpos : 0 < T := Nat.lt_of_lt_of_le hT0pos hT
  have hTpos' : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hT_gt_one : (1 : ℝ) < (T : ℝ) := by
    have hT0_gt_one : 1 < T0 := by
      unfold T0; norm_num
    have hT0_le_T : T0 ≤ T := hT
    exact_mod_cast Nat.lt_of_lt_of_le hT0_gt_one hT0_le_T
  have h_log_T_pos : 0 < Real.log (T : ℝ) := Real.log_pos hT_gt_one
  have hJpos : 1 ≤ J := j0_pos hT
  by_cases hJle4 : J ≤ 4
  · -- Case (a): J ≤ 4
    have hJle4' : (J : ℝ) ≤ 4 := by exact_mod_cast hJle4
    have hT0_le_T : (T0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hpos_denom2 : 0 < 20 * Real.exp 1 * (J : ℝ) := by positivity
    have h_denom_le : 20 * Real.exp 1 * (J : ℝ) ≤ 80 * Real.exp 1 := by
      have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith
    have h_div_ge : (T0 : ℝ) / (80 * Real.exp 1) ≤ (T : ℝ) / (20 * Real.exp 1 * (J : ℝ)) :=
      div_le_div₀ (by positivity) hT0_le_T hpos_denom2 h_denom_le
    -- Show (T0 : ℝ) / (80 * exp 1) ≥ exp (29/4)
    have h_T0_ge : 80 * Real.exp (33/4 : ℝ) ≤ (T0 : ℝ) := by
      have h_exp_le : Real.exp (33/4 : ℝ) ≤ 4446 := exp_33_4_le
      have h_mul : 80 * Real.exp (33/4 : ℝ) ≤ 80 * (4446 : ℝ) := by nlinarith
      have h_80_4446 : (80 : ℝ) * 4446 ≤ (T0 : ℝ) := by
        unfold T0; norm_num
      nlinarith
    have h_exp_sub : Real.exp (29/4 : ℝ) = Real.exp (33/4 : ℝ) / Real.exp 1 := by
      calc
        Real.exp (29/4 : ℝ) = Real.exp ((33/4 : ℝ) - 1) := by ring_nf
        _ = Real.exp (33/4 : ℝ) / Real.exp 1 := Real.exp_sub _ _
    have h_div_T0_ge : Real.exp (29/4 : ℝ) ≤ (T0 : ℝ) / (80 * Real.exp 1) := by
      rw [h_exp_sub]
      calc
        Real.exp (33/4 : ℝ) / Real.exp 1 = (80 * Real.exp (33/4 : ℝ)) / (80 * Real.exp 1) := by ring
        _ ≤ (T0 : ℝ) / (80 * Real.exp 1) :=
          ((div_le_div_iff_of_pos_right (by positivity : 0 < 80 * Real.exp 1)).mpr h_T0_ge)
    have h_final : Real.exp (29/4 : ℝ) ≤ (T : ℝ) / (20 * Real.exp 1 * (J : ℝ)) :=
      le_trans h_div_T0_ge h_div_ge
    have h_log : 29/4 ≤ Real.log ((T : ℝ) / (20 * Real.exp 1 * (J : ℝ))) := by
      calc
        29/4 = Real.log (Real.exp (29/4 : ℝ)) := (Real.log_exp _).symm
        _ ≤ Real.log ((T : ℝ) / (20 * Real.exp 1 * (J : ℝ))) :=
          Real.log_le_log (by positivity) h_final
    unfold level
    rw [← hJ]
    nlinarith
  · -- Case (b): 5 ≤ J
    have hJge5 : 5 ≤ J := by omega
    have hJpos' : 1 ≤ J := by omega
    have h_lt_ceil : (J - 1) < j0 T := by
      rw [hJ]
      omega
    have h_lt_log : ((J - 1 : ℕ) : ℝ) < Real.log (3 * Real.log (T : ℝ)) :=
      (Nat.lt_ceil.mp h_lt_ceil)
    have h_cast : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
      rw [Nat.cast_sub hJpos', Nat.cast_one]
    rw [h_cast] at h_lt_log
    have h_pos_arg : 0 < 3 * Real.log (T : ℝ) := by
      positivity
    have h_exp_lt : Real.exp ((J : ℝ) - 1) < 3 * Real.log (T : ℝ) := by
      calc
        Real.exp ((J : ℝ) - 1) < Real.exp (Real.log (3 * Real.log (T : ℝ))) :=
          Real.exp_lt_exp.mpr h_lt_log
        _ = 3 * Real.log (T : ℝ) := Real.exp_log h_pos_arg
    have h_2log_gt : 2 * Real.log (T : ℝ) > (2/3 : ℝ) * Real.exp ((J : ℝ) - 1) := by
      linarith
    have h_five_case := five_case hJge5
    have h_ineq : 29/2 ≤ (2/3 : ℝ) * Real.exp ((J : ℝ) - 1) - 2 * Real.log (20 * Real.exp 1 * (J : ℝ)) := by
      linarith
    have h_level_eq : level T = 2 * Real.log (T : ℝ) - 2 * Real.log (20 * Real.exp 1 * (J : ℝ)) := by
      unfold level
      rw [hJ]
      rw [Real.log_div (by positivity) (by positivity)]
      ring
    rw [h_level_eq]
    linarith

theorem j0_le {T : ℕ} (hT : T0 ≤ T) : (j0 T : ℝ) ≤ log (log T) + 2.1 := by
  have hTpos : 1 < (T : ℝ) := by
    have hT0 : (1 : ℕ) < T0 := by
      unfold T0; norm_num
    have hT' : (1 : ℕ) < T := Nat.lt_of_lt_of_le hT0 hT
    exact_mod_cast hT'
  have hlogTpos : 0 < log (T : ℝ) := Real.log_pos hTpos
  have hone_lt_logT : 1 < log (T : ℝ) := by
    have h_exp_lt_T : Real.exp 1 < (T : ℝ) := by
      have h_exp_lt_3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      have h3_le_T : (3 : ℝ) ≤ (T : ℝ) := by
        have hT3 : (3 : ℕ) ≤ T := by
          have hT0_3 : (3 : ℕ) ≤ T0 := by unfold T0; norm_num
          exact Nat.le_trans hT0_3 hT
        exact_mod_cast hT3
      linarith
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ < Real.log (T : ℝ) := Real.log_lt_log (Real.exp_pos 1) h_exp_lt_T
  have hpos : 0 ≤ log (3 * log (T : ℝ)) := by
    have hpos' : 1 < 3 * log (T : ℝ) := by linarith
    have hpos'' : 1 ≤ 3 * log (T : ℝ) := by linarith
    exact Real.log_nonneg hpos''
  unfold j0
  have hceil : (⌈log (3 * log (T : ℝ))⌉₊ : ℝ) < log (3 * log (T : ℝ)) + 1 :=
    Nat.ceil_lt_add_one hpos
  have hlog3 : Real.log 3 < 1.1 := by
    have h : Real.log 3 < 1.0986122888 := Real.log_three_lt_d9
    have h' : (1.0986122888 : ℝ) < 1.1 := by norm_num
    linarith
  have hmul : log (3 * log (T : ℝ)) = Real.log 3 + log (log (T : ℝ)) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by linarith : log (T : ℝ) ≠ 0)]
  have hgoal : log (3 * log (T : ℝ)) + 1 ≤ log (log (T : ℝ)) + 2.1 := by
    rw [hmul]
    linarith
  linarith

/-- (C2). -/
theorem C2 {T : ℕ} (hT : T0 ≤ T) :
    (j0 T : ℝ) * (88 / 10 * exp 1 * exp (level T / 2) + 1) ≤ (T1 T : ℝ) - 1 := by
  have hj0_pos : 1 ≤ j0 T := j0_pos hT
  have hj0_le : (j0 T : ℝ) ≤ Real.log (Real.log T) + 2.1 := j0_le hT
  have hT0_pos : 0 < T0 := by unfold T0; norm_num
  have hT0_gt_one : 1 < T0 := by unfold T0; norm_num
  have hT_pos : 0 < (T : ℝ) := by
    have h : 0 < T := Nat.lt_of_lt_of_le hT0_pos hT
    exact_mod_cast h
  have h_denom_pos : 0 < 20 * Real.exp 1 * (j0 T : ℝ) := by
    have hj0 : 0 < (j0 T : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hj0_pos
    positivity
  have h_arg_pos : 0 < (T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ)) := by
    positivity
  have h_exp : Real.exp (level T / 2) = (T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ)) := by
    unfold level
    have h : (2 * Real.log ((T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ)))) / 2 =
             Real.log ((T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ))) := by ring
    rw [h, Real.exp_log h_arg_pos]
  have h_left : (j0 T : ℝ) * (88 / 10 * Real.exp 1 * Real.exp (level T / 2) + 1) =
               (44/100) * (T : ℝ) + (j0 T : ℝ) := by
    rw [h_exp]
    field_simp
    ring
  have h_right : (T : ℝ) / 2 - 3/2 ≤ (T1 T : ℝ) - 1 := by
    have hdiv : (T1 T : ℝ) ≥ (T : ℝ) / 2 - 1/2 := by
      rw [T1]
      rcases Nat.even_or_odd T with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- T = k + k (even)
        rw [hk]
        have : ((k + k) / 2 : ℕ) = k := by omega
        rw [this]
        push_cast
        ring_nf
        linarith
      · -- T = 2*k + 1 (odd)
        rw [hk]
        have : ((2*k + 1) / 2 : ℕ) = k := by omega
        rw [this]
        push_cast
        ring_nf
        linarith
    linarith
  have h_logT_nonneg : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by
      have h : 1 ≤ (T : ℝ) := by
        have h' : 1 < T := Nat.lt_of_lt_of_le hT0_gt_one hT
        exact_mod_cast h'.le
      exact h)
  have h_log_log_le_log : Real.log (Real.log (T : ℝ)) ≤ Real.log (T : ℝ) :=
    Real.log_le_self h_logT_nonneg
  have h_logT_le_T_div_1000_add_6 : Real.log (T : ℝ) ≤ (T : ℝ) / 1000 + 6 := by
    have h_exp_seven_gt_1000 : (1000 : ℝ) < Real.exp 7 := by
      have h_exp_one_gt : (2.7 : ℝ) < Real.exp 1 := by
        linarith [exp_one_gt_d9]
      have h_pow : (2.7 : ℝ)^7 < (Real.exp 1)^7 := by
        gcongr
      have h_27_pow_gt : ((10 : ℝ)^10) < (27 : ℝ)^7 := by norm_num
      have h_27_div_10_pow_gt : (1000 : ℝ) < ((27 : ℝ) / 10)^7 := by
        have hpos : (0 : ℝ) < (10 : ℝ)^7 := by norm_num
        calc
          (1000 : ℝ) = ((10 : ℝ)^10) / ((10 : ℝ)^7) := by norm_num
          _ < (27 : ℝ)^7 / ((10 : ℝ)^7) := by
            exact (div_lt_div_of_pos_right h_27_pow_gt hpos)
          _ = ((27 : ℝ) / 10)^7 := by ring
      have h_exp_seven_eq : Real.exp 7 = (Real.exp 1)^7 := by
        calc
          Real.exp 7 = Real.exp ((7 : ℕ) * 1) := by ring_nf
          _ = (Real.exp 1)^(7 : ℕ) := by rw [Real.exp_nat_mul]
          _ = (Real.exp 1)^7 := by norm_num
      rw [h_exp_seven_eq]
      linarith
    have h_log_1000_lt_7 : Real.log (1000 : ℝ) < 7 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 1000) h_exp_seven_gt_1000
      rwa [Real.log_exp (7 : ℝ)] at h
    have h_log_div : Real.log ((T : ℝ) / 1000) ≤ (T : ℝ) / 1000 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hT_pos (by norm_num))
    have h_log_eq : Real.log ((T : ℝ) / 1000) = Real.log (T : ℝ) - Real.log (1000 : ℝ) := by
      exact Real.log_div hT_pos.ne' (by norm_num : (1000 : ℝ) ≠ 0)
    rw [h_log_eq] at h_log_div
    linarith
  have h_j0_bound : (j0 T : ℝ) ≤ (6/100) * (T : ℝ) - 3/2 := by
    have h1 : (j0 T : ℝ) ≤ Real.log (Real.log (T : ℝ)) + 2.1 := hj0_le
    have h2 : Real.log (Real.log (T : ℝ)) + 2.1 ≤ Real.log (T : ℝ) + 2.1 := by linarith
    have h3 : Real.log (T : ℝ) + 2.1 ≤ ((T : ℝ) / 1000 + 6) + 2.1 := by linarith
    have h4 : ((T : ℝ) / 1000 + 6) + 2.1 ≤ (6/100) * (T : ℝ) - 3/2 := by
      have hT_large : (355713 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      nlinarith
    linarith
  linarith

/-- (C3). -/
theorem C3 {T : ℕ} (hT : T0 ≤ T) : π ^ 2 * exp 2 * (aP (level T) + 2) ^ 2 ≤ k0 T := by
  -- We work in ℝ throughout
  have hTpos : 0 < (T : ℝ) := by
    have h : 0 < T := Nat.lt_of_lt_of_le (by norm_num [T0]) hT
    exact_mod_cast h
  have hT0pos : 0 < (T0 : ℝ) := by norm_num [T0]
  -- Step 1: k0 T ≥ T/2 as reals
  have hk0_ge : (T : ℝ) / 2 ≤ (k0 T : ℝ) := by
    have h_mul : 2 * (T / 2) ≤ T := Nat.mul_div_le T 2
    have h_mul' : 2 * ((T / 2 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast h_mul
    have h_div_le : T / 2 ≤ T := Nat.div_le_self T 2
    unfold k0 T1
    rw [Nat.cast_sub h_div_le]
    linarith
  -- Step 2: level T ≤ 2 * log T
  have hlevel_le : level T ≤ 2 * Real.log (T : ℝ) := by
    unfold level
    have h_j0_pos : 1 ≤ j0 T := j0_pos hT
    have h_j0_pos' : (1 : ℝ) ≤ (j0 T : ℝ) := by exact_mod_cast h_j0_pos
    have h_one_le_denom : 1 ≤ 20 * Real.exp 1 * (j0 T : ℝ) := by
      have h_exp_gt_2 : 2 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      nlinarith
    have h_arg_le : (T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ)) ≤ (T : ℝ) := by
      calc
        (T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ)) ≤ (T : ℝ) / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h_one_le_denom
        _ = (T : ℝ) := by simp
    have h_log_le : Real.log ((T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ))) ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by positivity) h_arg_le
    nlinarith
  -- Step 3: aP (level T) ≤ √(2 * log T) + 1
  have haP_le : aP (level T) ≤ Real.sqrt (2 * Real.log (T : ℝ)) + 1 := by
    unfold aP
    have hL_nonneg : 0 ≤ level T := by
      have h := level_ge hT
      linarith
    have h_sqrt58_le_one : Real.sqrt (5/8 : ℝ) ≤ 1 := by
      calc
        Real.sqrt (5/8 : ℝ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
        _ = 1 := Real.sqrt_one
    have h_exp_le_one : Real.exp (-(level T) / 4) ≤ 1 := by
      have h_nonpos : -(level T) / 4 ≤ 0 := by
        linarith
      exact (Real.exp_le_one_iff.mpr h_nonpos)
    have h_sqrtL_le : Real.sqrt (level T) ≤ Real.sqrt (2 * Real.log (T : ℝ)) :=
      Real.sqrt_le_sqrt hlevel_le
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (2 * Real.log (T : ℝ)) := Real.sqrt_nonneg _
    have h_nonneg_sqrt58 : 0 ≤ Real.sqrt (5/8 : ℝ) := Real.sqrt_nonneg _
    have h_nonneg_exp : 0 ≤ Real.exp (-(level T) / 4) := Real.exp_nonneg _
    -- aP = √L + √(5/8) * exp(-L/4) ≤ √(2 log T) + 1 * 1 = √(2 log T) + 1
    calc
      Real.sqrt (level T) + Real.sqrt (5/8 : ℝ) * Real.exp (-(level T) / 4) ≤
          Real.sqrt (2 * Real.log (T : ℝ)) + Real.sqrt (5/8 : ℝ) * Real.exp (-(level T) / 4) := by
        gcongr
      _ ≤ Real.sqrt (2 * Real.log (T : ℝ)) + 1 * Real.exp (-(level T) / 4) := by
        gcongr
      _ ≤ Real.sqrt (2 * Real.log (T : ℝ)) + 1 * 1 := by
        gcongr
      _ = Real.sqrt (2 * Real.log (T : ℝ)) + 1 := by ring
  -- Step 4: (aP (level T) + 2)^2 ≤ 4 * log T + 18
  have h_sq_le : (aP (level T) + 2)^2 ≤ 4 * Real.log (T : ℝ) + 18 := by
    have h_sum_le : aP (level T) + 2 ≤ Real.sqrt (2 * Real.log (T : ℝ)) + 3 := by
      linarith
    have h_nonneg_sum : 0 ≤ aP (level T) + 2 := by
      have haP_nonneg : 0 ≤ aP (level T) := by
        unfold aP
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (level T) := Real.sqrt_nonneg _
        have h_exp_nonneg : 0 ≤ Real.exp (-(level T) / 4) := Real.exp_nonneg _
        positivity
      linarith
    have h_nonneg_sqrt_sum : 0 ≤ Real.sqrt (2 * Real.log (T : ℝ)) + 3 := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.log (T : ℝ)) := Real.sqrt_nonneg _
      positivity
    have h_sq_le' : (aP (level T) + 2)^2 ≤ (Real.sqrt (2 * Real.log (T : ℝ)) + 3)^2 := by
      have := sq_le_sq₀ h_nonneg_sum h_nonneg_sqrt_sum
      -- this : (aP + 2)^2 ≤ (√ + 3)^2 ↔ aP + 2 ≤ √ + 3
      rw [this]
      exact h_sum_le
    have h_sq_bound : (Real.sqrt (2 * Real.log (T : ℝ)) + 3)^2 ≤ 4 * Real.log (T : ℝ) + 18 := by
      have h_add_sq := add_sq_le (a := Real.sqrt (2 * Real.log (T : ℝ))) (b := 3)
      -- h_add_sq : (a + b)^2 ≤ 2*(a^2 + b^2)
      have h_sq_sqrt : (Real.sqrt (2 * Real.log (T : ℝ))) ^ 2 = 2 * Real.log (T : ℝ) := by
        have h_nonneg : 0 ≤ 2 * Real.log (T : ℝ) := by
          have hT1 : 1 ≤ T := by
            have h0 : 0 < T := Nat.lt_of_lt_of_le (by norm_num [T0]) hT
            omega
          have h_log_nonneg : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT1)
          positivity
        rw [Real.sq_sqrt h_nonneg]
      nlinarith
    linarith
  -- Step 5: π^2 * exp 2 ≤ 74
  have h_pi_eps : π ^ 2 * Real.exp 2 ≤ 74 := by
    have h_pi_lt : π < 3.15 := Real.pi_lt_d2
    have h_exp1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h_pi_sq_lt : π ^ 2 < (3.15 : ℝ) ^ 2 := by
      have h_pi_nonneg : 0 ≤ π := by positivity
      have h_315_nonneg : 0 ≤ (3.15 : ℝ) := by norm_num
      exact pow_lt_pow_left₀ h_pi_lt h_pi_nonneg (n := 2) (by norm_num)
    have h_exp2_lt : Real.exp 2 < (2.7182818286 : ℝ) ^ 2 := by
      have h_exp2_eq : Real.exp 2 = (Real.exp 1) ^ 2 := by
        calc
          Real.exp 2 = Real.exp ((2 : ℕ) • (1 : ℝ)) := by norm_num
          _ = (Real.exp 1) ^ (2 : ℕ) := by rw [Real.exp_nsmul]
          _ = (Real.exp 1) ^ 2 := by norm_num
      rw [h_exp2_eq]
      refine pow_lt_pow_left₀ h_exp1_lt (Real.exp_pos 1).le (n := 2) (by norm_num)
    have h_bound : (3.15 : ℝ) ^ 2 * (2.7182818286 : ℝ) ^ 2 ≤ 74 := by norm_num
    nlinarith
  -- Step 6: T/2 ≥ 74*(4 log T + 18)
  have h_main : 74 * (4 * Real.log (T : ℝ) + 18) ≤ (T : ℝ) / 2 := by
    -- First, prove log T0 ≤ 13 (since exp 13 > 355713)
    have h_log_T0_le_13 : Real.log (T0 : ℝ) ≤ 13 := by
      have h_exp13_gt : (T0 : ℝ) < Real.exp 13 := by
        have h_num : (T0 : ℝ) = 355713 := by norm_num [T0]
        rw [h_num]
        have h_exp1_gt : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
        have h_pow_lt : (2.7182818283 : ℝ) ^ 13 < (Real.exp 1) ^ 13 :=
          pow_lt_pow_left₀ h_exp1_gt (by norm_num) (by norm_num : 13 ≠ 0)
        have h_exp13_eq : (Real.exp 1) ^ 13 = Real.exp 13 := by
          calc
            (Real.exp 1) ^ 13 = Real.exp ((13 : ℕ) • (1 : ℝ)) := by rw [Real.exp_nsmul]
            _ = Real.exp 13 := by norm_num
        have h_num_lt : 355713 < (2.7182818283 : ℝ) ^ 13 := by norm_num
        linarith
      have h_pos : 0 < (T0 : ℝ) := by norm_num [T0]
      exact (Real.log_le_iff_le_exp h_pos).mpr h_exp13_gt.le
    -- Now bound log T for any T ≥ T0
    have h_log_T_le : Real.log (T : ℝ) ≤ Real.log (T0 : ℝ) + ((T : ℝ) - (T0 : ℝ)) / (T0 : ℝ) := by
      have h_ratio_pos : 0 < (T : ℝ) / (T0 : ℝ) := div_pos hTpos hT0pos
      have h_log_ratio_le : Real.log ((T : ℝ) / (T0 : ℝ)) ≤ ((T : ℝ) / (T0 : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos h_ratio_pos
      have h_log_div : Real.log ((T : ℝ) / (T0 : ℝ)) = Real.log (T : ℝ) - Real.log (T0 : ℝ) :=
        Real.log_div (by linarith) (by linarith)
      rw [h_log_div] at h_log_ratio_le
      have h_eq : ((T : ℝ) / (T0 : ℝ)) - 1 = ((T : ℝ) - (T0 : ℝ)) / (T0 : ℝ) := by
        field_simp [hT0pos.ne']
      rw [h_eq] at h_log_ratio_le
      linarith
    -- Now combine the bounds
    have h_log_T_le' : Real.log (T : ℝ) ≤ 13 + ((T : ℝ) - (T0 : ℝ)) / (T0 : ℝ) := by
      linarith
    have h_592_div_T0_le_1_over_600 : 592 / (T0 : ℝ) ≤ 1/600 := by
      have h_T0_eq : (T0 : ℝ) = 355713 := by norm_num [T0]
      rw [h_T0_eq]
      norm_num
    -- 592 * log T ≤ 592 * (13 + (T - T0)/T0) = 592*13 + 592*(T - T0)/T0
    -- = 7696 + 592*(T - T0)/T0 ≤ 7696 + (T - T0)/600
    have h_bound_log : 592 * Real.log (T : ℝ) ≤ 7696 + ((T : ℝ) - (T0 : ℝ)) / 600 := by
      have h_mul : 592 * (((T : ℝ) - (T0 : ℝ)) / (T0 : ℝ)) ≤ ((T : ℝ) - (T0 : ℝ)) / 600 := by
        have h_nonneg : 0 ≤ (T : ℝ) - (T0 : ℝ) := by
          have hT_ge_T0 : (T0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
          linarith
        have h := mul_le_mul_of_nonneg_right h_592_div_T0_le_1_over_600 h_nonneg
        calc
          592 * (((T : ℝ) - (T0 : ℝ)) / (T0 : ℝ)) = (592 / (T0 : ℝ)) * ((T : ℝ) - (T0 : ℝ)) := by ring
          _ ≤ (1/600) * ((T : ℝ) - (T0 : ℝ)) := h
          _ = ((T : ℝ) - (T0 : ℝ)) / 600 := by ring
      nlinarith
    -- We need: T/2 ≥ 74*(4 log T + 18) = 296 log T + 1332
    -- Using the bound on log T:
    -- 296 log T = (296/592) * 592 log T ≤ (1/2) * (7696 + (T - T0)/600)
    -- = 3848 + (T - T0)/1200
    -- Then T - 296 log T - 1332 ≥ T - 3848 - (T - T0)/1200 - 1332
    -- = T*(1 - 1/1200) - 5180 + T0/1200
    have h_main' : 296 * Real.log (T : ℝ) + 1332 ≤ (T : ℝ) / 2 := by
      have hT_ge_T0 : (T0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      -- From h_bound_log: 592 * log T ≤ 7696 + (T - T0)/600
      -- So 296 * log T ≤ 3848 + (T - T0)/1200
      have h_log_bound : 296 * Real.log (T : ℝ) ≤ 3848 + ((T : ℝ) - (T0 : ℝ)) / 1200 := by
        nlinarith
      -- Then 296 * log T + 1332 ≤ 3848 + (T - T0)/1200 + 1332 = 5180 + (T - T0)/1200
      -- We need: 5180 + (T - T0)/1200 ≤ T/2
      have h_ineq : 5180 + ((T : ℝ) - (T0 : ℝ)) / 1200 ≤ (T : ℝ) / 2 := by
        have hT0_eq : (T0 : ℝ) = 355713 := by norm_num [T0]
        rw [hT0_eq]
        -- Goal: 5180 + (T - 355713)/1200 ≤ T/2
        -- Multiply by 1200: 5180*1200 + T - 355713 ≤ 600*T
        have h_mul : 5180*1200 + ((T : ℝ) - 355713) ≤ 600*(T : ℝ) := by
          have hT_ge : (355713 : ℝ) ≤ (T : ℝ) := by
            simpa [hT0_eq] using hT_ge_T0
          nlinarith
        linarith
      nlinarith
    nlinarith
  -- Combine
  have h_nonneg_pi_eps : 0 ≤ π ^ 2 * Real.exp 2 := by positivity
  have h_nonneg_log_term : 0 ≤ 4 * Real.log (T : ℝ) + 18 := by
    have h_log_nonneg : 0 ≤ Real.log (T : ℝ) := by
      have hT1 : 1 ≤ T := by
        have h0 : 0 < T := Nat.lt_of_lt_of_le (by norm_num [T0]) hT
        omega
      exact Real.log_nonneg (by exact_mod_cast hT1)
    positivity
  calc
    π ^ 2 * exp 2 * (aP (level T) + 2) ^ 2 ≤ π ^ 2 * exp 2 * (4 * Real.log (T : ℝ) + 18) := by
      gcongr
    _ ≤ 74 * (4 * Real.log (T : ℝ) + 18) := by
      gcongr
    _ ≤ (T : ℝ) / 2 := h_main
    _ ≤ (k0 T : ℝ) := hk0_ge

theorem c1_le : c1 ≤ 333 / 100 := by
  unfold c1 Jc
  -- Goal: (1/2 + 4/3 - 8/π² + log(π²) + ((π²/4) - 2)/(π² * exp 2)) ≤ 333/100
  -- bounds on π
  have hπl : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hπu : π < (3.141593 : ℝ) := Real.pi_lt_d6
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  -- bounds on π²
  have hπsq_lt : π ^ 2 < (9.8697 : ℝ) := by
    have hsq : π ^ 2 < (3.141593 : ℝ) ^ 2 := by
      have hpos' : (0 : ℝ) < (3.141593 : ℝ) := by norm_num
      have h1 : π * π < (3.141593 : ℝ) * π :=
        mul_lt_mul_of_pos_right hπu hπpos
      have h2 : (3.141593 : ℝ) * π < (3.141593 : ℝ) * (3.141593 : ℝ) :=
        mul_lt_mul_of_pos_left hπu hpos'
      simpa [sq] using lt_trans h1 h2
    have hval : (3.141593 : ℝ) ^ 2 < (9.8697 : ℝ) := by norm_num
    linarith
  have hπsq_gt : (9.8696 : ℝ) < π ^ 2 := by
    have hsq : (3.141592 : ℝ) ^ 2 < π ^ 2 := by
      have hpos' : (0 : ℝ) < (3.141592 : ℝ) := by norm_num
      have h1 : (3.141592 : ℝ) * (3.141592 : ℝ) < π * (3.141592 : ℝ) :=
        mul_lt_mul_of_pos_right hπl hpos'
      have h2 : π * (3.141592 : ℝ) < π * π :=
        mul_lt_mul_of_pos_left hπl hπpos
      simpa [sq] using lt_trans h1 h2
    have hval : (9.8696 : ℝ) < (3.141592 : ℝ) ^ 2 := by norm_num
    linarith
  -- bounds on exp 2
  have hexp2_gt : (7.389 : ℝ) < exp 2 := by
    have hexp2_eq : exp 2 = exp 1 * exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hexp2_eq]
    have h := Real.exp_one_gt_d9
    have hpos_exp : (0 : ℝ) < exp 1 := Real.exp_pos 1
    have hpos' : (0 : ℝ) < (2.7182818283 : ℝ) := by norm_num
    have h1 : (2.7182818283 : ℝ) * (2.7182818283 : ℝ) < exp 1 * (2.7182818283 : ℝ) :=
      mul_lt_mul_of_pos_right h hpos'
    have h2 : exp 1 * (2.7182818283 : ℝ) < exp 1 * exp 1 :=
      mul_lt_mul_of_pos_left h hpos_exp
    have hsq : (2.7182818283 : ℝ) * (2.7182818283 : ℝ) < exp 1 * exp 1 := lt_trans h1 h2
    have hval : (7.389 : ℝ) < (2.7182818283 : ℝ) * (2.7182818283 : ℝ) := by norm_num
    linarith
  -- bound on log(π²)
  have hlog_lt : Real.log (π ^ 2) < (2.2976 : ℝ) := by
    have h_exp_bound : (3.141593 : ℝ) < exp (1.1488 : ℝ) := by
      have hsum : ∑ i ∈ Finset.range 6, ((1.1488 : ℝ) ^ i / (i.factorial : ℝ)) ≤ exp (1.1488 : ℝ) :=
        Real.sum_le_exp_of_nonneg (by norm_num) 6
      have hval : (3.141593 : ℝ) < ∑ i ∈ Finset.range 6, ((1.1488 : ℝ) ^ i / (i.factorial : ℝ)) := by
        norm_num
      linarith
    have hπ_lt_exp : π < exp (1.1488 : ℝ) := by linarith
    have hlog_lt' : Real.log π < (1.1488 : ℝ) := by
      have h := (Real.log_lt_log_iff hπpos (Real.exp_pos _)).mpr hπ_lt_exp
      rwa [Real.log_exp] at h
    calc
      Real.log (π ^ 2) = 2 * Real.log π := by rw [Real.log_pow, Nat.cast_ofNat]
      _ < 2 * (1.1488 : ℝ) := by nlinarith
      _ = (2.2976 : ℝ) := by norm_num
  -- bound on (π²/4 - 2)/(π² * exp 2)
  have h_num_lt : (π ^ 2 / 4 - 2) < (0.467425 : ℝ) := by
    have h : π ^ 2 / 4 < (9.8697 : ℝ) / 4 := by linarith
    have h' : (9.8697 : ℝ) / 4 - 2 = (0.467425 : ℝ) := by norm_num
    linarith
  have h_denom_gt : (9.8696 : ℝ) * (7.389 : ℝ) < π ^ 2 * exp 2 := by
    have hpos1 : (0 : ℝ) < π ^ 2 := by positivity
    have hpos2 : (0 : ℝ) < (7.389 : ℝ) := by norm_num
    have h1 : (9.8696 : ℝ) < π ^ 2 := hπsq_gt
    have h2 : (7.389 : ℝ) ≤ exp 2 := by linarith
    exact mul_lt_mul h1 h2 hpos2 hpos1.le
  have hpos_num : (0 : ℝ) < π ^ 2 / 4 - 2 := by
    -- π² > 9.8696 > 8, so π²/4 > 2
    have h : (8 : ℝ) < π ^ 2 := by linarith
    linarith
  -- Now combine all bounds
  -- We have:
  -- hA: 8/9.8697 < 8/π²
  have hA : 8 / (9.8697 : ℝ) < 8 / π ^ 2 := by
    have h_one_div : 1 / (9.8697 : ℝ) < 1 / π ^ 2 :=
      ((one_div_lt_one_div (by norm_num) (by positivity)).mpr hπsq_lt)
    have h8pos : (0 : ℝ) < (8 : ℝ) := by norm_num
    calc
      8 / (9.8697 : ℝ) = (8 : ℝ) * (1 / (9.8697 : ℝ)) := by ring
      _ < (8 : ℝ) * (1 / π ^ 2) := mul_lt_mul_of_pos_left h_one_div h8pos
      _ = 8 / π ^ 2 := by ring
  -- hC: (π²/4 - 2)/(π² * exp 2) < 0.467425/(9.8696 * 7.389)
  have hC : ((π ^ 2 / 4 - 2) / (π ^ 2 * exp 2)) < ((0.467425 : ℝ) / ((9.8696 : ℝ) * (7.389 : ℝ))) := by
    have hpos_denom : (0 : ℝ) < π ^ 2 * exp 2 := by positivity
    have hpos_denom2 : (0 : ℝ) < (9.8696 : ℝ) * (7.389 : ℝ) := by norm_num
    have hpos_A : (0 : ℝ) < (0.467425 : ℝ) := by norm_num
    have h1 : (π ^ 2 / 4 - 2) / (π ^ 2 * exp 2) < (0.467425 : ℝ) / (π ^ 2 * exp 2) :=
      div_lt_div_of_pos_right h_num_lt hpos_denom
    have h2 : (0.467425 : ℝ) / (π ^ 2 * exp 2) < (0.467425 : ℝ) / ((9.8696 : ℝ) * (7.389 : ℝ)) :=
      div_lt_div_of_pos_left hpos_A hpos_denom2 h_denom_gt
    linarith
  -- Now the main inequality:
  -- 1/2 + 4/3 - 8/π² + log(π²) + (π²/4-2)/(π²*exp 2)
  -- < 1/2 + 4/3 - 8/9.8697 + 2.2976 + 0.467425/(9.8696*7.389)
  -- ≤ 333/100
  have h_main : (1/2 : ℝ) + (4/3 : ℝ) - 8/π^2 + Real.log (π^2) + ((π^2/4 - 2)/(π^2 * exp 2)) ≤
      (1/2 : ℝ) + (4/3 : ℝ) - 8/(9.8697 : ℝ) + (2.2976 : ℝ) + ((0.467425 : ℝ)/((9.8696 : ℝ)*(7.389 : ℝ))) := by
    linarith
  have h_final : (1/2 : ℝ) + (4/3 : ℝ) - 8/(9.8697 : ℝ) + (2.2976 : ℝ) + ((0.467425 : ℝ)/((9.8696 : ℝ)*(7.389 : ℝ))) ≤ (333/100 : ℝ) := by
    norm_num
  linarith

/-- The bound is nondecreasing in `|ρ_{T₁}|`: `u ↦ u² + log(k/(u+2)²)` on `[1, ∞)`. -/
theorem mono_u {k a u : ℝ} (hk : 0 < k) (ha : 1 ≤ a) (hau : a ≤ u) :
    a ^ 2 + log (k / (a + 2) ^ 2) ≤ u ^ 2 + log (k / (u + 2) ^ 2) := by
  have ha_pos : 0 < a + 2 := by linarith
  have hu_pos : 0 < u + 2 := by linarith
  have hdiv_pos : 0 < (u + 2) / (a + 2) := div_pos hu_pos ha_pos
  have h_nonneg : 0 ≤ u - a := by linarith
  have ha2_ge_3 : (3 : ℝ) ≤ a + 2 := by linarith
  -- simplify log terms: log(k / (x+2)²) = log k - 2*log(x+2)
  have hlog_a : log (k / (a + 2) ^ 2) = log k - 2 * log (a + 2) := by
    rw [Real.log_div (ne_of_gt hk) (by positivity), Real.log_pow, Nat.cast_ofNat]
  have hlog_u : log (k / (u + 2) ^ 2) = log k - 2 * log (u + 2) := by
    rw [Real.log_div (ne_of_gt hk) (by positivity), Real.log_pow, Nat.cast_ofNat]
  rw [hlog_a, hlog_u]
  -- goal: a² + (log k - 2*log(a+2)) ≤ u² + (log k - 2*log(u+2))
  -- cancel log k, rearrange to: 2*(log(u+2) - log(a+2)) ≤ u² - a²
  have hgoal : 2 * (log (u + 2) - log (a + 2)) ≤ u ^ 2 - a ^ 2 := by
    have hlog_div : log (u + 2) - log (a + 2) = log ((u + 2) / (a + 2)) := by
      rw [Real.log_div (ne_of_gt hu_pos) (ne_of_gt ha_pos)]
    rw [hlog_div]
    have hlog_bound : log ((u + 2) / (a + 2)) ≤ ((u + 2) / (a + 2)) - 1 :=
      Real.log_le_sub_one_of_pos hdiv_pos
    have h_simp : ((u + 2) / (a + 2)) - 1 = (u - a) / (a + 2) := by
      field_simp [ne_of_gt ha_pos]
      ring
    rw [h_simp] at hlog_bound
    have h_div_bound : (u - a) / (a + 2) ≤ (u - a) / 3 :=
      div_le_div_of_nonneg_left h_nonneg (by norm_num : 0 < (3 : ℝ)) ha2_ge_3
    have h_u2_minus_a2 : u ^ 2 - a ^ 2 = (u - a) * (u + a) := by ring
    rw [h_u2_minus_a2]
    have h_ua_sum : (2 : ℝ) ≤ u + a := by linarith
    nlinarith
  linarith

theorem two_log_a_add_two_le {T : ℕ} (hT : T0 ≤ T) :
    2 * log (√(level T) + 2) ≤ log (log T) + log 2 + 0.85 := by
  set L := level T with hL
  set a := √L with ha
  have hL_ge : 29/2 ≤ L := level_ge hT
  have hj0_pos : 1 ≤ j0 T := j0_pos hT
  have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
  have hL_nonneg : 0 ≤ L := by
    have : 0 ≤ 29/2 := by norm_num
    linarith
  -- a ≥ 3.8
  have ha_ge : 3.8 ≤ a := by
    have ha_sq_ge : 29/2 ≤ a ^ 2 := by
      rw [ha, Real.sq_sqrt hL_nonneg]
      exact hL_ge
    have h : (3.8 : ℝ)^2 ≤ 29/2 := by norm_num
    nlinarith
  have ha_pos : 0 < a := by linarith
  -- L ≤ 2 * log T
  have hL_le : L ≤ 2 * log (T : ℝ) := by
    rw [hL, level]
    have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    have hT_pos' : 0 < (T : ℝ) := by
      have : 0 < (T0 : ℝ) := by norm_num [T0]
      have hT_cast : (T0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      linarith
    have hj0 : (1 : ℝ) ≤ (j0 T : ℝ) := by exact_mod_cast hj0_pos
    have h_denom2_pos : 0 < (20 : ℝ) * exp 1 := by positivity
    have h_denom_le : (20 : ℝ) * exp 1 ≤ (20 : ℝ) * exp 1 * (j0 T : ℝ) := by
      nlinarith [exp_pos 1]
    have h_div_le : (T : ℝ) / ((20 : ℝ) * exp 1 * (j0 T : ℝ)) ≤ (T : ℝ) / ((20 : ℝ) * exp 1) :=
      div_le_div_of_nonneg_left hT_nonneg h_denom2_pos h_denom_le
    have h_div_pos : 0 < (T : ℝ) / ((20 : ℝ) * exp 1 * (j0 T : ℝ)) := by
      refine div_pos hT_pos' (by positivity)
    have h_div_pos2 : 0 < (T : ℝ) / ((20 : ℝ) * exp 1) := by
      refine div_pos hT_pos' (by positivity)
    have h_log_div_le : log ((T : ℝ) / ((20 : ℝ) * exp 1 * (j0 T : ℝ))) ≤ log ((T : ℝ) / ((20 : ℝ) * exp 1)) :=
      Real.log_le_log h_div_pos h_div_le
    have h_one_le_20exp1 : 1 ≤ (20 : ℝ) * exp 1 := by
      have h_exp1 : 1 ≤ Real.exp 1 := by
        have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (1 : ℝ)) 2
        have hsum : ∑ i ∈ Finset.range 2, ((1 : ℝ) ^ i / (i.factorial : ℝ)) = 2 := by norm_num
        linarith
      nlinarith
    have h_div_self : (T : ℝ) / ((20 : ℝ) * exp 1) ≤ (T : ℝ) :=
      div_le_self hT_nonneg h_one_le_20exp1
    have h_log_T_le : log ((T : ℝ) / ((20 : ℝ) * exp 1)) ≤ log (T : ℝ) :=
      Real.log_le_log h_div_pos2 h_div_self
    linarith
  -- 2 * log (29/19) ≤ 0.85
  have h_two_log_29_19_le_085 : 2 * log (29/19) ≤ 0.85 := by
    have h_sq : (29/19 : ℝ)^2 = 841/361 := by norm_num
    have h_exp_lower : (29/19 : ℝ)^2 ≤ Real.exp 0.85 := by
      rw [h_sq]
      have h_sum := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (0.85 : ℝ)) 7
      have h_sum_ge : (841/361 : ℝ) ≤ ∑ i ∈ Finset.range 7, ((0.85 : ℝ) ^ i / (i.factorial : ℝ)) := by
        simp [Finset.sum_range_succ]
        norm_num
      linarith
    have h_pos : 0 < 29/19 := by norm_num
    have h_log_le : log ((29/19 : ℝ)^2) ≤ log (Real.exp 0.85) :=
      Real.log_le_log (by positivity) h_exp_lower
    rw [Real.log_pow, Nat.cast_ofNat, Real.log_exp] at h_log_le
    exact h_log_le
  -- 1 + 2/a ≤ 29/19
  have h_ratio_bound : 1 + 2/a ≤ 29/19 := by
    have h_div : 2/a ≤ 2/3.8 := by
      have h_one_div : 1/a ≤ 1/(3.8 : ℝ) :=
        ((one_div_le_one_div ha_pos (by norm_num : 0 < (3.8 : ℝ))).mpr ha_ge)
      have := mul_le_mul_of_nonneg_right h_one_div (by norm_num : 0 ≤ (2 : ℝ))
      simpa [div_eq_mul_inv, mul_comm] using this
    have h_29_19 : 1 + 2/(3.8 : ℝ) = 29/19 := by norm_num
    linarith
  have hT_pos : 1 < (T : ℝ) := by
    have hT0_pos : 1 < (T0 : ℝ) := by norm_num [T0]
    have hT_cast : (T0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have h_log_T_pos : 0 < log (T : ℝ) := Real.log_pos hT_pos
  have h_log_2_T_pos : 0 < 2 * log (T : ℝ) := by positivity
  have h_log_2_T_ne_zero : 2 * log (T : ℝ) ≠ 0 := by linarith
  have h_one_plus_2a_pos : 0 < 1 + 2/a := by
    have : 0 < 2/a := div_pos (by norm_num) ha_pos
    linarith
  calc
    2 * log (√(level T) + 2) = 2 * log (a + 2) := by rw [ha]
    _ = 2 * (log a + log (1 + 2/a)) := by
      have h_add : a + 2 = a * (1 + 2/a) := by
        field_simp [ha_pos.ne']
      rw [h_add, Real.log_mul ha_pos.ne' (by linarith)]
    _ = 2 * log a + 2 * log (1 + 2/a) := by ring
    _ = log (a ^ 2) + 2 * log (1 + 2/a) := by
      rw [Real.log_pow, Nat.cast_ofNat]
    _ = log L + 2 * log (1 + 2/a) := by rw [ha, Real.sq_sqrt hL_nonneg]
    _ ≤ log L + 2 * log (29/19) := by
      apply add_le_add (le_refl (log L))
      refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ h_ratio_bound) (by norm_num)
      have : 0 < 2/a := div_pos (by norm_num) ha_pos
      linarith
    _ ≤ log (2 * log (T : ℝ)) + 2 * log (29/19) := by
      apply add_le_add (Real.log_le_log (by
        have : 0 < L := by linarith
        exact this) hL_le) (le_refl (2 * log (29/19)))
    _ = log (2 * log (T : ℝ)) + 2 * log (29/19) := rfl
    _ = (log 2 + log (log (T : ℝ))) + 2 * log (29/19) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith)]
    _ = log (log (T : ℝ)) + log 2 + 2 * log (29/19) := by ring
    _ ≤ log (log (T : ℝ)) + log 2 + 0.85 := by
      apply add_le_add (le_refl (log (log (T : ℝ)) + log 2)) h_two_log_29_19_le_085
    _ = log (log T) + log 2 + 0.85 := by simp

theorem small_k0 {T : ℕ} (hT : T0 ≤ T) : log (k0 T) / (2 * k0 T) + 1 / k0 T ≤ 1 / 10000 := by
  -- k0 T = T - T/2 ≥ T/2 ≥ 177856
  have hk0_ge_nat : 177856 ≤ k0 T := by
    have hhalf : 177856 ≤ T / 2 := by
      rw [Nat.le_div_two_iff_mul_two_le]
      have : 355712 ≤ T := by
        have hT0 : T0 ≤ T := hT
        unfold T0 at hT0
        omega
      omega
    have hk0_eq : k0 T = T - T / 2 := rfl
    rw [hk0_eq]
    omega
  have hk0_ge_real : (177856 : ℝ) ≤ (k0 T : ℝ) := by exact_mod_cast hk0_ge_nat
  have hpos_k0 : 0 < (k0 T : ℝ) := by
    have : 0 < (177856 : ℝ) := by norm_num
    linarith
  have hpos_177856 : 0 < (177856 : ℝ) := by norm_num
  -- exp 1 < 177856, so both k0 T and 177856 are in Ici (exp 1)
  have h_exp1_lt_177856 : Real.exp 1 < (177856 : ℝ) := by
    have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h' : (2.7182818286 : ℝ) < (177856 : ℝ) := by norm_num
    linarith
  have hmem_177856 : (177856 : ℝ) ∈ Set.Ici (Real.exp 1) :=
    Set.mem_Ici.mpr (by linarith)
  have hmem_k0 : (k0 T : ℝ) ∈ Set.Ici (Real.exp 1) :=
    Set.mem_Ici.mpr (by linarith)
  -- AntitoneOn: 177856 ≤ k0 T → log(k0 T)/(k0 T) ≤ log(177856)/177856
  have h_antitone : Real.log (k0 T : ℝ) / (k0 T : ℝ) ≤ Real.log (177856 : ℝ) / (177856 : ℝ) :=
    Real.log_div_self_antitoneOn hmem_177856 hmem_k0 hk0_ge_real
  -- Now we need to show log(177856) ≤ 13
  have h_log_le : Real.log (177856 : ℝ) ≤ (13 : ℝ) := by
    rw [Real.log_le_iff_le_exp hpos_177856]
    -- exp(13) = (exp 1)^13
    have h_exp_13 : Real.exp (13 : ℝ) = (Real.exp 1) ^ (13 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h_exp_13]
    -- exp 1 > 2.7182818283 > 27/10
    have h_exp1_gt : (27/10 : ℝ) < Real.exp 1 := by
      have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h_base : (27/10 : ℝ) < (2.7182818283 : ℝ) := by norm_num
      linarith
    have h_pow_lt : (27/10 : ℝ) ^ (13 : ℕ) < (Real.exp 1) ^ (13 : ℕ) :=
      pow_lt_pow_left₀ h_exp1_gt (by norm_num) (by norm_num : (13 : ℕ) ≠ 0)
    -- Now we need: 177856 ≤ (27/10)^13
    -- i.e., 177856 * 10^13 ≤ 27^13
    have h_num : (177856 : ℕ) * (10 : ℕ) ^ (13 : ℕ) ≤ (27 : ℕ) ^ (13 : ℕ) := by
      norm_num
    have h_num' : (177856 : ℝ) * ((10 : ℝ) ^ (13 : ℕ)) ≤ ((27 : ℝ) ^ (13 : ℕ)) := by
      exact_mod_cast h_num
    have h_bound : (177856 : ℝ) ≤ (27/10 : ℝ) ^ (13 : ℕ) := by
      -- (27/10)^13 = 27^13 / 10^13
      -- So 177856 ≤ 27^13 / 10^13 ↔ 177856 * 10^13 ≤ 27^13
      calc
        (177856 : ℝ) = ((177856 : ℝ) * ((10 : ℝ) ^ (13 : ℕ))) / ((10 : ℝ) ^ (13 : ℕ)) := by
          field_simp
        _ ≤ ((27 : ℝ) ^ (13 : ℕ)) / ((10 : ℝ) ^ (13 : ℕ)) := by
          refine (div_le_div_of_nonneg_right h_num' (by positivity))
        _ = (27/10 : ℝ) ^ (13 : ℕ) := by ring
    calc
      (177856 : ℝ) ≤ (27/10 : ℝ) ^ (13 : ℕ) := h_bound
      _ ≤ (Real.exp 1) ^ (13 : ℕ) := h_pow_lt.le
  -- Now combine the antitone bound with the log bound
  have h_main : Real.log (k0 T : ℝ) / (2 * (k0 T : ℝ)) + 1 / (k0 T : ℝ) ≤
      Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) + 1 / (177856 : ℝ) := by
    have h1 : Real.log (k0 T : ℝ) / (2 * (k0 T : ℝ)) ≤ Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) := by
      calc
        Real.log (k0 T : ℝ) / (2 * (k0 T : ℝ)) = (Real.log (k0 T : ℝ) / (k0 T : ℝ)) / 2 := by ring
        _ ≤ (Real.log (177856 : ℝ) / (177856 : ℝ)) / 2 :=
          div_le_div_of_nonneg_right h_antitone (by norm_num)
        _ = Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) := by ring
    have h2 : 1 / (k0 T : ℝ) ≤ 1 / (177856 : ℝ) :=
      (one_div_le_one_div hpos_k0 hpos_177856).mpr hk0_ge_real
    linarith
  -- Now we need to show RHS ≤ 1/10000
  have h_final : Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) + 1 / (177856 : ℝ) ≤ 1 / 10000 := by
    have h_log_bound : Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) ≤ (13 : ℝ) / (2 * (177856 : ℝ)) :=
      div_le_div_of_nonneg_right h_log_le (by positivity)
    calc
      Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) + 1 / (177856 : ℝ) ≤
          (13 : ℝ) / (2 * (177856 : ℝ)) + 1 / (177856 : ℝ) := by nlinarith
      _ = ((13 : ℝ) + 2) / (2 * (177856 : ℝ)) := by ring
      _ = (15 : ℝ) / (355712 : ℝ) := by norm_num
      _ ≤ 1 / 10000 := by
        -- 15/355712 ≤ 1/10000 ↔ 15*10000 ≤ 355712 ↔ 150000 ≤ 355712
        have h : (15 : ℝ) * 10000 ≤ (355712 : ℝ) := by norm_num
        field_simp
        nlinarith
  -- Combine
  calc
    Real.log (k0 T : ℝ) / (2 * (k0 T : ℝ)) + 1 / (k0 T : ℝ) ≤
        Real.log (177856 : ℝ) / (2 * (177856 : ℝ)) + 1 / (177856 : ℝ) := h_main
    _ ≤ 1 / 10000 := h_final

theorem const_le : 2 * log (20 * exp 1) + 2 * log 2 + 0.85 + 3.33 + 1 / 10000 ≤ 13.59 := by
  have hlog2 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog5 : log 5 ≤ 1.61 := by
    have hpos : (0 : ℝ) ≤ 1.61 := by norm_num
    have hsum : (5 : ℝ) ≤ ∑ i ∈ Finset.range 15, ((1.61 : ℝ) ^ i / (i.factorial : ℝ)) := by
      norm_num
    have hle : ∑ i ∈ Finset.range 15, ((1.61 : ℝ) ^ i / (i.factorial : ℝ)) ≤ Real.exp (1.61 : ℝ) :=
      Real.sum_le_exp_of_nonneg hpos 15
    have h5leexp : (5 : ℝ) ≤ Real.exp (1.61 : ℝ) := le_trans hsum hle
    calc
      log 5 ≤ log (Real.exp (1.61 : ℝ)) := Real.log_le_log (by norm_num : 0 < (5 : ℝ)) h5leexp
      _ = 1.61 := Real.log_exp _
  have hlog20 : log (20 * exp 1) = 2 * log 2 + log 5 + 1 := by
    calc
      log (20 * exp 1) = log 20 + log (exp 1) := Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) (Real.exp_pos 1).ne'
      _ = log 20 + 1 := by rw [Real.log_exp 1]
      _ = log (4 * 5) + 1 := by norm_num
      _ = (log 4 + log 5) + 1 := by rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
      _ = (log ((2:ℝ)^2) + log 5) + 1 := by norm_num
      _ = (2 * log 2 + log 5) + 1 := by rw [Real.log_pow, Nat.cast_ofNat]
      _ = 2 * log 2 + log 5 + 1 := by ring
  rw [hlog20]
  have hcalc : 2 * (2 * log 2 + log 5 + 1) + 2 * log 2 + 0.85 + 3.33 + 1 / 10000 < 13.59 := by
    linarith
  linarith

theorem B0_ge {T : ℕ} (hT : T0 ≤ T) :
    3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 13.6 ≤ B0 T := by
  set u := log (T : ℝ) with hu
  set L := level T with hL
  set k := k0 T with hk
  set j := j0 T with hj
  have hposT : 0 < (T : ℝ) := by
    have hT0pos : 0 < (T0 : ℝ) := by norm_num [T0]
    exact hT0pos.trans_le (by exact_mod_cast hT)
  have hu_pos : 1 < u := by
    rw [hu]
    have h_exp_one_lt_T : Real.exp 1 < (T : ℝ) := by
      have h_exp_one_lt_T0 : Real.exp 1 < (T0 : ℝ) := by
        have h_exp_one_lt_355713 : Real.exp 1 < 355713 := by
          have : Real.exp 1 < 3 := Real.exp_one_lt_three
          linarith
        norm_num [T0]
        linarith
      exact h_exp_one_lt_T0.trans_le (by exact_mod_cast hT)
    have h_log_exp_one_lt_log_T : log (Real.exp 1) < log (T : ℝ) :=
      Real.log_lt_log (Real.exp_pos 1) h_exp_one_lt_T
    rw [Real.log_exp 1] at h_log_exp_one_lt_log_T
    exact h_log_exp_one_lt_log_T
  have hj_pos : 1 ≤ j := j0_pos hT
  have hj_pos' : 0 < (j : ℝ) := by
    have : 1 ≤ (j : ℝ) := by exact_mod_cast hj_pos
    linarith
  have hj_le : (j : ℝ) ≤ log u + 2.1 := j0_le hT
  have h_two_log_sqrtL : 2 * log (√(L) + 2) ≤ log u + log 2 + 0.85 := two_log_a_add_two_le hT
  have h_small_k : log (k : ℝ) / (2 * (k : ℝ)) + 1 / (k : ℝ) ≤ 1 / 10000 := small_k0 hT
  have h_c1_le : c1 ≤ 333 / 100 := c1_le
  have h_const_le : 2 * log (20 * Real.exp 1) + 2 * log 2 + 0.85 + 3.33 + 1 / 10000 ≤ 13.59 := const_le
  have h_const_le' : 2 * log (20 * Real.exp 1) + 2 * log 2 + 0.85 + 3.33 + 1 / 10000 ≤ 13.6 := by
    linarith
  have hposk : 0 < (k : ℝ) := by
    have hk_pos_nat : 0 < k0 T := by
      dsimp [k0, T1]
      have hTpos_nat : 0 < T := by
        have hT0pos_nat : 0 < T0 := by norm_num [T0]
        exact hT0pos_nat.trans_le hT
      omega
    exact_mod_cast hk_pos_nat
  have h_level_eq : L = 2 * u - 2 * log (20 * Real.exp 1) - 2 * log (j : ℝ) := by
    dsimp [L, level, j]
    have hpos_20e : 0 < 20 * Real.exp 1 := by positivity
    have hpos_j0 : 0 < ((j0 T : ℕ) : ℝ) := by
      have hpos_nat : 0 < j0 T := by
        have h := j0_pos hT
        omega
      exact_mod_cast hpos_nat
    rw [Real.log_div (ne_of_gt hposT) (by positivity : 20 * Real.exp 1 * ((j0 T : ℕ) : ℝ) ≠ 0)]
    rw [Real.log_mul (ne_of_gt hpos_20e) (ne_of_gt hpos_j0)]
    ring
  have h_log_k_ge : u - log 2 ≤ log (k : ℝ) := by
    have hk_ge : (T : ℝ) / 2 ≤ (k : ℝ) := by
      dsimp [k]
      have h_floor : ((T / 2 : ℕ) : ℝ) ≤ (T : ℝ) / 2 := Nat.cast_div_le
      have h_sub : (T : ℝ) - ((T / 2 : ℕ) : ℝ) ≥ (T : ℝ) / 2 := by linarith
      have h_k0_le : (k0 T : ℝ) = (T : ℝ) - ((T / 2 : ℕ) : ℝ) := by
        dsimp [k0, T1]
        have h_le : T / 2 ≤ T := Nat.div_le_self T 2
        rw [Nat.cast_sub h_le]
      rw [h_k0_le]
      exact h_sub
    have h_log_T_div_two : log ((T : ℝ) / 2) = u - log 2 := by
      rw [hu, Real.log_div (ne_of_gt hposT) (by norm_num : (2 : ℝ) ≠ 0)]
    have h_log_le : log ((T : ℝ) / 2) ≤ log (k : ℝ) :=
      Real.log_le_log (by positivity) hk_ge
    rw [h_log_T_div_two] at h_log_le
    exact h_log_le
  unfold B0
  rw [← hL, ← hk]
  rw [h_level_eq]
  -- Now the goal has L replaced by its expansion, but we need to rewrite the log term
  -- The goal is: 3*u - log u - 2*log(log u + 2.1) - 13.6 ≤
  --   (2*u - 2*log(20*e) - 2*log j) + log(k/(√(2*u - 2*log(20*e) - 2*log j) + 2)^2) - c1 - log k/(2*k) - 1/k
  have h_log_term : log ((k : ℝ) / ((√(2 * u - 2 * log (20 * Real.exp 1) - 2 * log (j : ℝ))) + 2) ^ 2) =
      log (k : ℝ) - 2 * log (√(2 * u - 2 * log (20 * Real.exp 1) - 2 * log (j : ℝ)) + 2) := by
    rw [Real.log_div (ne_of_gt hposk) (by positivity : (√(2 * u - 2 * log (20 * Real.exp 1) - 2 * log (j : ℝ)) + 2) ^ 2 ≠ 0)]
    rw [Real.log_pow, Nat.cast_ofNat]
  rw [h_log_term]
  -- Now the goal is: 3*u - log u - 2*log(log u + 2.1) - 13.6 ≤
  --   (2*u - 2*log(20*e) - 2*log j) + (log k - 2*log(√(...) + 2)) - c1 - log k/(2*k) - 1/k
  -- But the √(...) contains the expanded form, not L. We need to rewrite it back to L.
  rw [← h_level_eq]
  -- Now the goal is: 3*u - log u - 2*log(log u + 2.1) - 13.6 ≤
  --   (2*u - 2*log(20*e) - 2*log j) + (log k - 2*log(√L + 2)) - c1 - log k/(2*k) - 1/k
  have h_main : (2 * u - 2 * log (20 * Real.exp 1) - 2 * log (j : ℝ)) + (log (k : ℝ) - 2 * log (√L + 2)) - c1 - log (k : ℝ) / (2 * (k : ℝ)) - 1 / (k : ℝ)
      ≥ 3 * u - log u - 2 * log (log u + 2.1) - (2 * log (20 * Real.exp 1) + 2 * log 2 + 0.85 + 333/100 + 1/10000) := by
    have h_log_k_ge' : log (k : ℝ) ≥ u - log 2 := h_log_k_ge
    have h_sqrtL_le : -2 * log (√L + 2) ≥ -(log u + log 2 + 0.85) := by linarith
    have h_j_le : -2 * log (j : ℝ) ≥ -2 * log (log u + 2.1) := by
      have h_log_j_le : log (j : ℝ) ≤ log (log u + 2.1) :=
        Real.log_le_log hj_pos' hj_le
      linarith
    have h_c1_le' : -c1 ≥ -(333/100 : ℝ) := by linarith
    have h_k_small : -log (k : ℝ) / (2 * (k : ℝ)) - 1 / (k : ℝ) ≥ -(1/10000) := by
      have h := h_small_k
      calc
        -log (k : ℝ) / (2 * (k : ℝ)) - 1 / (k : ℝ) = -(log (k : ℝ) / (2 * (k : ℝ)) + 1 / (k : ℝ)) := by ring
        _ ≥ -(1/10000) := by linarith
    linarith
  have h_const_term : 2 * log (20 * Real.exp 1) + 2 * log 2 + 0.85 + 333/100 + 1/10000 ≤ 13.6 := by
    -- This is h_const_le' but with 333/100 instead of 3.33
    -- Actually h_const_le' already has 3.33, which is 333/100
    -- So we can just use h_const_le'
    -- But h_const_le' has 3.33, not 333/100
    -- Let me rewrite
    have : (333/100 : ℝ) = 3.33 := by norm_num
    rw [this]
    exact h_const_le'
  linarith

theorem bT_ge {T : ℕ} (hT : T0 ≤ T) : B0 T - 1 ≤ bT T := by
  have hj0 : 1 ≤ j0 T := j0_pos hT
  have hT_one_lt : 1 < (T : ℝ) := by
    have : 1 < T0 := by unfold T0; omega
    have hT0 : (1 : ℕ) < T := by omega
    exact_mod_cast hT0
  have hlogTpos : 0 < log (T : ℝ) := Real.log_pos hT_one_lt
  have h3logTpos : 0 < 3 * log (T : ℝ) := by nlinarith
  have hk0pos_nat : 0 < k0 T := by
    unfold k0 T1
    have hTpos' : 0 < T := by
      have : 0 < T0 := by unfold T0; omega
      omega
    have hhalf : T / 2 < T := Nat.div_lt_self hTpos' (by omega)
    have : 0 < T - T / 2 := by omega
    exact this
  have hk0pos : 0 < (k0 T : ℝ) := by exact_mod_cast hk0pos_nat
  have hk0leT : (k0 T : ℝ) ≤ (T : ℝ) := by
    unfold k0 T1
    have h : (T : ℕ) / 2 ≤ T := Nat.div_le_self _ _
    have h' : (T : ℕ) - (T : ℕ) / 2 ≤ (T : ℕ) := by omega
    exact_mod_cast h'
  -- Key inequality: exp(-j0) * B0 ≤ 1
  have hkey : exp (-(j0 T : ℝ)) * B0 T ≤ 1 := by
    by_cases hB0 : B0 T ≤ 0
    · have hpos : 0 ≤ exp (-(j0 T : ℝ)) := Real.exp_pos _ |>.le
      nlinarith
    · have hB0pos : 0 < B0 T := by linarith
      -- Show B0 T ≤ 3 * log T
      have hB0le : B0 T ≤ 3 * log (T : ℝ) := by
        have hlevel : level T ≤ 2 * log (T : ℝ) := by
          unfold level
          have hdiv : (T : ℝ) / (20 * exp 1 * (j0 T : ℝ)) ≤ (T : ℝ) := by
            have hden : 1 ≤ 20 * exp 1 * (j0 T : ℝ) := by
              have hj0' : (1 : ℝ) ≤ (j0 T : ℝ) := by exact_mod_cast hj0
              have hexp_gt_two : 2 < exp 1 := Real.exp_one_gt_two
              nlinarith
            calc
              (T : ℝ) / (20 * exp 1 * (j0 T : ℝ)) ≤ (T : ℝ) / 1 :=
                div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
              _ = (T : ℝ) := by simp
          calc
            2 * log ((T : ℝ) / (20 * exp 1 * (j0 T : ℝ))) ≤ 2 * log (T : ℝ) := by
              nlinarith [Real.log_le_log (by positivity) hdiv]
            _ = 2 * log (T : ℝ) := rfl
        have hlogk0 : log ((k0 T : ℝ) / ((√(level T) + 2) ^ 2)) ≤ log (T : ℝ) := by
          refine Real.log_le_log (by positivity) ?_
          have hsq_ge_one : 1 ≤ (√(level T) + 2) ^ 2 := by
            have hsq_nonneg : 0 ≤ √(level T) := Real.sqrt_nonneg _
            nlinarith
          calc
            (k0 T : ℝ) / ((√(level T) + 2) ^ 2) ≤ (k0 T : ℝ) / 1 :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq_ge_one
            _ = (k0 T : ℝ) := by simp
            _ ≤ (T : ℝ) := hk0leT
        have hc1_nonneg : 0 ≤ c1 := by
          unfold c1 Jc
          have hπgt3 : 3 < π := Real.pi_gt_three
          have hπsq_gt_9 : 9 < π ^ 2 := by nlinarith
          have h_first_part_pos : 0 < 1/2 + 4/3 - 8/π ^ 2 := by
            have : (11 : ℝ) / 6 - 8 / π ^ 2 > 0 := by
              have h : (48 : ℝ) / 11 < π ^ 2 := by nlinarith
              field_simp
              nlinarith
            nlinarith
          have hlogπsq_pos : 0 < log (π ^ 2) := Real.log_pos (by nlinarith)
          have h_last_part_pos : 0 < (π ^ 2 / 4 - 2) / (π ^ 2 * exp 2) := by
            refine div_pos ?_ (by positivity)
            nlinarith
          nlinarith
        have hlogk0_nonneg : 0 ≤ log (k0 T : ℝ) / (2 * (k0 T : ℝ)) := by
          have hlog : 0 ≤ log (k0 T : ℝ) := Real.log_nonneg (by exact_mod_cast hk0pos_nat)
          positivity
        have hone_over_k0_nonneg : 0 ≤ 1 / (k0 T : ℝ) := by positivity
        unfold B0
        linarith
      -- Show 3 * log T ≤ exp(j0 T)
      have hexp_ge : 3 * log (T : ℝ) ≤ exp (j0 T : ℝ) := by
        have hceil : log (3 * log (T : ℝ)) ≤ (j0 T : ℝ) :=
          (Nat.ceil_le (a := log (3 * log (T : ℝ))) (n := j0 T)).mp (by
            -- ⌈log(3*log T)⌉₊ = j0 T by definition, so ⌈...⌉₊ ≤ j0 T is rfl
            rfl)
        calc
          3 * log (T : ℝ) = exp (log (3 * log (T : ℝ))) := by
            rw [Real.exp_log h3logTpos]
          _ ≤ exp (j0 T : ℝ) := Real.exp_le_exp.mpr hceil
      -- Combine: exp(-j0) * B0 ≤ exp(-j0) * (3 log T) ≤ exp(-j0) * exp(j0) = 1
      have hexp_nonneg : 0 ≤ exp (-(j0 T : ℝ)) := Real.exp_pos _ |>.le
      calc
        exp (-(j0 T : ℝ)) * B0 T ≤ exp (-(j0 T : ℝ)) * (3 * log (T : ℝ)) := by
          nlinarith
        _ ≤ exp (-(j0 T : ℝ)) * exp (j0 T : ℝ) := by
          nlinarith
        _ = exp ((-(j0 T : ℝ)) + (j0 T : ℝ)) := by rw [Real.exp_add]
        _ = exp 0 := by simp
        _ = 1 := by simp
  -- Now use hkey to prove the goal
  have hbT_eq : bT T = (1 - exp (-(j0 T : ℝ))) * B0 T := rfl
  rw [hbT_eq]
  nlinarith

set_option maxHeartbeats 400000 in
theorem simplified_two {T : ℕ} (hT : T0 ≤ T) :
    3 * log T - 2 * log (log T) - 15.2 ≤
      3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 14.6 := by
  set z := log (log (T : ℝ)) with hz
  have hT' : (T0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hT0_pos : 0 < (T0 : ℝ) := by norm_num [T0]
  have hT_pos : 0 < (T : ℝ) := by linarith
  have hlogT_pos : 0 < log (T : ℝ) := Real.log_pos (by
    have : (1 : ℝ) < (T0 : ℝ) := by norm_num [T0]
    linarith)
  have hz_lower : 2.5 ≤ z := by
    -- First, prove exp(0.19) < 1.21 using Real.exp_bound
    have h_exp019_lt : Real.exp (0.19 : ℝ) < 1.21 := by
      have hx : |(0.19 : ℝ)| ≤ 1 := by
        rw [abs_of_pos (by norm_num : 0 < (0.19 : ℝ))]
        norm_num
      have hn : 0 < 5 := by norm_num
      have h_bound := Real.exp_bound hx hn
      have h_abs_le : Real.exp (0.19 : ℝ) ≤
          (∑ m ∈ Finset.range 5, (0.19 : ℝ) ^ m / (m.factorial : ℝ)) +
          |(0.19 : ℝ)| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) := by
        have h := abs_sub_le_iff.mp h_bound
        rcases h with ⟨h_left, h_right⟩
        linarith
      have h_sum_lt : (∑ m ∈ Finset.range 5, (0.19 : ℝ) ^ m / (m.factorial : ℝ)) +
          |(0.19 : ℝ)| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5)) < 1.21 := by
        norm_num
      linarith
    -- Now prove exp(12.19) < 355713
    have h_exp12_19_lt : Real.exp (12.19 : ℝ) < (T0 : ℝ) := by
      have h_exp1_lt : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
      have h_exp12_eq : Real.exp (12 : ℝ) = Real.exp (1 : ℝ) ^ 12 := by
        calc
          Real.exp (12 : ℝ) = Real.exp ((12 : ℕ) * (1 : ℝ)) := by ring_nf
          _ = Real.exp (1 : ℝ) ^ 12 := by rw [Real.exp_nat_mul]
      have h_exp12_19_eq : Real.exp (12.19 : ℝ) = Real.exp (12 : ℝ) * Real.exp (0.19 : ℝ) := by
        rw [← Real.exp_add]
        ring_nf
      rw [h_exp12_19_eq, h_exp12_eq]
      have h_pow : Real.exp (1 : ℝ) ^ 12 < (2.7182818286 : ℝ) ^ 12 := by
        gcongr
      have h_prod : Real.exp (1 : ℝ) ^ 12 * Real.exp (0.19 : ℝ) < (2.7182818286 : ℝ) ^ 12 * (1.21 : ℝ) := by
        have h_pos_pow : 0 < Real.exp (1 : ℝ) ^ 12 := by positivity
        nlinarith
      have h_final : (2.7182818286 : ℝ) ^ 12 * (1.21 : ℝ) < (T0 : ℝ) := by
        unfold T0
        norm_num
      linarith
    -- From hT' : (T0 : ℝ) ≤ (T : ℝ), we get log(T) ≥ log(T0)
    have h_logT_ge : 12.19 ≤ log (T : ℝ) := by
      have h_logT0_ge : 12.19 ≤ log (T0 : ℝ) := by
        rw [← Real.log_exp (12.19 : ℝ)]
        exact Real.log_le_log (Real.exp_pos _) h_exp12_19_lt.le
      have h_log_mono : log (T0 : ℝ) ≤ log (T : ℝ) :=
        Real.log_le_log (by exact_mod_cast hT0_pos) hT'
      linarith
    -- Now prove exp(2.5) ≤ 12.19
    have h_exp25_le : Real.exp (2.5 : ℝ) ≤ 12.19 := by
      have h_exp1_lt : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
      have h_exp2_lt : Real.exp (2 : ℝ) < 7.3891 := by
        have h_eq : Real.exp (2 : ℝ) = Real.exp (1 : ℝ) ^ 2 := by
          calc
            Real.exp (2 : ℝ) = Real.exp ((2 : ℕ) * (1 : ℝ)) := by ring_nf
            _ = Real.exp (1 : ℝ) ^ 2 := by rw [Real.exp_nat_mul]
        rw [h_eq]
        have h_sq : Real.exp (1 : ℝ) ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
          have h_pos : 0 ≤ Real.exp (1 : ℝ) := by positivity
          nlinarith
        have h_sq_lt : (2.7182818286 : ℝ) ^ 2 < 7.3891 := by norm_num
        linarith
      have h_exp_half_sq_eq : Real.exp (0.5 : ℝ) ^ 2 = Real.exp (1 : ℝ) := by
        calc
          Real.exp (0.5 : ℝ) ^ 2 = Real.exp (0.5 : ℝ) * Real.exp (0.5 : ℝ) := by ring
          _ = Real.exp ((0.5 : ℝ) + (0.5 : ℝ)) := by rw [Real.exp_add]
          _ = Real.exp (1 : ℝ) := by ring_nf
      have h_exp_half_lt : Real.exp (0.5 : ℝ) < 1.6488 := by
        have h_sq_lt : Real.exp (0.5 : ℝ) ^ 2 < (1.6488 : ℝ) ^ 2 := by
          rw [h_exp_half_sq_eq]
          have h : Real.exp (1 : ℝ) < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
          have h' : (2.7182818286 : ℝ) < (1.6488 : ℝ) ^ 2 := by norm_num
          linarith
        have h_pos : 0 < Real.exp (0.5 : ℝ) := Real.exp_pos _
        nlinarith
      have h_exp25_eq : Real.exp (2.5 : ℝ) = Real.exp (2 : ℝ) * Real.exp (0.5 : ℝ) := by
        rw [← Real.exp_add]
        ring_nf
      rw [h_exp25_eq]
      have h_prod : Real.exp (2 : ℝ) * Real.exp (0.5 : ℝ) < 7.3891 * 1.6488 := by
        have h_pos2 : 0 ≤ Real.exp (2 : ℝ) := by positivity
        have h_pos_half : 0 ≤ Real.exp (0.5 : ℝ) := by positivity
        nlinarith
      have h_73891_mul : (7.3891 : ℝ) * (1.6488 : ℝ) ≤ (12.19 : ℝ) := by
        norm_num
      linarith
    -- Now: z = log(log T) ≥ log(12.19) ≥ log(exp(2.5)) = 2.5
    rw [hz]
    have h_log_logT_ge : 2.5 ≤ log (log (T : ℝ)) := by
      have h_log_ge_exp25 : Real.exp (2.5 : ℝ) ≤ log (T : ℝ) := by
        linarith
      have h_pos_exp25 : 0 < Real.exp (2.5 : ℝ) := Real.exp_pos _
      have h_log_ge : Real.log (Real.exp (2.5 : ℝ)) ≤ Real.log (log (T : ℝ)) :=
        Real.log_le_log h_pos_exp25 h_log_ge_exp25
      rw [Real.log_exp (2.5 : ℝ)] at h_log_ge
      exact h_log_ge
    exact h_log_logT_ge
  have h_main : 2 * Real.log (z + 2.1) ≤ z + 0.6 := by
    have hz_pos : 0 < z + 2.1 := by linarith
    -- Use log(z+2.1) = log(4.6 * ((z+2.1)/4.6)) = log 4.6 + log((z+2.1)/4.6)
    have h_log_bound : Real.log (z + 2.1) ≤ Real.log 4.6 + (z - 2.5) / 4.6 := by
      have h_eq : Real.log (z + 2.1) = Real.log 4.6 + Real.log ((z + 2.1) / 4.6) := by
        calc
          Real.log (z + 2.1) = Real.log (4.6 * ((z + 2.1) / 4.6)) := by
            field_simp
          _ = Real.log 4.6 + Real.log ((z + 2.1) / 4.6) := by
            rw [Real.log_mul (by norm_num : (4.6 : ℝ) ≠ 0) (by
              have : 0 < z + 2.1 := hz_pos
              positivity)]
      rw [h_eq]
      have h_log_le : Real.log ((z + 2.1) / 4.6) ≤ ((z + 2.1) / 4.6) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity : 0 < (z + 2.1) / 4.6)
      -- Note: ((z + 2.1) / 4.6) - 1 = (z - 2.5) / 4.6
      have h_simp : ((z + 2.1) / 4.6) - 1 = (z - 2.5) / 4.6 := by ring
      rw [h_simp] at h_log_le
      linarith
    -- Prove 2 * log 4.6 ≤ 3.1
    have h_log46_bound : 2 * Real.log 4.6 ≤ 3.1 := by
      have h_exp31_gt : (21.16 : ℝ) < Real.exp (3.1 : ℝ) := by
        have h_exp1_gt : (2.7182818283 : ℝ) < Real.exp (1 : ℝ) := Real.exp_one_gt_d9
        have h_exp01_ge : (1.1 : ℝ) ≤ Real.exp (0.1 : ℝ) := by
          have h := Real.add_one_le_exp (0.1 : ℝ)
          linarith
        have h_bound : (21.16 : ℝ) < (2.7182818283 : ℝ) ^ 3 * (1.1 : ℝ) := by norm_num
        have h_exp3 : Real.exp (3.1 : ℝ) = Real.exp (1 : ℝ) ^ 3 * Real.exp (0.1 : ℝ) := by
          calc
            Real.exp (3.1 : ℝ) = Real.exp ((3 : ℝ) + (0.1 : ℝ)) := by ring_nf
            _ = Real.exp (3 : ℝ) * Real.exp (0.1 : ℝ) := by rw [Real.exp_add]
            _ = Real.exp ((1 : ℝ) + (1 : ℝ) + (1 : ℝ)) * Real.exp (0.1 : ℝ) := by ring_nf
            _ = (Real.exp (1 : ℝ) * Real.exp (1 : ℝ) * Real.exp (1 : ℝ)) * Real.exp (0.1 : ℝ) := by
              simp [Real.exp_add]
            _ = Real.exp (1 : ℝ) ^ 3 * Real.exp (0.1 : ℝ) := by ring
        rw [h_exp3]
        have h_pos_cube : 0 < Real.exp (1 : ℝ) ^ 3 := by positivity
        have h_pos_01 : 0 < Real.exp (0.1 : ℝ) := Real.exp_pos _
        have h_prod : (2.7182818283 : ℝ) ^ 3 * (1.1 : ℝ) < Real.exp (1 : ℝ) ^ 3 * Real.exp (0.1 : ℝ) := by
          have h_cube : (2.7182818283 : ℝ) ^ 3 < Real.exp (1 : ℝ) ^ 3 := by
            have h_sq : (2.7182818283 : ℝ) ^ 2 < Real.exp (1 : ℝ) ^ 2 := by
              nlinarith
            nlinarith
          nlinarith
        linarith
      -- 2*log 4.6 ≤ 3.1 ↔ log(4.6^2) ≤ 3.1 ↔ 21.16 ≤ exp(3.1)
      have h_log_sq : Real.log ((4.6 : ℝ) ^ 2) = 2 * Real.log 4.6 := by
        rw [Real.log_pow, Nat.cast_ofNat]
      rw [← h_log_sq]
      have h_46sq_eq : (4.6 : ℝ) ^ 2 = (21.16 : ℝ) := by norm_num
      rw [h_46sq_eq]
      have h_sq_pos : 0 < (21.16 : ℝ) := by norm_num
      have h_log_le : Real.log (21.16 : ℝ) ≤ Real.log (Real.exp (3.1 : ℝ)) :=
        Real.log_le_log (by norm_num) h_exp31_gt.le
      rw [Real.log_exp (3.1 : ℝ)] at h_log_le
      exact h_log_le
    calc
      2 * Real.log (z + 2.1) ≤ 2 * (Real.log 4.6 + (z - 2.5) / 4.6) := by gcongr
      _ = 2 * Real.log 4.6 + (z - 2.5) * (2 / 4.6) := by ring
      _ ≤ 2 * Real.log 4.6 + (z - 2.5) := by
        have h_ratio : (2 : ℝ) / 4.6 ≤ 1 := by norm_num
        have h_nonneg : 0 ≤ z - 2.5 := by linarith
        nlinarith
      _ ≤ 3.1 + (z - 2.5) := by nlinarith
      _ = z + 0.6 := by ring
  -- Now rearrange the original inequality
  -- The goal uses `log T` where T : ℕ, but our lemmas use (T : ℝ)
  -- `log T` where T : ℕ is automatically cast to ℝ
  nlinarith

theorem lowerSharpSimplified : LowerSharpSimplified := fun T hT =>
  ⟨by linarith [B0_ge hT, bT_ge hT], simplified_two hT⟩

end RegretKappa.LowerSharp
