import Mathlib

/-!
# The weights of `TheoremB`

The real inequalities behind the weights `b_t = 1/log(t + 1) - 1/log(t + 2)` of `TheoremB`, in
0-indexed rounds
(`wB t = 1/log(t + 2) - 1/log(t + 3)` is the weight of
round `t`): positivity, monotonicity (AM-HM), the lower bound `b_T ≥ 1/((T + 2) log² (T + 2))`, the
lower bound of the level `λ_t ≥ 3 (t + 2) log(t + 2)`, the terminal condition of `theoremA`, the
constant `K ≤ 1.3706`, and the log algebra of the closed form.
-/

namespace RegretKappa.UnknownBT

open Real Filter Topology

theorem wB_pos (t : ℕ) : 0 < 1 / Real.log ((t : ℝ) + 2) - 1 / Real.log ((t : ℝ) + 3) := by
  have ht_nonneg : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hpos2 : 0 < (t : ℝ) + 2 := by linarith
  have hpos3 : 0 < (t : ℝ) + 3 := by linarith
  have hone_lt_2 : 1 < (t : ℝ) + 2 := by linarith
  have ha_pos : 0 < Real.log ((t : ℝ) + 2) := Real.log_pos hone_lt_2
  have ha_lt_b : Real.log ((t : ℝ) + 2) < Real.log ((t : ℝ) + 3) :=
    Real.log_lt_log hpos2 (by linarith)
  have h_one_div_lt : 1 / Real.log ((t : ℝ) + 3) < 1 / Real.log ((t : ℝ) + 2) :=
    ((one_div_lt_one_div (by linarith) ha_pos).mpr ha_lt_b)
  exact sub_pos.mpr h_one_div_lt


theorem wB_antitone (t : ℕ) :
    1 / Real.log ((t : ℝ) + 3) - 1 / Real.log ((t : ℝ) + 4) ≤
      1 / Real.log ((t : ℝ) + 2) - 1 / Real.log ((t : ℝ) + 3) := by
  set L1 := Real.log ((t : ℝ) + 2) with hL1
  set L2 := Real.log ((t : ℝ) + 3) with hL2
  set L3 := Real.log ((t : ℝ) + 4) with hL3
  have ht_nonneg : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hpos1 : 0 < L1 := by
    rw [hL1]
    exact Real.log_pos (by nlinarith)
  have hpos2 : 0 < L2 := by
    rw [hL2]
    exact Real.log_pos (by nlinarith)
  have hpos3 : 0 < L3 := by
    rw [hL3]
    exact Real.log_pos (by nlinarith)
  -- (t+2)(t+4) = (t+3)² - 1 ≤ (t+3)²
  have hprod_le : ((t : ℝ) + 2) * ((t : ℝ) + 4) ≤ ((t : ℝ) + 3) ^ 2 := by
    nlinarith
  -- Therefore L1 + L3 ≤ 2*L2
  have hsum_le : L1 + L3 ≤ 2 * L2 := by
    rw [hL1, hL2, hL3]
    calc
      Real.log ((t : ℝ) + 2) + Real.log ((t : ℝ) + 4) = Real.log (((t : ℝ) + 2) * ((t : ℝ) + 4)) := by
        rw [Real.log_mul (by nlinarith) (by nlinarith)]
      _ ≤ Real.log (((t : ℝ) + 3) ^ 2) :=
        Real.log_le_log (by nlinarith) hprod_le
      _ = 2 * Real.log ((t : ℝ) + 3) := by
        rw [Real.log_pow, Nat.cast_ofNat]
  -- Goal: 2*L1*L3 ≤ L2*(L1+L3)
  -- From hsum_le: L2 ≥ (L1+L3)/2
  -- So L2*(L1+L3) ≥ (L1+L3)²/2
  -- And (L1+L3)²/2 ≥ 2*L1*L3 because (L1-L3)² ≥ 0
  have h_sq_nonneg : (L1 - L3)^2 ≥ 0 := by positivity
  have h_main : 2 * L1 * L3 ≤ L2 * (L1 + L3) := by
    have h_ineq : 2 * L1 * L3 ≤ ((L1 + L3)^2) / 2 := by
      nlinarith
    have hL2_ge : (L1 + L3) / 2 ≤ L2 := by linarith
    nlinarith
  -- Convert back to the original goal
  field_simp [hpos1.ne.symm, hpos2.ne.symm, hpos3.ne.symm]
  nlinarith


theorem wB_lower (T : ℕ) (hT : 1 ≤ T) :
    1 / (((T : ℝ) + 2) * Real.log ((T : ℝ) + 2) ^ 2) ≤
      1 / Real.log ((T : ℝ) + 1) - 1 / Real.log ((T : ℝ) + 2) := by
  set a := (T : ℝ) + 1 with ha
  set b := (T : ℝ) + 2 with hb
  have ha_pos : 0 < a := by
    have hT' : (0 : ℝ) ≤ (T : ℝ) := by exact mod_cast (Nat.zero_le T)
    linarith
  have hb_pos : 0 < b := by
    have hT' : (0 : ℝ) ≤ (T : ℝ) := by exact mod_cast (Nat.zero_le T)
    linarith
  have ha_one : 1 < a := by
    have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact mod_cast hT
    linarith
  have hb_one : 1 < b := by
    have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact mod_cast hT
    linarith
  have hL1_pos : 0 < Real.log a := Real.log_pos ha_one
  have hL2_pos : 0 < Real.log b := Real.log_pos hb_one
  have hL1_le_L2 : Real.log a ≤ Real.log b :=
    Real.log_le_log (by linarith) (by linarith)
  have h_diff : 1 / b ≤ Real.log b - Real.log a := by
    have hx_pos : 0 < b / a := div_pos hb_pos ha_pos
    have hineq_raw : 1 - (b / a)⁻¹ ≤ Real.log (b / a) :=
      Real.one_sub_inv_le_log_of_pos hx_pos
    have h_inv_eq : (b / a)⁻¹ = a / b := by field_simp
    rw [h_inv_eq] at hineq_raw
    have hlog_div : Real.log (b / a) = Real.log b - Real.log a :=
      Real.log_div (by linarith) (by linarith)
    rw [hlog_div] at hineq_raw
    have h_sub_eq : 1 - a / b = 1 / b := by
      field_simp [hb_pos.ne']
      ring
    rw [h_sub_eq] at hineq_raw
    exact hineq_raw
  have hRHS : 1 / Real.log a - 1 / Real.log b =
      (Real.log b - Real.log a) / (Real.log a * Real.log b) := by
    field_simp [hL1_pos.ne', hL2_pos.ne']
  rw [hRHS]
  have h_denom1 : 0 < b * Real.log b ^ 2 := by positivity
  have h_denom2 : 0 < Real.log a * Real.log b := by positivity
  rw [div_le_div_iff₀ h_denom1 h_denom2]
  simp only [one_mul]
  have h_diff' : 1 ≤ b * (Real.log b - Real.log a) := by
    calc
      1 = (1 / b) * b := by field_simp [hb_pos.ne']
      _ ≤ (Real.log b - Real.log a) * b :=
        mul_le_mul_of_nonneg_right h_diff hb_pos.le
      _ = b * (Real.log b - Real.log a) := mul_comm _ _
  calc
    Real.log a * Real.log b ≤ Real.log b * Real.log b :=
      mul_le_mul_of_nonneg_right hL1_le_L2 hL2_pos.le
    _ = Real.log b ^ 2 := by ring
    _ = 1 * Real.log b ^ 2 := by simp
    _ ≤ (b * (Real.log b - Real.log a)) * Real.log b ^ 2 :=
      mul_le_mul_of_nonneg_right h_diff' (by positivity)
    _ = (Real.log b - Real.log a) * b * Real.log b ^ 2 := by ring
    _ = (Real.log b - Real.log a) * (b * Real.log b ^ 2) := by ring


theorem lamB_lower (t : ℕ) :
    3 * ((t : ℝ) + 2) * Real.log ((t : ℝ) + 2) ≤
      3 * Real.log ((t : ℝ) + 2) / Real.log (((t : ℝ) + 3) / ((t : ℝ) + 2)) := by
  have ht_nonneg : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have ht2pos : 0 < (t : ℝ) + 2 := by linarith
  have hratio_gt_one : 1 < ((t : ℝ) + 3) / ((t : ℝ) + 2) := by
    refine (one_lt_div ht2pos).mpr ?_
    linarith
  have hupos : 0 < Real.log (((t : ℝ) + 3) / ((t : ℝ) + 2)) :=
    Real.log_pos hratio_gt_one
  have hLpos : 0 < Real.log ((t : ℝ) + 2) :=
    Real.log_pos (by linarith)
  set u := Real.log (((t : ℝ) + 3) / ((t : ℝ) + 2)) with hu_def
  set L := Real.log ((t : ℝ) + 2) with hL_def
  have hu_le : u ≤ 1 / ((t : ℝ) + 2) := by
    rw [hu_def]
    calc
      Real.log (((t : ℝ) + 3) / ((t : ℝ) + 2)) ≤ ((t : ℝ) + 3) / ((t : ℝ) + 2) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (by linarith) ht2pos)
      _ = 1 / ((t : ℝ) + 2) := by
        field_simp [ht2pos.ne.symm]
        ring
  have htu_le_one : ((t : ℝ) + 2) * u ≤ 1 := by
    calc
      ((t : ℝ) + 2) * u ≤ ((t : ℝ) + 2) * (1 / ((t : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hu_le (by linarith)
      _ = 1 := by field_simp [ht2pos.ne.symm]
  have hineq : (3 * ((t : ℝ) + 2) * L) * u ≤ 3 * L := by
    calc
      (3 * ((t : ℝ) + 2) * L) * u = (3 * L) * (((t : ℝ) + 2) * u) := by ring
      _ ≤ (3 * L) * 1 := mul_le_mul_of_nonneg_left htu_le_one (by linarith)
      _ = 3 * L := by ring
  rw [le_div_iff₀ hupos]
  simpa [hu_def, hL_def] using hineq


theorem terminal_cond (T : ℕ) (hT : 1 ≤ T) :
    √(2 * π) * exp (min 4 (T : ℝ) / 2) ≤
      3 * ((T : ℝ) + 1) * Real.log ((T : ℝ) + 1) * (√(T : ℝ) + 1) := by
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hexp1 : Real.exp 1 < 2.7183 := by linarith [Real.exp_one_lt_d9]
  have hlog2 : 0.69 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hsqrt2pi : √(2 * π) < (2.51 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2.51 : ℝ))]
    nlinarith
  have hexp_half : Real.exp (1/2 : ℝ) < 1.65 := by
    have hsq : (Real.exp (1/2 : ℝ)) ^ 2 = Real.exp 1 := by
      calc
        (Real.exp (1/2 : ℝ)) ^ 2 = Real.exp (1/2 : ℝ) * Real.exp (1/2 : ℝ) := by ring_nf
        _ = Real.exp ((1/2 : ℝ) + (1/2 : ℝ)) := by rw [Real.exp_add]
        _ = Real.exp 1 := by ring_nf
    have hpos : 0 ≤ Real.exp (1/2 : ℝ) := by positivity
    have h165sq : (1.65 : ℝ) ^ 2 = 2.7225 := by norm_num
    have h_lt_sq : (Real.exp (1/2 : ℝ)) ^ 2 < (1.65 : ℝ) ^ 2 := by
      rw [hsq, h165sq]
      linarith [Real.exp_one_lt_d9]
    nlinarith
  have hexp_3half : Real.exp (3/2 : ℝ) < 4.49 := by
    have h_eq : Real.exp (3/2 : ℝ) = Real.exp 1 * Real.exp (1/2 : ℝ) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h_eq]
    have h_mul : Real.exp 1 * Real.exp (1/2 : ℝ) < (2.7183 : ℝ) * 1.65 := by
      have h1 : Real.exp 1 * Real.exp (1/2 : ℝ) < (2.7183 : ℝ) * Real.exp (1/2 : ℝ) :=
        mul_lt_mul_of_pos_right hexp1 (Real.exp_pos _)
      have h2 : (2.7183 : ℝ) * Real.exp (1/2 : ℝ) < (2.7183 : ℝ) * 1.65 :=
        mul_lt_mul_of_pos_left hexp_half (by norm_num : (0 : ℝ) < (2.7183 : ℝ))
      linarith
    nlinarith
  have hexp2 : Real.exp 2 < 7.39 := by
    have h_eq : Real.exp 2 = (Real.exp 1) ^ 2 := by
      calc
        Real.exp 2 = Real.exp (1 + 1) := by norm_num
        _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
        _ = (Real.exp 1) ^ 2 := by ring_nf
    rw [h_eq]
    have hpos : 0 ≤ Real.exp 1 := by positivity
    have hsq : (Real.exp 1) ^ 2 < (2.7183 : ℝ) ^ 2 := by
      have h := mul_self_lt_mul_self hpos hexp1
      simpa [sq] using h
    have h_bound : (2.7183 : ℝ) ^ 2 < (7.39 : ℝ) := by
      norm_num
    have h_lt : (Real.exp 1) ^ 2 < (7.39 : ℝ) :=
      lt_trans hsq h_bound
    exact h_lt
  have hlog_gt_one {x : ℝ} (hx : 3 ≤ x) : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt (by linarith : 0 < x)]
    have h_exp1_lt_3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hT_real : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  by_cases hT1 : (T : ℕ) = 1
  · -- T = 1
    have hT1' : (T : ℝ) = 1 := by exact_mod_cast hT1
    rw [hT1']
    have hmin : min (4 : ℝ) (1 : ℝ) = (1 : ℝ) := by
      rw [min_eq_right (by norm_num : (1 : ℝ) ≤ 4)]
    rw [hmin]
    have hleft : √(2 * π) * Real.exp (1/2 : ℝ) < (2.51 : ℝ) * 1.65 := by
      have h1 : √(2 * π) * Real.exp (1/2 : ℝ) < (2.51 : ℝ) * Real.exp (1/2 : ℝ) :=
        mul_lt_mul_of_pos_right hsqrt2pi (Real.exp_pos _)
      have h2 : (2.51 : ℝ) * Real.exp (1/2 : ℝ) < (2.51 : ℝ) * 1.65 :=
        mul_lt_mul_of_pos_left hexp_half (by norm_num : (0 : ℝ) < (2.51 : ℝ))
      linarith
    have hright : (8.28 : ℝ) < 3 * ((1 : ℝ) + 1) * Real.log ((1 : ℝ) + 1) * (√(1 : ℝ) + 1) := by
      have hlog2_val : Real.log ((1 : ℝ) + 1) = Real.log 2 := by norm_num
      rw [hlog2_val]
      have h_sqrt1 : √(1 : ℝ) = 1 := by norm_num
      rw [h_sqrt1]
      nlinarith
    nlinarith
  · -- T ≠ 1
    by_cases hT2 : (T : ℕ) = 2
    · -- T = 2
      have hT2' : (T : ℝ) = 2 := by exact_mod_cast hT2
      rw [hT2']
      have hmin : min (4 : ℝ) (2 : ℝ) = (2 : ℝ) := by
        rw [min_eq_right (by norm_num : (2 : ℝ) ≤ 4)]
      rw [hmin]
      -- simplify 2/2 = 1
      have h_div : (2 : ℝ) / 2 = (1 : ℝ) := by norm_num
      rw [h_div]
      have hleft : √(2 * π) * Real.exp 1 < (2.51 : ℝ) * (2.7183 : ℝ) := by
        have h1 : √(2 * π) * Real.exp 1 < (2.51 : ℝ) * Real.exp 1 :=
          mul_lt_mul_of_pos_right hsqrt2pi (Real.exp_pos _)
        have h2 : (2.51 : ℝ) * Real.exp 1 < (2.51 : ℝ) * (2.7183 : ℝ) :=
          mul_lt_mul_of_pos_left hexp1 (by norm_num : (0 : ℝ) < (2.51 : ℝ))
        linarith
      have hright : (18 : ℝ) < 3 * ((2 : ℝ) + 1) * Real.log ((2 : ℝ) + 1) * (√(2 : ℝ) + 1) := by
        have hlog3 : 1 < Real.log ((2 : ℝ) + 1) := by
          have h_eq : (2 : ℝ) + 1 = (3 : ℝ) := by norm_num
          rw [h_eq]
          exact hlog_gt_one (by norm_num)
        have h_sqrt2 : 2 < √(2 : ℝ) + 1 := by
          have h_sqrt2_val : 1 < √(2 : ℝ) := by
            calc
              (1 : ℝ) = √((1 : ℝ) ^ 2) := by norm_num
              _ < √2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          linarith
        nlinarith
      nlinarith
    · -- T ≠ 2
      by_cases hT3 : (T : ℕ) = 3
      · -- T = 3
        have hT3' : (T : ℝ) = 3 := by exact_mod_cast hT3
        rw [hT3']
        have hmin : min (4 : ℝ) (3 : ℝ) = (3 : ℝ) := by
          rw [min_eq_right (by norm_num : (3 : ℝ) ≤ 4)]
        rw [hmin]
        have hleft : √(2 * π) * Real.exp (3/2 : ℝ) < (2.51 : ℝ) * 4.49 := by
          have h1 : √(2 * π) * Real.exp (3/2 : ℝ) < (2.51 : ℝ) * Real.exp (3/2 : ℝ) :=
            mul_lt_mul_of_pos_right hsqrt2pi (Real.exp_pos _)
          have h2 : (2.51 : ℝ) * Real.exp (3/2 : ℝ) < (2.51 : ℝ) * 4.49 :=
            mul_lt_mul_of_pos_left hexp_3half (by norm_num : (0 : ℝ) < (2.51 : ℝ))
          linarith
        have hright : (24 : ℝ) < 3 * ((3 : ℝ) + 1) * Real.log ((3 : ℝ) + 1) * (√(3 : ℝ) + 1) := by
          have hlog4 : 1 < Real.log ((3 : ℝ) + 1) := by
            have h_eq : (3 : ℝ) + 1 = (4 : ℝ) := by norm_num
            rw [h_eq]
            exact hlog_gt_one (by norm_num)
          have h_sqrt3 : 2 < √(3 : ℝ) + 1 := by
            have h_sqrt3_val : 1 < √(3 : ℝ) := by
              calc
                (1 : ℝ) = √((1 : ℝ) ^ 2) := by norm_num
                _ < √3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
            linarith
          nlinarith
        have h_bound : (2.51 : ℝ) * 4.49 < (24 : ℝ) := by nlinarith
        have h_lt : √(2 * π) * Real.exp (3/2 : ℝ) < 3 * ((3 : ℝ) + 1) * Real.log ((3 : ℝ) + 1) * (√(3 : ℝ) + 1) :=
          lt_trans hleft (lt_trans h_bound hright)
        exact le_of_lt h_lt
      · -- T ≠ 3, so T ≥ 4
        have hT4 : 4 ≤ (T : ℕ) := by
          have h_not1 : T ≠ 1 := hT1
          have h_not2 : T ≠ 2 := hT2
          have h_not3 : T ≠ 3 := hT3
          omega
        have hT4' : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT4
        have hmin : min (4 : ℝ) (T : ℝ) = (4 : ℝ) := by
          rw [min_eq_left hT4']
        rw [hmin]
        -- simplify 4/2 = 2
        have h_div : (4 : ℝ) / 2 = (2 : ℝ) := by norm_num
        rw [h_div]
        have hleft : √(2 * π) * Real.exp 2 < (2.51 : ℝ) * 7.39 := by
          have h1 : √(2 * π) * Real.exp 2 < (2.51 : ℝ) * Real.exp 2 :=
            mul_lt_mul_of_pos_right hsqrt2pi (Real.exp_pos _)
          have h2 : (2.51 : ℝ) * Real.exp 2 < (2.51 : ℝ) * 7.39 :=
            mul_lt_mul_of_pos_left hexp2 (by norm_num : (0 : ℝ) < (2.51 : ℝ))
          linarith
        have hright : (45 : ℝ) ≤ 3 * ((T : ℝ) + 1) * Real.log ((T : ℝ) + 1) * (√(T : ℝ) + 1) := by
          have hlogT : 1 < Real.log ((T : ℝ) + 1) := by
            have hpos_T1 : 0 < (T : ℝ) + 1 := by linarith
            rw [Real.lt_log_iff_exp_lt hpos_T1]
            have h_exp1_lt_T1 : Real.exp 1 < (T : ℝ) + 1 := by
              have h_exp1_lt_5 : Real.exp 1 < 5 := by linarith [Real.exp_one_lt_d9]
              linarith
            exact h_exp1_lt_T1
          have h_sqrtT : 2 ≤ √(T : ℝ) := by
            have h := Real.sqrt_le_sqrt hT4'
            have h_sqrt4 : √(4 : ℝ) = 2 := by norm_num
            rw [h_sqrt4] at h
            exact h
          have h_sqrtT_plus_one : 3 ≤ √(T : ℝ) + 1 := by linarith
          have hlogT_nonneg : 0 ≤ Real.log ((T : ℝ) + 1) := by
            have hx : 1 ≤ (T : ℝ) + 1 := by linarith
            exact Real.log_nonneg hx
          have hA : 3 * 5 ≤ 3 * ((T : ℝ) + 1) := by nlinarith
          have hB : 1 ≤ Real.log ((T : ℝ) + 1) := by linarith
          have hC : 3 ≤ √(T : ℝ) + 1 := h_sqrtT_plus_one
          have h_nonneg_A : 0 ≤ 3 * ((T : ℝ) + 1) := by nlinarith
          have h_nonneg_B : 0 ≤ (1 : ℝ) := by norm_num
          -- (3*5)*1 ≤ (3*(T+1))*log(T+1)
          have hAB : (3 * 5) * 1 ≤ (3 * ((T : ℝ) + 1)) * Real.log ((T : ℝ) + 1) :=
            mul_le_mul hA hB h_nonneg_B h_nonneg_A
          -- multiply by (√T+1)
          have hABC : ((3 * 5) * 1) * 3 ≤ ((3 * ((T : ℝ) + 1)) * Real.log ((T : ℝ) + 1)) * (√(T : ℝ) + 1) :=
            mul_le_mul hAB hC (by
              have h_sqrt_nonneg : 0 ≤ √(T : ℝ) := Real.sqrt_nonneg _
              nlinarith) (by nlinarith)
          have h_goal_eq : (45 : ℝ) = ((3 : ℝ) * 5) * 1 * 3 := by norm_num
          rw [h_goal_eq]
          simpa [mul_assoc] using hABC
        have h_bound : (2.51 : ℝ) * 7.39 < (45 : ℝ) := by nlinarith
        have h_lt : √(2 * π) * Real.exp 2 < 3 * ((T : ℝ) + 1) * Real.log ((T : ℝ) + 1) * (√(T : ℝ) + 1) :=
          lt_trans hleft (lt_of_lt_of_le h_bound hright)
        exact le_of_lt h_lt


theorem exp_lower : (3.93765 : ℝ) ≤ exp 1.3706 := by
  have h_add : exp (1.3706 : ℝ) = exp 1 * exp (0.3706 : ℝ) := by
    calc
      exp (1.3706 : ℝ) = exp ((1 : ℝ) + (0.3706 : ℝ)) := by norm_num
      _ = exp 1 * exp (0.3706 : ℝ) := by rw [Real.exp_add]
  have h_exp1 : (2.7182818283 : ℝ) < exp 1 := Real.exp_one_gt_d9
  have h_nonneg : (0 : ℝ) ≤ 0.3706 := by norm_num
  have h_taylor : (∑ i ∈ Finset.range 6, (0.3706 : ℝ) ^ i / (i.factorial : ℝ)) ≤ exp (0.3706 : ℝ) :=
    Real.sum_le_exp_of_nonneg h_nonneg 6
  have h_taylor_val : (∑ i ∈ Finset.range 6, (0.3706 : ℝ) ^ i / (i.factorial : ℝ)) = (543224894267549349493 / 375000000000000000000 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have h_prod : (3.93765 : ℝ) ≤ (2.7182818283 : ℝ) * ((543224894267549349493 : ℝ) / 375000000000000000000 : ℝ) := by
    nlinarith
  have h_taylor_nonneg : 0 ≤ (∑ i ∈ Finset.range 6, (0.3706 : ℝ) ^ i / (i.factorial : ℝ)) := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    positivity
  have h_exp1_pos : 0 < exp 1 := Real.exp_pos 1
  calc
    (3.93765 : ℝ) ≤ (2.7182818283 : ℝ) * ((543224894267549349493 : ℝ) / 375000000000000000000 : ℝ) := h_prod
    _ = (2.7182818283 : ℝ) * (∑ i ∈ Finset.range 6, (0.3706 : ℝ) ^ i / (i.factorial : ℝ)) := by rw [h_taylor_val]
    _ ≤ exp 1 * (∑ i ∈ Finset.range 6, (0.3706 : ℝ) ^ i / (i.factorial : ℝ)) := by
      nlinarith
    _ ≤ exp 1 * exp (0.3706 : ℝ) := by
      nlinarith
    _ = exp (1.3706 : ℝ) := by rw [h_add]


theorem constK_le (h3 : Real.log 3 < 1.0986123) (he : exp (-1 / 2) ≤ 0.6065306598)
    (hx : (3.93765 : ℝ) ≤ exp 1.3706) :
    2 * Real.log (3 / Real.log 2 + 2 * exp (-1 / 2) * (1 / Real.log 2 - 1 / Real.log 3)) -
      Real.log (2 * π) ≤ 1.3706 := by
  set H := 3 / Real.log 2 + 2 * exp (-1 / 2) * (1 / Real.log 2 - 1 / Real.log 3) with hH
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hlog2_lt_log3 : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
  have hc_pos : 0 < 1 / Real.log 2 - 1 / Real.log 3 := by
    have h : 1 / Real.log 3 < 1 / Real.log 2 :=
      (one_div_lt_one_div hlog3pos hlog2pos).mpr hlog2_lt_log3
    linarith
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have h_two_pi_pos : 0 < 2 * π := by positivity
  have h_two_pi_ne_zero : 2 * π ≠ 0 := by linarith
  -- Step 2: upper bound of H
  have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog3_lt : Real.log 3 < 1.0986123 := h3
  have hpos_0693 : 0 < (0.6931471803 : ℝ) := by norm_num
  have hpos_1098 : 0 < (1.0986123 : ℝ) := by norm_num
  have h_one_div_log2_lt : 1 / Real.log 2 < 1 / (0.6931471803 : ℝ) :=
    (one_div_lt_one_div hlog2pos hpos_0693).mpr hlog2_gt
  have h_one_div_log3_gt : 1 / (1.0986123 : ℝ) < 1 / Real.log 3 :=
    (one_div_lt_one_div hpos_1098 hlog3pos).mpr hlog3_lt
  have hc_lt : 1 / Real.log 2 - 1 / Real.log 3 < 1 / (0.6931471803 : ℝ) - 1 / (1.0986123 : ℝ) := by
    linarith
  have hpos_6065 : 0 < (0.6065306598 : ℝ) := by norm_num
  have hH_lt : H < 3 / (0.6931471803 : ℝ) + 2 * (0.6065306598 : ℝ) * (1 / (0.6931471803 : ℝ) - 1 / (1.0986123 : ℝ)) := by
    dsimp [H]
    have h3lt : 3 / Real.log 2 < 3 / (0.6931471803 : ℝ) := by
      have h := (one_div_lt_one_div hlog2pos hpos_0693).mpr hlog2_gt
      -- h : 1 / log 2 < 1 / 0.6931471803, multiply by 3 > 0
      have h' := mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 3)
      -- h' : 3*(1/log 2) < 3*(1/0.693...)
      -- but 3*(1/x) = 3/x
      simpa [div_eq_mul_inv] using h'
    have h2le : 2 * exp (-1 / 2) * (1 / Real.log 2 - 1 / Real.log 3) ≤
               2 * (0.6065306598 : ℝ) * (1 / Real.log 2 - 1 / Real.log 3) := by
      have h := mul_le_mul_of_nonneg_right he (by linarith [hc_pos])
      nlinarith
    have h2lt : 2 * (0.6065306598 : ℝ) * (1 / Real.log 2 - 1 / Real.log 3) <
               2 * (0.6065306598 : ℝ) * (1 / (0.6931471803 : ℝ) - 1 / (1.0986123 : ℝ)) := by
      have hpos' : 0 < 2 * (0.6065306598 : ℝ) := by positivity
      exact mul_lt_mul_of_pos_left hc_lt hpos'
    linarith
  have hH_lt_bound : H < 4.973987 := by
    have hcalc : 3 / (0.6931471803 : ℝ) + 2 * (0.6065306598 : ℝ) * (1 / (0.6931471803 : ℝ) - 1 / (1.0986123 : ℝ)) < 4.973987 := by
      norm_num
    linarith
  have hH_sq_lt : H ^ 2 < (4.973987 : ℝ) ^ 2 := by
    nlinarith
  -- Step 3: lower bound of 2*pi*exp(1.3706)
  have hpi_gt : 3.141592 < π := Real.pi_gt_d6
  have h_two_pi_exp_gt : (4.973987 : ℝ) ^ 2 < 2 * π * exp 1.3706 := by
    have hcalc1 : (4.973987 : ℝ) ^ 2 < 2 * (3.141592 : ℝ) * (3.93765 : ℝ) := by norm_num
    have hcalc2 : 2 * (3.141592 : ℝ) * (3.93765 : ℝ) < 2 * π * exp 1.3706 := by
      nlinarith
    nlinarith
  have hH_sq_lt_two_pi_exp : H ^ 2 < 2 * π * exp 1.3706 := by
    nlinarith
  -- Step 4: final inequality via log(H^2/(2*π)) ≤ 1.3706
  have h_div_lt : H ^ 2 / (2 * π) < exp 1.3706 := by
    field_simp [h_two_pi_ne_zero]
    nlinarith
  have h_nonneg : 0 < H ^ 2 / (2 * π) := div_pos (by positivity) h_two_pi_pos
  have h_log_ineq : Real.log (H ^ 2 / (2 * π)) ≤ 1.3706 := by
    rw [Real.log_le_iff_le_exp h_nonneg]
    exact h_div_lt.le
  calc
    2 * Real.log H - Real.log (2 * π) = Real.log (H ^ 2) - Real.log (2 * π) := by
      rw [Real.log_pow, Nat.cast_ofNat]
    _ = Real.log (H ^ 2 / (2 * π)) := by rw [Real.log_div (by positivity) h_two_pi_ne_zero]
    _ ≤ 1.3706 := h_log_ineq


theorem closed_form (T : ℕ) (hT : 1 ≤ T) (b : ℝ)
    (hb : 1 / (((T : ℝ) + 2) * Real.log ((T : ℝ) + 2) ^ 2) ≤ b) :
    2 * Real.log (3 / Real.log 2 + 2 * exp (-1 / 2) * (1 / Real.log 2 - 1 / Real.log 3)) +
        2 * Real.log ((√(T : ℝ) + 1) / (√(2 * π) * b)) ≤
      3 * Real.log T + 4 * Real.log (Real.log ((T : ℝ) + 2)) +
        (2 * Real.log (3 / Real.log 2 + 2 * exp (-1 / 2) * (1 / Real.log 2 - 1 / Real.log 3)) -
          Real.log (2 * π)) +
        2 * Real.log (1 + 1 / √(T : ℝ)) + 2 * Real.log (1 + 2 / T) := by
  set L := Real.log ((T : ℝ) + 2) with hLdef
  have hT_one_le : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTpos' : 0 < (T : ℝ) + 2 := by linarith
  have hTpos : 0 < (T : ℝ) := by linarith
  have hT_plus_two_ne_zero : (T : ℝ) + 2 ≠ 0 := by linarith
  have hLpos : 0 < L := by
    rw [hLdef]
    refine Real.log_pos ?_
    linarith
  have hbpos : 0 < b := by
    have hpos : 0 < 1 / (((T : ℝ) + 2) * Real.log ((T : ℝ) + 2) ^ 2) := by
      refine div_pos (by norm_num) (mul_pos hTpos' (pow_pos hLpos 2))
    linarith
  have hsqrtTpos : 0 < √(T : ℝ) := Real.sqrt_pos.mpr hTpos
  have hsqrt2pipos : 0 < √(2 * π) := by
    refine Real.sqrt_pos.mpr ?_
    have hπpos : 0 < π := by exact Real.pi_pos
    nlinarith
  have hsqrt2pine_zero : √(2 * π) ≠ 0 := by linarith
  have h_sqrtT_plus_one_pos : 0 < √(T : ℝ) + 1 := by linarith
  have h_denom_pos : 0 < √(2 * π) * b := mul_pos hsqrt2pipos hbpos
  have h_denom_ne_zero : √(2 * π) * b ≠ 0 := by linarith
  have h_sqrtT_plus_one_ne_zero : √(T : ℝ) + 1 ≠ 0 := by linarith
  have hL_ne_zero : L ≠ 0 := by linarith
  have hT_ne_zero : (T : ℝ) ≠ 0 := by linarith
  have hb_ne_zero : b ≠ 0 := by linarith
  have h_one_plus_one_over_sqrtT_pos : 0 < 1 + 1 / √(T : ℝ) := by
    refine add_pos_of_pos_of_nonneg (by norm_num) (div_nonneg (by norm_num) (by linarith))
  have h_one_plus_one_over_sqrtT_ne_zero : 1 + 1 / √(T : ℝ) ≠ 0 := by linarith
  have h_one_plus_two_over_T_pos : 0 < 1 + 2 / (T : ℝ) := by
    refine add_pos_of_pos_of_nonneg (by norm_num) (div_nonneg (by norm_num) (by linarith))
  have h_one_plus_two_over_T_ne_zero : 1 + 2 / (T : ℝ) ≠ 0 := by linarith
  have hT_plus_two_eq : (T : ℝ) + 2 = (T : ℝ) * (1 + 2 / (T : ℝ)) := by
    field_simp [hT_ne_zero]
  set C := 2 * Real.log (3 / Real.log 2 + 2 * exp (-1 / 2) * (1 / Real.log 2 - 1 / Real.log 3)) with hCdef
  have hgoal : 2 * Real.log ((√(T : ℝ) + 1) / (√(2 * π) * b)) ≤
      3 * Real.log (T : ℝ) + 4 * Real.log L - Real.log (2 * π) + 2 * Real.log (1 + 1 / √(T : ℝ)) + 2 * Real.log (1 + 2 / (T : ℝ)) := by
    -- Step 1: expand the log of the fraction
    have h_log_div : Real.log ((√(T : ℝ) + 1) / (√(2 * π) * b)) =
        Real.log (√(T : ℝ) + 1) - Real.log (√(2 * π) * b) :=
      Real.log_div h_sqrtT_plus_one_ne_zero h_denom_ne_zero
    -- Step 2: expand log(√(2π) * b)
    have h_log_mul_sqrt : Real.log (√(2 * π) * b) = Real.log (√(2 * π)) + Real.log b :=
      Real.log_mul hsqrt2pine_zero hb_ne_zero
    -- Step 3: 2 * log(√(2π)) = log(2π)
    have h_log_sqrt_2pi : Real.log (√(2 * π)) = Real.log (2 * π) / 2 :=
      Real.log_sqrt (by nlinarith [Real.pi_pos] : 0 ≤ 2 * π)
    have h_two_log_sqrt_2pi : 2 * Real.log (√(2 * π)) = Real.log (2 * π) := by
      rw [h_log_sqrt_2pi]
      ring
    -- Step 4: expand log(√T + 1) = log(√T * (1 + 1/√T))
    have h_sqrtT_plus_one_eq : √(T : ℝ) + 1 = √(T : ℝ) * (1 + 1 / √(T : ℝ)) := by
      field_simp [hsqrtTpos.ne']
    have h_log_sqrtT_plus_one : Real.log (√(T : ℝ) + 1) = Real.log (√(T : ℝ)) + Real.log (1 + 1 / √(T : ℝ)) := by
      rw [h_sqrtT_plus_one_eq]
      exact Real.log_mul (by linarith : √(T : ℝ) ≠ 0) h_one_plus_one_over_sqrtT_ne_zero
    -- Step 5: 2 * log(√T) = log T
    have h_log_sqrtT : Real.log (√(T : ℝ)) = Real.log (T : ℝ) / 2 :=
      Real.log_sqrt (by linarith : 0 ≤ (T : ℝ))
    have h_two_log_sqrtT : 2 * Real.log (√(T : ℝ)) = Real.log (T : ℝ) := by
      rw [h_log_sqrtT]
      ring
    -- Step 6: combine to get expression for 2 * log((√T + 1)/(√(2π)*b))
    have h_expr : 2 * Real.log ((√(T : ℝ) + 1) / (√(2 * π) * b)) =
        Real.log (T : ℝ) + 2 * Real.log (1 + 1 / √(T : ℝ)) - Real.log (2 * π) - 2 * Real.log b := by
      calc
        2 * Real.log ((√(T : ℝ) + 1) / (√(2 * π) * b))
            = 2 * (Real.log (√(T : ℝ) + 1) - Real.log (√(2 * π) * b)) := by rw [h_log_div]
        _ = 2 * Real.log (√(T : ℝ) + 1) - 2 * Real.log (√(2 * π) * b) := by ring
        _ = 2 * Real.log (√(T : ℝ) + 1) - 2 * (Real.log (√(2 * π)) + Real.log b) := by rw [h_log_mul_sqrt]
        _ = 2 * Real.log (√(T : ℝ) + 1) - (2 * Real.log (√(2 * π)) + 2 * Real.log b) := by ring
        _ = 2 * Real.log (√(T : ℝ) + 1) - 2 * Real.log (√(2 * π)) - 2 * Real.log b := by ring
        _ = (2 * Real.log (√(T : ℝ)) + 2 * Real.log (1 + 1 / √(T : ℝ))) - 2 * Real.log (√(2 * π)) - 2 * Real.log b := by
          rw [h_log_sqrtT_plus_one]
          ring
        _ = (Real.log (T : ℝ) + 2 * Real.log (1 + 1 / √(T : ℝ))) - Real.log (2 * π) - 2 * Real.log b := by
          rw [h_two_log_sqrtT, h_two_log_sqrt_2pi]
        _ = Real.log (T : ℝ) + 2 * Real.log (1 + 1 / √(T : ℝ)) - Real.log (2 * π) - 2 * Real.log b := by ring
    rw [h_expr]
    -- Step 7: from hb, derive inequality for -2 log b
    have h_log_hb : Real.log (1 / (((T : ℝ) + 2) * L ^ 2)) ≤ Real.log b :=
      Real.log_le_log (by
        refine div_pos (by norm_num) (mul_pos hTpos' (pow_pos hLpos 2))) hb
    have h_log_left : Real.log (1 / (((T : ℝ) + 2) * L ^ 2)) = -L - 2 * Real.log L := by
      calc
        Real.log (1 / (((T : ℝ) + 2) * L ^ 2)) = Real.log 1 - Real.log (((T : ℝ) + 2) * L ^ 2) :=
          Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (mul_ne_zero hT_plus_two_ne_zero (pow_ne_zero 2 hL_ne_zero))
        _ = 0 - Real.log (((T : ℝ) + 2) * L ^ 2) := by simp
        _ = -Real.log (((T : ℝ) + 2) * L ^ 2) := by simp
        _ = -(Real.log ((T : ℝ) + 2) + Real.log (L ^ 2)) := by
          rw [Real.log_mul hT_plus_two_ne_zero (pow_ne_zero 2 hL_ne_zero)]
        _ = -(L + Real.log (L ^ 2)) := by rw [hLdef]
        _ = -(L + 2 * Real.log L) := by rw [Real.log_pow, Nat.cast_ofNat]
        _ = -L - 2 * Real.log L := by ring
    have h_neg_two_log_b : -2 * Real.log b ≤ 2 * Real.log ((T : ℝ) + 2) + 4 * Real.log L := by
      rw [h_log_left] at h_log_hb
      linarith
    -- Step 8: expand 2 * log(T + 2)
    have h_log_T_plus_two : Real.log ((T : ℝ) + 2) = Real.log (T : ℝ) + Real.log (1 + 2 / (T : ℝ)) := by
      rw [hT_plus_two_eq]
      exact Real.log_mul hT_ne_zero h_one_plus_two_over_T_ne_zero
    have h_two_log_T_plus_two : 2 * Real.log ((T : ℝ) + 2) = 2 * Real.log (T : ℝ) + 2 * Real.log (1 + 2 / (T : ℝ)) := by
      rw [h_log_T_plus_two]
      ring
    -- Step 9: combine everything
    have h_combined : Real.log (T : ℝ) + 2 * Real.log (1 + 1 / √(T : ℝ)) - Real.log (2 * π) - 2 * Real.log b ≤
        3 * Real.log (T : ℝ) + 4 * Real.log L - Real.log (2 * π) + 2 * Real.log (1 + 1 / √(T : ℝ)) + 2 * Real.log (1 + 2 / (T : ℝ)) := by
      rw [h_two_log_T_plus_two] at h_neg_two_log_b
      linarith
    exact h_combined
  -- Now add C to both sides
  have h_total : C + 2 * Real.log ((√(T : ℝ) + 1) / (√(2 * π) * b)) ≤
      C + (3 * Real.log (T : ℝ) + 4 * Real.log L - Real.log (2 * π) + 2 * Real.log (1 + 1 / √(T : ℝ)) + 2 * Real.log (1 + 2 / (T : ℝ))) := by
    linarith
  -- Simplify RHS to match goal
  simpa [hCdef, hLdef, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h_total

end RegretKappa.UnknownBT
