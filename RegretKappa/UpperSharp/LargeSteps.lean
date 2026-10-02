import RegretKappa.UpperSharp.Weights

/-!
# The upper bound with the paper's constants: large steps

In the units of `Upper` (`G = Γ/2`): for `2/3 ≤ b² ≤ 1` and every `ρ`,
`max (G (ρ c + b)) (G (ρ c - b)) ≤ G ρ + 2.7053/2` with `c = √(1 - b²)` (`large_step_sharp`).

* geometry (the paper's step (i)): `(ρ √(1 - s) + √s)² ≤ m2 ρ` for `ρ ≥ 0`, `s ∈ [2/3, 1]`, with
  `m2 ρ = 1 + ρ²` for `ρ² ≤ 1/2` and `(ρ/√3 + √(2/3))²` beyond (`m2_ge`); `m2` is nondecreasing and
  `m2 ρ - ρ²` nonincreasing on `[0, ∞)`;
* for `ρ ≥ 2`, `m2 ρ ≤ ρ²` and the step does not raise the potential (`m2_le_sq`);
* on `[0, 2]`, the paper's 22 pieces `[(i-1)/11, i/11]` (its step (iv)): on each,
  `G √(m2 ρ) - G ρ ≤ q_i Dg(x_i)` by the convexity of `g` (`G_sqrt_sub_le`), with
  `q_i ≥ m2((i-1)/11) - ((i-1)/11)²` and `x_i ≥ m2(i/11)` rational, and
  `q_i (gpN 30 x_i + tailN 30 x_i) ≤ 2.7053` (`piece_1` to `piece_22`).
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set Finset Filter Topology

/-- The majorant `m(ρ)²` of `(ρ √(1 - s) + √s)²` over `s ∈ [2/3, 1]`: `1 + ρ²` for `ρ² ≤ 1/2`,
`(ρ/√3 + √(2/3))²` beyond. -/
noncomputable def m2 (ρ : ℝ) : ℝ :=
  if ρ ^ 2 ≤ 1 / 2 then 1 + ρ ^ 2 else ρ ^ 2 / 3 + 2 * √2 * ρ / 3 + 2 / 3

/-! ### Geometry -/

theorem m2_ge {ρ s : ℝ} (hρ : 0 ≤ ρ) (hs0 : 2 / 3 ≤ s) (hs1 : s ≤ 1) :
    (ρ * √(1 - s) + √s) ^ 2 ≤ m2 ρ := by
  by_cases hρsq : ρ ^ 2 ≤ 1 / 2
  · -- case ρ² ≤ 1/2
    rw [m2, ite_eq_left hρsq]
    set c := √(1 - s) with hc_def
    set σ := √s with hσ_def
    have hc_sq : c ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
    have hσ_sq : σ ^ 2 = s := Real.sq_sqrt (by linarith)
    have h_sum_sq : c ^ 2 + σ ^ 2 = 1 := by
      rw [hc_sq, hσ_sq]
      ring
    have h_nonneg : (c - ρ * σ) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  · -- case ρ² > 1/2
    rw [m2, ite_eq_right (by linarith)]
    set c := √(1 - s) with hc_def
    set σ := √s with hσ_def
    set c0 := √(1/3) with hc0_def
    set σ0 := √(2/3) with hσ0_def
    have hc_sq : c ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
    have hσ_sq : σ ^ 2 = s := Real.sq_sqrt (by linarith)
    have hc0_sq : c0 ^ 2 = 1/3 := Real.sq_sqrt (by norm_num)
    have hσ0_sq : σ0 ^ 2 = 2/3 := Real.sq_sqrt (by norm_num)
    have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
    have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
    have hc0_nonneg : 0 ≤ c0 := Real.sqrt_nonneg _
    have hσ0_nonneg : 0 ≤ σ0 := Real.sqrt_nonneg _
    have hc_le_c0 : c ≤ c0 := by
      rw [hc_def, hc0_def]
      exact Real.sqrt_le_sqrt (by linarith)
    have hσ_ge_σ0 : σ0 ≤ σ := by
      rw [hσ0_def, hσ_def]
      exact Real.sqrt_le_sqrt hs0
    -- key inequality: σ ≥ √2 * c
    have hσ_ge_sqrt2_mul_c : √2 * c ≤ σ := by
      have h_sq : (√2 * c) ^ 2 ≤ σ ^ 2 := by
        calc
          (√2 * c) ^ 2 = (√2) ^ 2 * c ^ 2 := by ring
          _ = 2 * c ^ 2 := by norm_num
          _ = 2 * (1 - s) := by rw [hc_sq]
          _ ≤ 2 * (1 - 2/3) := by linarith
          _ = 2/3 := by ring
          _ ≤ s := hs0
          _ = σ ^ 2 := by rw [hσ_sq]
      have h_nonneg_left : 0 ≤ √2 * c :=
        mul_nonneg (Real.sqrt_nonneg _) hc_nonneg
      have h_abs : |√2 * c| ≤ |σ| := (sq_le_sq (a := √2 * c) (b := σ)).mp h_sq
      have h_abs_left : |√2 * c| = √2 * c := abs_of_nonneg h_nonneg_left
      have h_abs_right : |σ| = σ := abs_of_nonneg hσ_nonneg
      rw [h_abs_left, h_abs_right] at h_abs
      exact h_abs
    -- ρ ≥ 1/√2, i.e., √2 * ρ ≥ 1
    have h_sqrt2_pos : 0 < √2 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
    have h_sqrt2_rho_ge_one : 1 ≤ √2 * ρ := by
      have h_nonneg_sqrt2_rho : 0 ≤ √2 * ρ :=
        mul_nonneg (Real.sqrt_nonneg _) hρ
      have h_sq_lt : (1 : ℝ) ^ 2 < (√2 * ρ) ^ 2 := by
        have h1 : (1 : ℝ) < 2 * (ρ ^ 2) := by linarith
        calc
          (1 : ℝ) ^ 2 = 1 := by norm_num
          _ < 2 * (ρ ^ 2) := h1
          _ = (√2) ^ 2 * (ρ ^ 2) := by norm_num
          _ = (√2 * ρ) ^ 2 := by ring
      have h_abs_lt : |(1 : ℝ)| < |√2 * ρ| := (sq_lt_sq (a := 1) (b := √2 * ρ)).mp h_sq_lt
      have h_abs_one : |(1 : ℝ)| = 1 := abs_of_pos (by norm_num : 0 < (1 : ℝ))
      have h_abs_sqrt2_rho : |√2 * ρ| = √2 * ρ := abs_of_nonneg h_nonneg_sqrt2_rho
      rw [h_abs_one, h_abs_sqrt2_rho] at h_abs_lt
      exact h_abs_lt.le
    -- identity: √2 * c0 = σ0
    have h_sqrt2_c0_eq_σ0 : √2 * c0 = σ0 := by
      rw [hc0_def, hσ0_def]
      calc
        √2 * √(1/3) = √(2 * (1/3)) := by
          rw [← Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
        _ = √(2/3) := by norm_num
    -- identity: √2*(c0 + c) ≤ σ + σ0
    have h_ratio : √2 * (c0 + c) ≤ σ + σ0 := by
      calc
        √2 * (c0 + c) = √2 * c0 + √2 * c := by ring
        _ = σ0 + √2 * c := by rw [h_sqrt2_c0_eq_σ0]
        _ ≤ σ + σ0 := by nlinarith
    -- combine: ρ*(σ + σ0) ≥ c0 + c
    have h_combined : c0 + c ≤ ρ * (σ + σ0) := by
      have h1 : √2 * (c0 + c) ≤ √2 * ρ * (σ + σ0) := by
        calc
          √2 * (c0 + c) ≤ σ + σ0 := h_ratio
          _ ≤ √2 * ρ * (σ + σ0) := by
            have h_nonneg_sum : 0 ≤ σ + σ0 := by nlinarith
            nlinarith
      have h1' : √2 * (c0 + c) ≤ √2 * (ρ * (σ + σ0)) := by
        simpa [mul_assoc] using h1
      exact le_of_mul_le_mul_left h1' h_sqrt2_pos
    -- key identity: (ρ*c0 + σ0 - (ρ*c + σ)) * (σ + σ0) = (c0 - c) * (ρ*(σ + σ0) - (c0 + c))
    have h_eq : (ρ * c0 + σ0 - (ρ * c + σ)) * (σ + σ0) = (c0 - c) * (ρ * (σ + σ0) - (c0 + c)) := by
      calc
        (ρ * c0 + σ0 - (ρ * c + σ)) * (σ + σ0)
            = (ρ * (c0 - c) + (σ0 - σ)) * (σ + σ0) := by ring
        _ = ρ * (c0 - c) * (σ + σ0) + (σ0 - σ) * (σ + σ0) := by ring
        _ = ρ * (c0 - c) * (σ + σ0) + (σ0 ^ 2 - σ ^ 2) := by ring
        _ = ρ * (c0 - c) * (σ + σ0) - (c0 ^ 2 - c ^ 2) := by
          rw [hσ0_sq, hσ_sq, hc0_sq, hc_sq]
          ring
        _ = ρ * (c0 - c) * (σ + σ0) - ((c0 - c) * (c0 + c)) := by ring
        _ = (c0 - c) * (ρ * (σ + σ0)) - (c0 - c) * (c0 + c) := by ring
        _ = (c0 - c) * (ρ * (σ + σ0) - (c0 + c)) := by ring
    -- RHS is nonnegative
    have h_rhs_nonneg : 0 ≤ (c0 - c) * (ρ * (σ + σ0) - (c0 + c)) := by
      have h1 : 0 ≤ c0 - c := by linarith
      have h2 : 0 ≤ ρ * (σ + σ0) - (c0 + c) := by linarith
      nlinarith
    -- Since σ + σ0 > 0, the LHS is nonnegative
    have h_sum_pos : 0 < σ + σ0 := by
      have hσ0_pos : 0 < σ0 := Real.sqrt_pos.mpr (by norm_num : 0 < (2/3 : ℝ))
      nlinarith
    have h_diff_nonneg : 0 ≤ ρ * c0 + σ0 - (ρ * c + σ) := by
      have h_prod_nonneg : 0 ≤ (ρ * c0 + σ0 - (ρ * c + σ)) * (σ + σ0) := by
        rw [h_eq]
        exact h_rhs_nonneg
      have h_comm : (σ + σ0) * 0 ≤ (σ + σ0) * (ρ * c0 + σ0 - (ρ * c + σ)) := by
        simpa [mul_comm] using h_prod_nonneg
      exact le_of_mul_le_mul_left h_comm h_sum_pos
    -- Now square both sides
    have h_nonneg_lhs : 0 ≤ ρ * c + σ := by
      apply add_nonneg
      · exact mul_nonneg hρ hc_nonneg
      · exact hσ_nonneg
    have h_nonneg_rhs : 0 ≤ ρ * c0 + σ0 := by
      apply add_nonneg
      · exact mul_nonneg hρ hc0_nonneg
      · exact hσ0_nonneg
    have h_sq_ineq : (ρ * c + σ) ^ 2 ≤ (ρ * c0 + σ0) ^ 2 := by
      have h_diff : ρ * c + σ ≤ ρ * c0 + σ0 := by linarith
      have h_abs : |ρ * c + σ| ≤ |ρ * c0 + σ0| := by
        rw [abs_of_nonneg h_nonneg_lhs, abs_of_nonneg h_nonneg_rhs]
        exact h_diff
      exact (sq_le_sq (a := ρ * c + σ) (b := ρ * c0 + σ0)).mpr h_abs
    -- compute (ρ*c0 + σ0)^2 = ρ^2/3 + 2√2ρ/3 + 2/3
    have h_sqrt_prod : √(1/3) * √(2/3) = √2 / 3 := by
      calc
        √(1/3) * √(2/3) = √((1/3) * (2/3)) := by
          rw [← Real.sqrt_mul (by norm_num : 0 ≤ (1/3 : ℝ))]
        _ = √(2/9) := by norm_num
        _ = √2 / √9 := by rw [Real.sqrt_div (by norm_num) _]
        _ = √2 / 3 := by norm_num
    have h_target : (ρ * c0 + σ0) ^ 2 = ρ ^ 2 / 3 + 2 * √2 * ρ / 3 + 2 / 3 := by
      rw [hc0_def, hσ0_def]
      calc
        (ρ * √(1/3) + √(2/3)) ^ 2
            = ρ ^ 2 * (√(1/3)) ^ 2 + 2 * ρ * √(1/3) * √(2/3) + (√(2/3)) ^ 2 := by ring
        _ = ρ ^ 2 * (1/3) + 2 * ρ * (√(1/3) * √(2/3)) + (2/3) := by
          rw [Real.sq_sqrt (by norm_num : 0 ≤ (1/3 : ℝ)), Real.sq_sqrt (by norm_num : 0 ≤ (2/3 : ℝ))]
          ring
        _ = ρ ^ 2 * (1/3) + 2 * ρ * (√2 / 3) + (2/3) := by rw [h_sqrt_prod]
        _ = ρ ^ 2 / 3 + 2 * √2 * ρ / 3 + 2 / 3 := by ring
    rw [hc_def, hσ_def]
    calc
      (ρ * √(1 - s) + √s) ^ 2 = (ρ * c + σ) ^ 2 := by rfl
      _ ≤ (ρ * c0 + σ0) ^ 2 := h_sq_ineq
      _ = ρ ^ 2 / 3 + 2 * √2 * ρ / 3 + 2 / 3 := h_target

theorem q_antitone : AntitoneOn (fun ρ : ℝ => m2 ρ - ρ ^ 2) (Ici 0) := by
  intro a ha b hb hle
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  dsimp
  unfold m2
  split_ifs with hb_sq ha_sq
  · -- both ≤ 1/2: q(a) = 1, q(b) = 1
    nlinarith
  · -- b² ≤ 1/2 < a², but a ≤ b and both ≥ 0 implies a² ≤ b², contradiction
    have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith
  · -- a² ≤ 1/2 < b²: q(a) = 1, q(b) = -2b²/3 + 2√2b/3 + 2/3 ≤ 1
    nlinarith
  · -- both > 1/2: q(b) ≤ q(a)
    have ha_gt : Real.sqrt 2 / 2 < a := by
      have hsq_eq : (Real.sqrt 2 / 2) ^ 2 = 1/2 := by
        ring_nf
        rw [hsq2]
        norm_num
      nlinarith
    have hb_gt : Real.sqrt 2 / 2 < b := by
      have hsq_eq : (Real.sqrt 2 / 2) ^ 2 = 1/2 := by
        ring_nf
        rw [hsq2]
        norm_num
      nlinarith
    nlinarith

theorem m2_monotone : MonotoneOn m2 (Ici 0) := by
  intro a ha b hb hle
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hsq2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
  have hsq2nonneg : 0 ≤ Real.sqrt 2 := le_of_lt hsq2pos
  have hsq2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  dsimp [m2]
  by_cases ha_sq : a ^ 2 ≤ 1 / 2
  · rw [ite_eq_left ha_sq]
    by_cases hb_sq : b ^ 2 ≤ 1 / 2
    · rw [ite_eq_left hb_sq]
      have ha_sq_le : a ^ 2 ≤ b ^ 2 := by
        nlinarith
      nlinarith
    · rw [ite_eq_right hb_sq]
      have hb_sq_gt : 1 / 2 < b ^ 2 := by linarith
      have hb_gt_sqrt2_div_2 : Real.sqrt 2 / 2 ≤ b := by
        have hhalf_nonneg : 0 ≤ (1/2 : ℝ) := by norm_num
        have h_sqrt_lt_sq : Real.sqrt (1/2) < Real.sqrt (b ^ 2) :=
          Real.sqrt_lt_sqrt hhalf_nonneg hb_sq_gt
        have h_sqrt_sq_eq : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb0
        rw [h_sqrt_sq_eq] at h_sqrt_lt_sq
        have h_sqrt_eq : Real.sqrt (1/2) = Real.sqrt 2 / 2 := by
          calc
            Real.sqrt (1/2) = Real.sqrt 1 / Real.sqrt 2 := Real.sqrt_div (by norm_num) 2
            _ = 1 / Real.sqrt 2 := by norm_num
            _ = Real.sqrt 2 / 2 := by
              field_simp [ne_of_gt hsq2pos]
              nlinarith [hsq2sq]
        linarith
      have hleft : 1 + a ^ 2 ≤ 3/2 := by nlinarith
      have hright : 3/2 ≤ b ^ 2 / 3 + 2 * Real.sqrt 2 * b / 3 + 2/3 := by
        have h_nonneg : 0 ≤ 2 * b ^ 2 + 4 * Real.sqrt 2 * b - 5 := by
          have h_factor : 2 * b ^ 2 + 4 * Real.sqrt 2 * b - 5 =
              2 * (b - Real.sqrt 2 / 2) * (b + 5 * Real.sqrt 2 / 2) := by
            ring_nf
            rw [hsq2sq]
            ring_nf
          rw [h_factor]
          have h1 : 0 ≤ b - Real.sqrt 2 / 2 := by linarith
          have h2 : 0 ≤ b + 5 * Real.sqrt 2 / 2 := by
            nlinarith
          nlinarith
        nlinarith
      nlinarith
  · rw [ite_eq_right ha_sq]
    have hb_sq : 1 / 2 < b ^ 2 := by
      nlinarith
    rw [ite_eq_right (by linarith : ¬ b ^ 2 ≤ 1 / 2)]
    have h_ineq : a ^ 2 + 2 * Real.sqrt 2 * a ≤ b ^ 2 + 2 * Real.sqrt 2 * b := by
      have h_diff_nonpos : a - b ≤ 0 := by linarith
      have h_sum_nonneg : 0 ≤ a + b + 2 * Real.sqrt 2 := by
        nlinarith
      have h_prod_nonpos : (a - b) * (a + b + 2 * Real.sqrt 2) ≤ 0 := by
        nlinarith
      nlinarith
    nlinarith

/-! ### Monotonicity of the truncated series -/

theorem GamC_nonneg {E K : ℝ} (hE : 0 ≤ E) (hK : 0 ≤ K) (n : ℕ) : 0 ≤ GamC E K n := by
  unfold GamC; split_ifs <;> positivity

theorem GamC_mono {E K E' K' : ℝ} (hE' : E ≤ E') (hK' : K ≤ K') (n : ℕ) :
    GamC E K n ≤ GamC E' K' n := by
  unfold GamC
  split_ifs
  · linarith
  · have : (0 : ℝ) ≤ (kk n : ℝ) + 2 * kk (n - 1) := by positivity
    nlinarith

theorem gpN_mono {E K E' K' x x' : ℝ} (hE : 0 ≤ E) (hK : 0 ≤ K) (hE' : E ≤ E') (hK' : K ≤ K')
    (hx : 0 ≤ x) (hx' : x ≤ x') (N : ℕ) : gpN E K N x ≤ gpN E' K' N x' := by
  unfold gpN
  refine Finset.sum_le_sum fun n _ => ?_
  have h1 := GamC_mono hE' hK' (n + 1)
  have h2 := GamC_nonneg hE hK (n + 1)
  have h3 : x ^ n ≤ x' ^ n := pow_le_pow_left₀ hx hx' n
  have h4 : 0 ≤ x ^ n := pow_nonneg hx n
  have hf : (0 : ℝ) < ((2 * (n + 1)).factorial : ℝ) := by positivity
  rw [div_le_div_iff_of_pos_right hf]
  have h5 : GamC E K (n + 1) * x ^ n ≤ GamC E' K' (n + 1) * x' ^ n :=
    mul_le_mul h1 h3 h4 (h2.trans h1)
  have h6 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  calc ((n + 1 : ℕ) : ℝ) * GamC E K (n + 1) * x ^ n
        = ((n + 1 : ℕ) : ℝ) * (GamC E K (n + 1) * x ^ n) := by ring
    _ ≤ ((n + 1 : ℕ) : ℝ) * (GamC E' K' (n + 1) * x' ^ n) := mul_le_mul_of_nonneg_left h5 h6
    _ = _ := by ring

/-- The numeric core of a piece: the true constants replaced by their rational upper bounds. -/
theorem piece_core {q x : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x)
    (h : q * (gpN 0.6065306598 0.2798869 30 x + tailN 30 x) ≤ 2.7053) :
    q * (gpN (exp (-1 / 2)) K0 30 x + tailN 30 x) ≤ 2.7053 := by
  have hg := gpN_mono (exp_pos _).le K0_nonneg exp_neg_half_bounds.2 K0_le hx le_rfl 30
  refine le_trans ?_ h
  gcongr

/-! ### The 22 pieces -/

theorem piece_1 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (201653/200000 : ℝ) + tailN 30 (201653/200000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_2 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (516529/500000 : ℝ) + tailN 30 (516529/500000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_3 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (1074381/1000000 : ℝ) + tailN 30 (1074381/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_4 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (141529/125000 : ℝ) + tailN 30 (141529/125000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_5 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (301653/250000 : ℝ) + tailN 30 (301653/250000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_6 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (1297521/1000000 : ℝ) + tailN 30 (1297521/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_7 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (1404959/1000000 : ℝ) + tailN 30 (1404959/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_8 : (1 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (305731/200000 : ℝ) + tailN 30 (305731/200000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_9 : (999729/1000000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (1661197/1000000 : ℝ) + tailN 30 (1661197/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_10 : (39671/40000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (112453/62500 : ℝ) + tailN 30 (112453/62500 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_11 : (486401/500000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (194281/100000 : ℝ) + tailN 30 (194281/100000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_12 : (94281/100000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (52297/25000 : ℝ) + tailN 30 (52297/25000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_13 : (450899/500000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (2246461/1000000 : ℝ) + tailN 30 (2246461/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_14 : (849767/1000000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (2406551/1000000 : ℝ) + tailN 30 (2406551/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_15 : (196679/250000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (2572151/1000000 : ℝ) + tailN 30 (2572151/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_16 : (356323/500000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (137163/50000 : ℝ) + tailN 30 (137163/50000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_17 : (627557/1000000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (2919879/1000000 : ℝ) + tailN 30 (2919879/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_18 : (531449/1000000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (387751/125000 : ℝ) + tailN 30 (387751/125000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_19 : (212161/500000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (1644823/500000 : ℝ) + tailN 30 (1644823/500000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_20 : (12247/40000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (1741397/500000 : ℝ) + tailN 30 (1741397/500000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_21 : (177009/1000000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (3681451/1000000 : ℝ) + tailN 30 (3681451/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

theorem piece_22 : (36823/1000000 : ℝ) * (gpN (exp (-1 / 2)) K0 30 (3885619/1000000 : ℝ) + tailN 30 (3885619/1000000 : ℝ)) ≤ 2.7053 := by
  refine piece_core (by norm_num) (by norm_num) ?_
  simp only [gpN, tailN, GamC, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [kk, Nat.factorial]

/-! ### Assembly -/

theorem m2_le_of {a u : ℝ} (ha : 0 ≤ a)
    (h : (if a ^ 2 ≤ 1 / 2 then 1 + a ^ 2 else a ^ 2 / 3 + 2 * 1.4142136 * a / 3 + 2 / 3) ≤ u) :
    m2 a ≤ u := by
  have hs : √2 ≤ 1.4142136 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  unfold m2
  split_ifs at h ⊢ with h1
  · exact h
  · nlinarith

theorem q_le_of {a q : ℝ} (ha : 0 ≤ a)
    (h : (if a ^ 2 ≤ 1 / 2 then 1 + a ^ 2 else a ^ 2 / 3 + 2 * 1.4142136 * a / 3 + 2 / 3) - a ^ 2 ≤ q) :
    m2 a - a ^ 2 ≤ q := by
  have := m2_le_of (u := q + a ^ 2) ha (by linarith)
  linarith

theorem m2_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ m2 ρ := by
  unfold m2
  have := Real.sqrt_nonneg 2
  split_ifs <;> positivity

/-- For `ρ ≥ 2` the majorant is below `ρ²`. -/
theorem m2_le_sq {ρ : ℝ} (hρ : 2 ≤ ρ) : m2 ρ ≤ ρ ^ 2 := by
  have hs : √2 ≤ 1.4142136 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have h1 : ¬ ρ ^ 2 ≤ 1 / 2 := by nlinarith
  unfold m2
  rw [ite_eq_right h1]
  nlinarith

/-- One piece: if `a ≤ ρ ≤ b`, `q ≥ m2 a - a²`, `x ≥ m2 b` and the numeric bound holds, then
`G √(m2 ρ) - G ρ ≤ 2.7053/2`. -/
theorem piece_bound {ρ a b q x : ℝ} (ha : 0 ≤ a) (haρ : a ≤ ρ) (hρb : ρ ≤ b) (hq : m2 a - a ^ 2 ≤ q)
    (hx : m2 b ≤ x) (hnum : q * (gpN (exp (-1 / 2)) K0 30 x + tailN 30 x) ≤ 2.7053)
    (hx32 : x < 32) : Upper.G √(m2 ρ) - Upper.G ρ ≤ 2.7053 / 2 := by
  have hρ : 0 ≤ ρ := ha.trans haρ
  have hb : 0 ≤ b := hρ.trans hρb
  rcases le_or_gt (m2 ρ) (ρ ^ 2) with h | h
  · have : Upper.G √(m2 ρ) ≤ Upper.G ρ := by
      refine Upper.G_mono ?_
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hρ]
      exact Real.sqrt_le_left hρ |>.2 h
    linarith
  · have hY : 0 < m2 ρ := lt_of_le_of_lt (sq_nonneg ρ) h
    have hconv := G_sqrt_sub_le (sq_nonneg ρ) h.le hY
    rw [Real.sqrt_sq hρ] at hconv
    have hq' : m2 ρ - ρ ^ 2 ≤ q := (q_antitone (mem_Ici.2 ha) (mem_Ici.2 hρ) haρ).trans hq
    have hmx : m2 ρ ≤ x := (m2_monotone (mem_Ici.2 hρ) (mem_Ici.2 hb) hρb).trans hx
    have hx0 : 0 < x := hY.trans_le hmx
    have hD := (Dg_mono hY hmx).trans (Dg_le hx0 hx32)
    have hD0 := Dg_nonneg hY
    have hq0 : 0 ≤ q := (sub_nonneg.2 h.le).trans hq'
    calc Upper.G √(m2 ρ) - Upper.G ρ ≤ (m2 ρ - ρ ^ 2) * Dg (m2 ρ) := hconv
      _ ≤ q * ((gpN (exp (-1 / 2)) K0 30 x + tailN 30 x) / 2) :=
          mul_le_mul hq' hD hD0 hq0
      _ ≤ 2.7053 / 2 := by linarith

/-- The pieces cover `[0, ∞)`. -/
theorem psi_le {ρ : ℝ} (hρ : 0 ≤ ρ) : Upper.G √(m2 ρ) - Upper.G ρ ≤ 2.7053 / 2 := by
  by_cases h1 : ρ ≤ 1/11
  · exact piece_bound (a := 0) (b := 1/11) (q := 1) (x := 201653/200000) (by norm_num) hρ h1
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_1 (by norm_num)
  by_cases h2 : ρ ≤ 2/11
  · exact piece_bound (a := 1/11) (b := 2/11) (q := 1) (x := 516529/500000) (by norm_num) (by linarith) h2
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_2 (by norm_num)
  by_cases h3 : ρ ≤ 3/11
  · exact piece_bound (a := 2/11) (b := 3/11) (q := 1) (x := 1074381/1000000) (by norm_num) (by linarith) h3
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_3 (by norm_num)
  by_cases h4 : ρ ≤ 4/11
  · exact piece_bound (a := 3/11) (b := 4/11) (q := 1) (x := 141529/125000) (by norm_num) (by linarith) h4
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_4 (by norm_num)
  by_cases h5 : ρ ≤ 5/11
  · exact piece_bound (a := 4/11) (b := 5/11) (q := 1) (x := 301653/250000) (by norm_num) (by linarith) h5
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_5 (by norm_num)
  by_cases h6 : ρ ≤ 6/11
  · exact piece_bound (a := 5/11) (b := 6/11) (q := 1) (x := 1297521/1000000) (by norm_num) (by linarith) h6
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_6 (by norm_num)
  by_cases h7 : ρ ≤ 7/11
  · exact piece_bound (a := 6/11) (b := 7/11) (q := 1) (x := 1404959/1000000) (by norm_num) (by linarith) h7
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_7 (by norm_num)
  by_cases h8 : ρ ≤ 8/11
  · exact piece_bound (a := 7/11) (b := 8/11) (q := 1) (x := 305731/200000) (by norm_num) (by linarith) h8
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_8 (by norm_num)
  by_cases h9 : ρ ≤ 9/11
  · exact piece_bound (a := 8/11) (b := 9/11) (q := 999729/1000000) (x := 1661197/1000000) (by norm_num) (by linarith) h9
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_9 (by norm_num)
  by_cases h10 : ρ ≤ 10/11
  · exact piece_bound (a := 9/11) (b := 10/11) (q := 39671/40000) (x := 112453/62500) (by norm_num) (by linarith) h10
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_10 (by norm_num)
  by_cases h11 : ρ ≤ 1
  · exact piece_bound (a := 10/11) (b := 1) (q := 486401/500000) (x := 194281/100000) (by norm_num) (by linarith) h11
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_11 (by norm_num)
  by_cases h12 : ρ ≤ 12/11
  · exact piece_bound (a := 1) (b := 12/11) (q := 94281/100000) (x := 52297/25000) (by norm_num) (by linarith) h12
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_12 (by norm_num)
  by_cases h13 : ρ ≤ 13/11
  · exact piece_bound (a := 12/11) (b := 13/11) (q := 450899/500000) (x := 2246461/1000000) (by norm_num) (by linarith) h13
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_13 (by norm_num)
  by_cases h14 : ρ ≤ 14/11
  · exact piece_bound (a := 13/11) (b := 14/11) (q := 849767/1000000) (x := 2406551/1000000) (by norm_num) (by linarith) h14
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_14 (by norm_num)
  by_cases h15 : ρ ≤ 15/11
  · exact piece_bound (a := 14/11) (b := 15/11) (q := 196679/250000) (x := 2572151/1000000) (by norm_num) (by linarith) h15
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_15 (by norm_num)
  by_cases h16 : ρ ≤ 16/11
  · exact piece_bound (a := 15/11) (b := 16/11) (q := 356323/500000) (x := 137163/50000) (by norm_num) (by linarith) h16
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_16 (by norm_num)
  by_cases h17 : ρ ≤ 17/11
  · exact piece_bound (a := 16/11) (b := 17/11) (q := 627557/1000000) (x := 2919879/1000000) (by norm_num) (by linarith) h17
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_17 (by norm_num)
  by_cases h18 : ρ ≤ 18/11
  · exact piece_bound (a := 17/11) (b := 18/11) (q := 531449/1000000) (x := 387751/125000) (by norm_num) (by linarith) h18
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_18 (by norm_num)
  by_cases h19 : ρ ≤ 19/11
  · exact piece_bound (a := 18/11) (b := 19/11) (q := 212161/500000) (x := 1644823/500000) (by norm_num) (by linarith) h19
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_19 (by norm_num)
  by_cases h20 : ρ ≤ 20/11
  · exact piece_bound (a := 19/11) (b := 20/11) (q := 12247/40000) (x := 1741397/500000) (by norm_num) (by linarith) h20
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_20 (by norm_num)
  by_cases h21 : ρ ≤ 21/11
  · exact piece_bound (a := 20/11) (b := 21/11) (q := 177009/1000000) (x := 3681451/1000000) (by norm_num) (by linarith) h21
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_21 (by norm_num)
  by_cases h22 : ρ ≤ 2
  · exact piece_bound (a := 21/11) (b := 2) (q := 36823/1000000) (x := 3885619/1000000) (by norm_num) (by linarith) h22
      (q_le_of (by norm_num) (by norm_num))
      (m2_le_of (by norm_num) (by norm_num)) piece_22 (by norm_num)
  have h2 : 2 ≤ ρ := by linarith
  have : Upper.G √(m2 ρ) ≤ Upper.G ρ := by
    refine Upper.G_mono ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hρ]
    exact (Real.sqrt_le_left hρ).2 (m2_le_sq h2)
  linarith

/-- **Large steps** (in the units of `G`): for `2/3 ≤ b² ≤ 1`,
`max (G (ρ c + b)) (G (ρ c - b)) ≤ G ρ + 2.7053/2` with `c = √(1 - b²)`. -/
theorem large_step_sharp (ρ : ℝ) {b : ℝ} (hb1 : 2 / 3 ≤ b ^ 2) (hb2 : b ^ 2 ≤ 1) :
    max (Upper.G (ρ * √(1 - b ^ 2) + b)) (Upper.G (ρ * √(1 - b ^ 2) - b)) ≤
      Upper.G ρ + 2.7053 / 2 := by
  set c := √(1 - b ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hsb : √(b ^ 2) = |b| := Real.sqrt_sq_eq_abs b
  have hgeo := m2_ge (abs_nonneg ρ) hb1 hb2
  rw [hsb] at hgeo
  have hr0 : 0 ≤ |ρ| * c + |b| := by positivity
  have hle : |ρ| * c + |b| ≤ √(m2 |ρ|) := Real.le_sqrt_of_sq_le hgeo
  have hpsi := psi_le (abs_nonneg ρ)
  rw [Upper.G_abs] at hpsi
  have key : ∀ e : ℝ, |e| = |b| → Upper.G (ρ * c + e) ≤ Upper.G ρ + 2.7053 / 2 := by
    intro e he
    have h1 : |ρ * c + e| ≤ |√(m2 |ρ|)| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      calc |ρ * c + e| ≤ |ρ * c| + |e| := abs_add_le _ _
        _ = |ρ| * c + |b| := by rw [abs_mul, abs_of_nonneg hc0, he]
        _ ≤ _ := hle
    have := Upper.G_mono h1
    linarith
  refine max_le (key b rfl) ?_
  have := key (-b) (abs_neg b)
  rwa [← sub_eq_add_neg] at this

end RegretKappa.UpperSharp
