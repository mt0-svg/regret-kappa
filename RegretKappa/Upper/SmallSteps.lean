import RegretKappa.Upper.Gamma

/-!
# Upper bound: small steps, `b² ≤ 3/4`

The paper, Lemmas 3.9 and 3.10, with a cruder constant. With `c = √(1 - b²)`, the
substitution `u = c θ` turns `Ghat (ρ c) b` into `∫_c^∞ cosh(u ρ) e^{-u²/2} (1/u + 2c²/u³) du`
(the scale invariance of the weight `1/θ`); the part on `(c, 1]` is the cutoff drift, the part
on `(1, ∞)` differs from `G ρ` by `-2 b² J(ρ)`. Instead of the power series of the paper, the
proof splits `cosh z = 1 + z²/2 + Rf z` and uses `Rf (u z) ≤ u⁴ Rf z` for `u ≤ 1` and the
reverse for `u ≥ 1`: the terms of order at least four of the drift are then negative, and
`Ghat (ρ c) b - G ρ ≤ b² (3 + 3ρ²/4 - ρ⁴/80) ≤ 12`.
-/

namespace RegretKappa.Upper

open Real MeasureTheory Set

theorem Rf_scale_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (z : ℝ) : Rf (u * z) ≤ u ^ 4 * Rf z := by
  set f := fun n : ℕ => (z ^ (2 * n)) / ((2 * n).factorial : ℝ) with hf
  have hcosh : HasSum f (cosh z) := Real.hasSum_cosh z
  have hRf : HasSum (fun n : ℕ => f (n + 2)) (Rf z) := by
    have hsum : HasSum f ((Rf z) + (∑ i ∈ Finset.range 2, f i)) := by
      have : (∑ i ∈ Finset.range 2, f i) = f 0 + f 1 := by
        simp [Finset.sum_range_succ]
      simpa [Rf, f, this] using hcosh
    exact ((hasSum_nat_add_iff 2).mpr hsum)
  have hcosh_u : HasSum (fun n : ℕ => ((u * z) ^ (2 * n)) / ((2 * n).factorial : ℝ)) (cosh (u * z)) :=
    Real.hasSum_cosh (u * z)
  set fu := fun n : ℕ => ((u * z) ^ (2 * n)) / ((2 * n).factorial : ℝ) with hfu
  have hRf_u : HasSum (fun n : ℕ => fu (n + 2)) (Rf (u * z)) := by
    have hsum : HasSum fu ((Rf (u * z)) + (∑ i ∈ Finset.range 2, fu i)) := by
      have : (∑ i ∈ Finset.range 2, fu i) = fu 0 + fu 1 := by
        simp [Finset.sum_range_succ]
      simpa [Rf, fu, this] using hcosh_u
    exact ((hasSum_nat_add_iff 2).mpr hsum)
  have h_ineq : ∀ n : ℕ, fu (n + 2) ≤ u ^ 4 * f (n + 2) := by
    intro n
    dsimp [fu, f]
    have h_pow : (u * z) ^ (2 * (n + 2)) = u ^ (2 * (n + 2)) * z ^ (2 * (n + 2)) := by
      ring
    rw [h_pow]
    have hz_nonneg : 0 ≤ z ^ (2 * (n + 2)) := by
      have h_even : Even (2 * (n + 2)) := by
        use n + 2
        ring
      exact h_even.pow_nonneg z
    have h_fact_pos : 0 < ((2 * (n + 2)).factorial : ℝ) := by
      exact mod_cast Nat.factorial_pos _
    have h_term_nonneg : 0 ≤ (z ^ (2 * (n + 2))) / ((2 * (n + 2)).factorial : ℝ) :=
      div_nonneg hz_nonneg (by positivity)
    have h_pow_le : u ^ (2 * (n + 2)) ≤ u ^ 4 := by
      have h_exp_le : 4 ≤ 2 * (n + 2) := by
        omega
      have h_pow_nonneg : 0 ≤ u ^ 4 := pow_nonneg hu0 4
      have h_base_le_one : u ≤ 1 := hu1
      -- For 0 ≤ u ≤ 1 and 4 ≤ m, u^m ≤ u^4
      -- Use pow_le_pow_of_le_one
      exact pow_le_pow_of_le_one hu0 hu1 (by omega)
    calc
      (u ^ (2 * (n + 2)) * z ^ (2 * (n + 2))) / ((2 * (n + 2)).factorial : ℝ)
          = (u ^ (2 * (n + 2))) * ((z ^ (2 * (n + 2))) / ((2 * (n + 2)).factorial : ℝ)) := by ring
      _ ≤ (u ^ 4) * ((z ^ (2 * (n + 2))) / ((2 * (n + 2)).factorial : ℝ)) := by
        nlinarith
      _ = u ^ 4 * ((z ^ (2 * (n + 2))) / ((2 * (n + 2)).factorial : ℝ)) := by ring
  have hRf_u' : HasSum (fun n : ℕ => u ^ 4 * f (n + 2)) (u ^ 4 * Rf z) := by
    simpa using HasSum.mul_left (u ^ 4) hRf
  exact hasSum_le h_ineq hRf_u hRf_u'

theorem Rf_scale_ge {u : ℝ} (hu : 1 ≤ u) (z : ℝ) : u ^ 4 * Rf z ≤ Rf (u * z) := by
  -- Rf z = cosh z - 1 - z^2/2
  -- Use the power series: cosh z = ∑_{n≥0} z^(2n)/(2n)!
  -- Rf z = ∑_{n≥2} z^(2n)/(2n)!
  have hcosh := Real.hasSum_cosh z
  have hcosh_uz := Real.hasSum_cosh (u * z)
  -- Define the term function f(n) = z^(2n)/(2n)!
  set f := fun (n : ℕ) => z ^ (2 * n) / ((2 * n).factorial : ℝ) with hf
  have hsum2 : (∑ i ∈ Finset.range 2, f i) = 1 + z ^ 2 / 2 := by
    dsimp [f]
    simp [Finset.sum_range_succ, show (2 * 0 : ℕ) = 0 by norm_num, show (2 * 1 : ℕ) = 2 by norm_num]
  -- Get the tail sum for Rf z
  have hRf_hasSum : HasSum (fun n => f (n + 2)) (Rf z) := by
    -- Rf z = cosh z - 1 - z^2/2
    have hRf_eq : Rf z = cosh z - 1 - z ^ 2 / 2 := rfl
    -- Use the reverse direction of hasSum_nat_add_iff
    -- Need: HasSum f (Rf z + ∑ i ∈ range 2, f i) = HasSum f (cosh z)
    apply ((hasSum_nat_add_iff 2).mpr)
    -- Goal: HasSum f (Rf z + ∑ i ∈ Finset.range 2, f i)
    rw [hRf_eq, hsum2]
    -- Goal: HasSum f ((cosh z - 1 - z ^ 2 / 2) + (1 + z ^ 2 / 2))
    have : (cosh z - 1 - z ^ 2 / 2) + (1 + z ^ 2 / 2) = cosh z := by ring
    rw [this]
    exact hcosh
  -- Define the term function for u*z
  set f_uz := fun (n : ℕ) => (u * z) ^ (2 * n) / ((2 * n).factorial : ℝ) with hf_uz
  have hsum2_uz : (∑ i ∈ Finset.range 2, f_uz i) = 1 + (u * z) ^ 2 / 2 := by
    dsimp [f_uz]
    simp [Finset.sum_range_succ, show (2 * 0 : ℕ) = 0 by norm_num, show (2 * 1 : ℕ) = 2 by norm_num]
  -- Get the tail sum for Rf (u*z)
  have hRf_uz_hasSum : HasSum (fun n => f_uz (n + 2)) (Rf (u * z)) := by
    have hRf_uz_eq : Rf (u * z) = cosh (u * z) - 1 - (u * z) ^ 2 / 2 := rfl
    apply ((hasSum_nat_add_iff 2).mpr)
    rw [hRf_uz_eq, hsum2_uz]
    have : (cosh (u * z) - 1 - (u * z) ^ 2 / 2) + (1 + (u * z) ^ 2 / 2) = cosh (u * z) := by ring
    rw [this]
    exact hcosh_uz
  -- Now compare termwise
  have hterm : ∀ n, u ^ 4 * f (n + 2) ≤ f_uz (n + 2) := by
    intro n
    dsimp [f, f_uz]
    -- Goal: u^4 * (z^(2*(n+2)) / D) ≤ (u*z)^(2*(n+2)) / D
    set D := ((2 * (n + 2)).factorial : ℝ) with hD
    -- Rewrite RHS using mul_pow
    have hRHS : (u * z) ^ (2 * (n + 2)) / D = (u ^ (2 * (n + 2)) * z ^ (2 * (n + 2))) / D := by
      rw [mul_pow]
    rw [hRHS]
    -- Goal: u^4 * (z^(2*(n+2)) / D) ≤ (u^(2*(n+2)) * z^(2*(n+2))) / D
    -- Rewrite LHS using mul_div
    rw [mul_div]
    -- Goal: (u^4 * z^(2*(n+2))) / D ≤ (u^(2*(n+2)) * z^(2*(n+2))) / D
    have hDpos : 0 < D := Nat.cast_pos.mpr (Nat.factorial_pos _)
    rw [div_le_div_iff_of_pos_right hDpos]
    -- Goal: u^4 * z^(2*(n+2)) ≤ u^(2*(n+2)) * z^(2*(n+2))
    have hz_nonneg : 0 ≤ z ^ (2 * (n + 2)) := by
      have : z ^ (2 * (n + 2)) = (z ^ (n + 2)) ^ 2 := by ring
      rw [this]
      apply pow_two_nonneg
    refine mul_le_mul_of_nonneg_right ?_ hz_nonneg
    -- Goal: u^4 ≤ u^(2*(n+2))
    have h_exp : 4 ≤ 2 * (n + 2) := by omega
    exact pow_le_pow_right₀ hu h_exp
  -- Now use hasSum_le to compare the two series
  have h_mul : HasSum (fun n => u ^ 4 * f (n + 2)) (u ^ 4 * Rf z) := by
    simpa using hRf_hasSum.mul_left (u ^ 4)
  -- Compare termwise using hasSum_le
  have h_final : u ^ 4 * Rf z ≤ Rf (u * z) :=
    hasSum_le hterm h_mul hRf_uz_hasSum
  exact h_final

theorem Rf_ge (z : ℝ) : z ^ 4 / 24 ≤ Rf z := by
  let f : ℕ → ℝ := fun n => z ^ (2 * n) / ((2 * n).factorial : ℝ)
  have hcosh : HasSum f (cosh z) := Real.hasSum_cosh z
  have hRf : Rf z = cosh z - 1 - z ^ 2 / 2 := rfl
  have hsum_range : (∑ i ∈ Finset.range 2, f i) = 1 + z ^ 2 / 2 := by
    calc
      (∑ i ∈ Finset.range 2, f i) = f 0 + f 1 := by
        simp [Finset.sum_range_succ]
      _ = (z ^ 0 / ((0).factorial : ℝ)) + (z ^ 2 / ((2).factorial : ℝ)) := rfl
      _ = 1 + z ^ 2 / 2 := by norm_num
  have hsum_eq : (cosh z - 1 - z ^ 2 / 2) + (∑ i ∈ Finset.range 2, f i) = cosh z := by
    rw [hsum_range]
    ring
  have hshift : HasSum (fun n => f (n + 2)) (Rf z) := by
    apply ((hasSum_nat_add_iff (G := ℝ) 2).mpr ?_)
    rw [hRf, hsum_range]
    ring_nf
    exact hcosh
  have h_nonneg : ∀ j, 0 ≤ f (j + 2) := by
    intro j
    dsimp [f]
    have h_num : 0 ≤ z ^ (2 * (j + 2)) := by
      have : z ^ (2 * (j + 2)) = (z ^ 2) ^ (j + 2) := by
        rw [← pow_mul, mul_comm, pow_mul]
      rw [this]
      apply pow_nonneg (sq_nonneg z)
    have h_den : 0 ≤ ((2 * (j + 2)).factorial : ℝ) := by exact Nat.cast_nonneg _
    exact div_nonneg h_num h_den
  have h_le := le_hasSum hshift 0 (by
    intro j hj_ne
    apply h_nonneg j)
  simpa [f, show ((4:ℕ).factorial : ℝ) = 24 by norm_num] using h_le

theorem integral_J2 : ∫ u in Ioi (1 : ℝ), u * exp (-u ^ 2 / 2) = exp (-1 / 2) := by
  set f : ℝ → ℝ := fun u => -exp (-u ^ 2 / 2) with hf
  set f' : ℝ → ℝ := fun u => u * exp (-u ^ 2 / 2) with hf'
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    dsimp [f, f']
    have h_deriv_inner : HasDerivAt (fun (u : ℝ) => -u ^ 2 / 2) (-x) x := by
      have h_sq : HasDerivAt (fun (u : ℝ) => u ^ 2) (2 * x) x := by
        simpa [two_mul] using hasDerivAt_pow 2 x
      have h_neg_sq : HasDerivAt (fun (u : ℝ) => -(u ^ 2)) (-(2 * x)) x :=
        HasDerivAt.neg h_sq
      have h_div : HasDerivAt (fun (u : ℝ) => -(u ^ 2) / 2) (-(2 * x) / 2) x := by
        simpa using HasDerivAt.div_const h_neg_sq 2
      simpa [show -(2 * x) / 2 = -x by ring] using h_div
    have h_exp : HasDerivAt (fun (u : ℝ) => exp (-u ^ 2 / 2)) (exp (-x ^ 2 / 2) * (-x)) x := by
      have := ((Real.hasDerivAt_exp (-x ^ 2 / 2)).comp x h_deriv_inner)
      simpa [Function.comp_def] using this
    have h_neg_exp : HasDerivAt (fun (u : ℝ) => -exp (-u ^ 2 / 2)) (-(exp (-x ^ 2 / 2) * (-x))) x :=
      HasDerivAt.neg h_exp
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul, mul_neg] using h_neg_exp
  have hint : IntegrableOn f' (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
    dsimp [f']
    have h_int : Integrable (fun (u : ℝ) => u * Real.exp (-((1/2 : ℝ)) * u ^ 2)) MeasureTheory.volume := by
      simpa using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    have h_eq : (fun (u : ℝ) => u * Real.exp (-u ^ 2 / 2)) = (fun (u : ℝ) => u * Real.exp (-((1/2 : ℝ)) * u ^ 2)) := by
      ext u
      congr
      ring
    rw [h_eq]
    exact h_int.integrableOn
  have htendsto : Filter.Tendsto f Filter.atTop (nhds (0 : ℝ)) := by
    dsimp [f]
    have h_arg_tendsto : Filter.Tendsto (fun (u : ℝ) => -u ^ 2 / 2) Filter.atTop Filter.atBot := by
      have : (fun (u : ℝ) => -u ^ 2 / 2) = (fun (u : ℝ) => (-1/2) * u ^ 2) := by
        ext u; ring
      rw [this]
      simpa using Filter.tendsto_neg_const_mul_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (-1/2 : ℝ) < 0)
    have h_exp_tendsto : Filter.Tendsto (fun (u : ℝ) => exp (-u ^ 2 / 2)) Filter.atTop (nhds (0 : ℝ)) :=
      Real.tendsto_exp_atBot.comp h_arg_tendsto
    simpa using h_exp_tendsto.neg
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htendsto
  simpa [f, hf] using h

/-- The integrand after the substitution `u = c θ`. -/
theorem integrableOn_h (ρ : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u => cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)) (Ioi c) := by
  refine integrableOn_Ioi_of_le_gauss (M := 3 / c * exp (ρ ^ 2)) (by norm_num : 0 < (1 / 4 : ℝ)) ?_ ?_
  · have hne : ∀ u ∈ Ioi c, u ≠ 0 := fun u hu => (lt_trans hc hu).ne'
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.add ?_ ?_)
    · exact continuousOn_const.div continuousOn_id hne
    · exact continuousOn_const.div (continuousOn_id.pow 3) fun u hu => pow_ne_zero 3 (hne u hu)
  · intro u hu
    have hu0 : 0 < u := lt_trans hc hu
    have hcu : c < u := hu
    have hW0 : 0 ≤ 1 / u + 2 * c ^ 2 / u ^ 3 := by positivity
    have hW : 1 / u + 2 * c ^ 2 / u ^ 3 ≤ 3 / c := by
      have h1 : 1 / u ≤ 1 / c := one_div_le_one_div_of_le hc hcu.le
      have h2 : 2 * c ^ 2 / u ^ 3 ≤ 2 / c := by
        rw [div_le_div_iff₀ (by positivity) hc]
        have : c ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hc.le hcu.le 3
        nlinarith
      have : 3 / c = 1 / c + 2 / c := by ring
      linarith
    have hpos : 0 ≤ cosh (u * ρ) * exp (-u ^ 2 / 2) := by positivity
    rw [abs_of_nonneg (mul_nonneg hpos hW0)]
    have hce : cosh (u * ρ) * exp (-u ^ 2 / 2) ≤ exp (ρ ^ 2) * exp (-(1 / 4) * u ^ 2) := by
      have h1 := cosh_le_exp_abs_u (u * ρ)
      rw [abs_mul, abs_of_pos hu0] at h1
      calc cosh (u * ρ) * exp (-u ^ 2 / 2) ≤ exp (u * |ρ|) * exp (-u ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right h1 (exp_pos _).le
        _ = exp (u * |ρ| - u ^ 2 / 2) := by rw [← exp_add]; ring_nf
        _ ≤ exp (ρ ^ 2 + -(1 / 4) * u ^ 2) := by
            apply exp_le_exp.mpr
            nlinarith [sq_nonneg (u / 2 - |ρ|), sq_abs ρ]
        _ = exp (ρ ^ 2) * exp (-(1 / 4) * u ^ 2) := exp_add _ _
    calc cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)
        ≤ exp (ρ ^ 2) * exp (-(1 / 4) * u ^ 2) * (3 / c) := mul_le_mul hce hW hW0 (by positivity)
      _ = 3 / c * exp (ρ ^ 2) * exp (-(1 / 4) * u ^ 2) := by ring

/-- Lemma 3.9 of the paper, first half: the substitution `u = c θ`. -/
theorem Ghat_subst (ρ : ℝ) {b c : ℝ} (hc : 0 < c) (hcb : c ^ 2 + b ^ 2 = 1) :
    Ghat (ρ * c) b = ∫ u in Ioi c, cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) := by
  have hc_ne : c ≠ 0 := by linarith
  have hb2 : b ^ 2 = 1 - c ^ 2 := by linarith
  set h := fun (u : ℝ) => cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) with hh
  have h_pointwise : ∀ θ, θ ∈ Ioi (1 : ℝ) → cosh (θ * (ρ * c)) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ = c * h (c * θ) := by
    intro θ hθ
    dsimp [h, wt]
    have h_exp : exp (θ ^ 2 * b ^ 2 / 2) * exp (-θ ^ 2 / 2) = exp (-(c * θ) ^ 2 / 2) := by
      calc
        exp (θ ^ 2 * b ^ 2 / 2) * exp (-θ ^ 2 / 2) = exp ((θ ^ 2 * b ^ 2 / 2) + (-θ ^ 2 / 2)) := by rw [Real.exp_add]
        _ = exp (θ ^ 2 * (b ^ 2 - 1) / 2) := by ring_nf
        _ = exp (θ ^ 2 * (-c ^ 2) / 2) := by rw [hb2]; ring_nf
        _ = exp (-(c * θ) ^ 2 / 2) := by ring_nf
    calc
      cosh (θ * (ρ * c)) * exp (θ ^ 2 * b ^ 2 / 2) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))
          = cosh (θ * (ρ * c)) * (exp (θ ^ 2 * b ^ 2 / 2) * exp (-θ ^ 2 / 2)) * (1 / θ + 2 / θ ^ 3) := by ring
      _ = cosh (θ * (ρ * c)) * exp (-(c * θ) ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := by rw [h_exp]
      _ = cosh (θ * ρ * c) * exp (-(c * θ) ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := by ring_nf
      _ = c * (cosh ((c * θ) * ρ) * exp (-(c * θ) ^ 2 / 2) * (1 / (c * θ) + 2 * c ^ 2 / (c * θ) ^ 3)) := by
        field_simp [hc_ne]
  calc
    Ghat (ρ * c) b = ∫ θ in Ioi (1 : ℝ), cosh (θ * (ρ * c)) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ := rfl
    _ = (∫ θ in Ioi (1 : ℝ), c * h (c * θ)) := by
      rw [setIntegral_congr_fun measurableSet_Ioi h_pointwise]
    _ = c * (∫ θ in Ioi (1 : ℝ), h (c * θ)) := by rw [integral_const_mul]
    _ = c * (c⁻¹ • (∫ u in Ioi (c * (1 : ℝ)), h u)) := by rw [integral_comp_mul_left_Ioi h 1 hc]
    _ = c * (c⁻¹ • (∫ u in Ioi c, h u)) := by ring_nf
    _ = (c * c⁻¹) • (∫ u in Ioi c, h u) := by simp [smul_eq_mul, mul_assoc]
    _ = 1 • (∫ u in Ioi c, h u) := by
      field_simp [hc_ne]
      simp
    _ = (∫ u in Ioi c, h u) := by simp
    _ = ∫ u in Ioi c, cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) := rfl

/-- The pointwise majorant of the integrand on `(c, 1]`. -/
theorem integral_P_pt (ρ : ℝ) {c u : ℝ} (hc0 : 0 < c) (hcu : c < u) (hu1 : u ≤ 1) :
    cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) ≤
      (1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) +
        Rf ρ * exp (-c ^ 2 / 2) * (u ^ 3 + 2 * c ^ 2 * u) := by
  have hu0 : 0 < u := lt_trans hc0 hcu
  have hW : 0 < 1 / u + 2 * c ^ 2 / u ^ 3 := by positivity
  have hR0 : 0 ≤ Rf ρ := le_trans (by positivity) (Rf_ge ρ)
  have hcosh : cosh (u * ρ) ≤ 1 + u ^ 2 * ρ ^ 2 / 2 + u ^ 4 * Rf ρ := by
    have h := Rf_scale_le hu0.le hu1 ρ
    unfold Rf at h ⊢
    nlinarith
  have hE1 : exp (-u ^ 2 / 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hE2 : exp (-u ^ 2 / 2) ≤ exp (-c ^ 2 / 2) := exp_le_exp.mpr (by nlinarith)
  have hE0 := exp_pos (-u ^ 2 / 2)
  have e2 : u ^ 2 * (1 / u + 2 * c ^ 2 / u ^ 3) = u + 2 * c ^ 2 / u := by field_simp
  have e4 : u ^ 4 * (1 / u + 2 * c ^ 2 / u ^ 3) = u ^ 3 + 2 * c ^ 2 * u := by field_simp
  have hcoshE : cosh (u * ρ) * exp (-u ^ 2 / 2) ≤
      1 + u ^ 2 * ρ ^ 2 / 2 + u ^ 4 * (Rf ρ * exp (-c ^ 2 / 2)) := by
    have h4 : 0 ≤ u ^ 4 * Rf ρ := by positivity
    have h2 : 0 ≤ u ^ 2 * ρ ^ 2 / 2 := by positivity
    calc cosh (u * ρ) * exp (-u ^ 2 / 2) ≤ (1 + u ^ 2 * ρ ^ 2 / 2 + u ^ 4 * Rf ρ) * exp (-u ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hcosh hE0.le
      _ = (1 + u ^ 2 * ρ ^ 2 / 2) * exp (-u ^ 2 / 2) + u ^ 4 * Rf ρ * exp (-u ^ 2 / 2) := by ring
      _ ≤ (1 + u ^ 2 * ρ ^ 2 / 2) * 1 + u ^ 4 * Rf ρ * exp (-c ^ 2 / 2) := by
          gcongr
      _ = 1 + u ^ 2 * ρ ^ 2 / 2 + u ^ 4 * (Rf ρ * exp (-c ^ 2 / 2)) := by ring
  calc cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)
      ≤ (1 + u ^ 2 * ρ ^ 2 / 2 + u ^ 4 * (Rf ρ * exp (-c ^ 2 / 2))) * (1 / u + 2 * c ^ 2 / u ^ 3) :=
        mul_le_mul_of_nonneg_right hcoshE hW.le
    _ = (1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u ^ 2 * (1 / u + 2 * c ^ 2 / u ^ 3)) +
          Rf ρ * exp (-c ^ 2 / 2) * (u ^ 4 * (1 / u + 2 * c ^ 2 / u ^ 3)) := by ring
    _ = _ := by rw [e2, e4]

/-- The integral of the majorant, by its antiderivative. -/
theorem integral_P_ftc (ρ K : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ u in Ioc c 1, ((1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) + K * (u ^ 3 + 2 * c ^ 2 * u)) =
      (-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
        K * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) := by
  rw [← intervalIntegral.integral_of_le hc1]
  have hpos : ∀ x ∈ uIcc c 1, 0 < x := by
    intro x hx; rw [uIcc_of_le hc1] at hx; exact lt_of_lt_of_le hc0 hx.1
  have hderiv : ∀ x ∈ uIcc c 1, HasDerivAt
      (fun u => log u - c ^ 2 * (u ^ 2)⁻¹ + ρ ^ 2 / 2 * (u ^ 2 / 2 + 2 * c ^ 2 * log u) +
        K * (u ^ 4 / 4 + c ^ 2 * u ^ 2))
      ((1 / x + 2 * c ^ 2 / x ^ 3) + ρ ^ 2 / 2 * (x + 2 * c ^ 2 / x) + K * (x ^ 3 + 2 * c ^ 2 * x)) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    have h1 := Real.hasDerivAt_log hx0
    have h2 := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).const_mul (c ^ 2)
    have h3 := hasDerivAt_pow 2 x
    have h4 := hasDerivAt_pow 4 x
    have := ((h1.sub h2).add (((h3.div_const 2).add (h1.const_mul (2 * c ^ 2))).const_mul (ρ ^ 2 / 2))).add
      (((h4.div_const 4).add (h3.const_mul (c ^ 2))).const_mul K)
    convert this using 1
    norm_num
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => (1 / x + 2 * c ^ 2 / x ^ 3) + ρ ^ 2 / 2 * (x + 2 * c ^ 2 / x) +
      K * (x ^ 3 + 2 * c ^ 2 * x)) (uIcc c 1) := by
    have hne : ∀ x ∈ uIcc c 1, x ≠ 0 := fun x hx => (hpos x hx).ne'
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) (continuousOn_const.mul
      (continuousOn_id.add ?_))) (by fun_prop)
    · exact continuousOn_const.div continuousOn_id hne
    · exact continuousOn_const.div (continuousOn_id.pow 3) fun x hx => pow_ne_zero 3 (hne x hx)
    · exact continuousOn_const.div continuousOn_id hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [log_one]
  field_simp
  ring

/-- The cutoff drift on `(c, 1]`, by the antiderivative of a pointwise majorant. -/
theorem integral_P_le (ρ : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ u in Ioc c 1, cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) ≤
      (-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
        Rf ρ * exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) := by
  have hne : ∀ x ∈ Icc c 1, x ≠ 0 := fun x hx => (lt_of_lt_of_le hc0 hx.1).ne'
  have hint : IntegrableOn (fun u : ℝ => (1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) +
      Rf ρ * exp (-c ^ 2 / 2) * (u ^ 3 + 2 * c ^ 2 * u)) (Ioc c 1) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) (continuousOn_const.mul
      (continuousOn_id.add ?_))) (by fun_prop)
    · exact continuousOn_const.div continuousOn_id hne
    · exact continuousOn_const.div (continuousOn_id.pow 3) fun x hx => pow_ne_zero 3 (hne x hx)
    · exact continuousOn_const.div continuousOn_id hne
  calc _ ≤ ∫ u in Ioc c 1, ((1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) +
        Rf ρ * exp (-c ^ 2 / 2) * (u ^ 3 + 2 * c ^ 2 * u)) :=
        setIntegral_mono_on ((integrableOn_h ρ hc0).mono_set Ioc_subset_Ioi_self) hint measurableSet_Ioc
          fun u hu => integral_P_pt ρ hc0 hu.1 hu.2
    _ = _ := integral_P_ftc ρ _ hc0 hc1

/-- The pointwise bound on `(1, ∞)`. -/
theorem tail_pt (ρ : ℝ) {c u : ℝ} (hc1 : c ^ 2 ≤ 1) (hu : 1 < u) :
    cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) - cosh (u * ρ) * wt u ≤
      -2 * (1 - c ^ 2) * Rf ρ * (u * exp (-u ^ 2 / 2)) := by
  have hu0 : 0 < u := by linarith
  have hu3 : 0 < u ^ 3 := by positivity
  have hE := exp_pos (-u ^ 2 / 2)
  have hR := Rf_scale_ge hu.le ρ
  have hcosh : u ^ 4 * Rf ρ ≤ cosh (u * ρ) := by
    have : Rf (u * ρ) ≤ cosh (u * ρ) := by
      unfold Rf; nlinarith [sq_nonneg (u * ρ)]
    linarith
  have key : u * Rf ρ ≤ cosh (u * ρ) / u ^ 3 := by
    rw [le_div_iff₀ hu3]; nlinarith
  have heq : cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) - cosh (u * ρ) * wt u =
      -2 * (1 - c ^ 2) * exp (-u ^ 2 / 2) * (cosh (u * ρ) / u ^ 3) := by
    unfold wt; field_simp; ring
  rw [heq]
  have hneg : -2 * (1 - c ^ 2) * exp (-u ^ 2 / 2) ≤ 0 := by
    have : 0 ≤ (1 - c ^ 2) * exp (-u ^ 2 / 2) := mul_nonneg (by linarith) hE.le
    nlinarith
  have := mul_le_mul_of_nonpos_left key hneg
  calc -2 * (1 - c ^ 2) * exp (-u ^ 2 / 2) * (cosh (u * ρ) / u ^ 3)
      ≤ -2 * (1 - c ^ 2) * exp (-u ^ 2 / 2) * (u * Rf ρ) := this
    _ = -2 * (1 - c ^ 2) * Rf ρ * (u * exp (-u ^ 2 / 2)) := by ring

/-- The drift on `(1, ∞)`: at most `-2 (1 - c²) Rf(ρ) e^{-1/2}`. -/
theorem tail_le (ρ : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∫ u in Ioi 1, cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)) - G ρ ≤
      -2 * (1 - c ^ 2) * Rf ρ * exp (-1 / 2) := by
  have hi1 := (integrableOn_h ρ hc0).mono_set (Ioi_subset_Ioi hc1)
  have hi2 := integrableOn_G ρ
  have hJ : IntegrableOn (fun u : ℝ => u * exp (-u ^ 2 / 2)) (Ioi 1) := by
    have h := integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine (h.congr (Filter.Eventually.of_forall fun u => ?_)).integrableOn
    simp only; congr 2; ring
  unfold G
  rw [← integral_sub hi1 hi2, ← integral_J2, ← integral_const_mul]
  refine setIntegral_mono_on (hi1.sub hi2) (hJ.const_mul _) measurableSet_Ioi fun u hu => ?_
  exact tail_pt ρ (by nlinarith) hu

/-- The logarithmic terms for `1/2 ≤ c ≤ 1`. -/
theorem small_log {c : ℝ} (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    -log c ≤ 2 * (1 - c ^ 2) ∧ -(2 * c ^ 2 * log c) ≤ 1 - c ^ 2 := by
  have hc_pos : 0 < c := by linarith
  have h_nonneg_one_sub_c : 0 ≤ 1 - c := by linarith
  have h_log_bound : 1 - c⁻¹ ≤ log c := Real.one_sub_inv_le_log_of_pos hc_pos
  have h_neg_log_bound : -log c ≤ (1 - c) / c := by
    have h : -log c ≤ c⁻¹ - 1 := by linarith
    have h_eq : c⁻¹ - 1 = (1 - c) / c := by
      field_simp [hc_pos.ne.symm]
    rw [h_eq] at h
    exact h
  have h_first : -log c ≤ 2 * (1 - c ^ 2) := by
    have h_inv_le_two : c⁻¹ ≤ 2 := by
      have h : 1 ≤ 2 * c := by linarith
      calc
        c⁻¹ = c⁻¹ * 1 := by ring
        _ ≤ c⁻¹ * (2 * c) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 := by field_simp [hc_pos.ne.symm]
    have h_div_le : (1 - c) / c ≤ 2 * (1 - c) := by
      calc
        (1 - c) / c = (1 - c) * c⁻¹ := by ring
        _ ≤ (1 - c) * 2 := mul_le_mul_of_nonneg_left h_inv_le_two h_nonneg_one_sub_c
        _ = 2 * (1 - c) := by ring
    have h_sq_le : 2 * (1 - c) ≤ 2 * (1 - c ^ 2) := by
      have h : 1 - c ≤ 1 - c ^ 2 := by
        nlinarith
      linarith
    linarith
  have h_second : -(2 * c ^ 2 * log c) ≤ 1 - c ^ 2 := by
    have h_eq : -(2 * c ^ 2 * log c) = 2 * c ^ 2 * (-log c) := by ring
    rw [h_eq]
    have h_mul : 2 * c ^ 2 * (-log c) ≤ 2 * c ^ 2 * ((1 - c) / c) :=
      mul_le_mul_of_nonneg_left h_neg_log_bound (by nlinarith)
    have h_simp : 2 * c ^ 2 * ((1 - c) / c) = 2 * c * (1 - c) := by
      field_simp [hc_pos.ne.symm]
    rw [h_simp] at h_mul
    have h_final : 2 * c * (1 - c) ≤ 1 - c ^ 2 := by
      nlinarith
    linarith
  exact And.intro h_first h_second

/-- The cutoff factor of the terms of order at least four. -/
theorem small_exp {c : ℝ} (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) ≤ 3 / 2 * exp (-1 / 2) * (1 - c ^ 2) := by
  set s := 1 - c ^ 2 with hs
  have hs_nonneg : 0 ≤ s := by
    nlinarith
  have h_exp_add : exp (-c ^ 2 / 2) = exp (-1 / 2) * exp (s / 2) := by
    calc
      exp (-c ^ 2 / 2) = exp ((-1 / 2) + (s / 2)) := by
        unfold s
        ring_nf
      _ = exp (-1 / 2) * exp (s / 2) := by rw [Real.exp_add]
  have h_bracket_eq : (1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2) = s * (6 - 5 * s) / 4 := by
    unfold s
    ring
  have h_main : exp (s / 2) * (6 - 5 * s) ≤ 6 := by
    have h_exp_ineq : 1 - s / 2 ≤ exp (-s / 2) := by
      have h := Real.add_one_le_exp (-s / 2)
      linarith
    have h_key : 6 - 5 * s ≤ 6 * exp (-s / 2) := by
      calc
        6 - 5 * s ≤ 6 - 3 * s := by nlinarith
        _ = 6 * (1 - s / 2) := by ring
        _ ≤ 6 * exp (-s / 2) := by nlinarith
    calc
      exp (s / 2) * (6 - 5 * s) = (6 - 5 * s) * exp (s / 2) := by ring
      _ ≤ (6 * exp (-s / 2)) * exp (s / 2) := by
        apply mul_le_mul_of_nonneg_right h_key
        positivity
      _ = 6 * (exp (-s / 2) * exp (s / 2)) := by ring
      _ = 6 * exp ((-s / 2) + (s / 2)) := by rw [Real.exp_add]
      _ = 6 * exp 0 := by ring_nf
      _ = 6 * 1 := by rw [Real.exp_zero]
      _ = 6 := by ring
  rw [h_exp_add, h_bracket_eq]
  calc
    exp (-1 / 2) * exp (s / 2) * (s * (6 - 5 * s) / 4) = exp (-1 / 2) * (exp (s / 2) * (6 - 5 * s)) * (s / 4) := by ring
    _ ≤ exp (-1 / 2) * 6 * (s / 4) := by
      have hpos_s : 0 ≤ s / 4 := by nlinarith
      refine mul_le_mul_of_nonneg_right ?_ hpos_s
      have hpos_exp : 0 ≤ exp (-1 / 2) := by positivity
      refine mul_le_mul_of_nonneg_left h_main hpos_exp
    _ = 3 / 2 * exp (-1 / 2) * s := by ring
    _ = 3 / 2 * exp (-1 / 2) * (1 - c ^ 2) := by rfl

/-- `e^{-1/2} ≥ 3/5`. -/
theorem exp_neg_half_ge : 3 / 5 ≤ exp (-1 / 2 : ℝ) := by
  have hpos : 0 < exp (1/2 : ℝ) := Real.exp_pos _
  have h_5_3_pos : 0 < (5/3 : ℝ) := by norm_num
  have hsq : exp (1/2 : ℝ) ^ 2 = exp 1 := by
    calc
      exp (1/2 : ℝ) ^ 2 = Real.exp ((2 : ℕ) * (1/2 : ℝ)) := by
        rw [Real.exp_nat_mul]
      _ = exp 1 := by norm_num
  have h_exp1_lt : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_25_9_gt : (2.7182818286 : ℝ) < (25/9 : ℝ) := by norm_num
  have h_sq_lt : exp (1/2 : ℝ) ^ 2 < (5/3 : ℝ) ^ 2 := by
    nlinarith
  have h_lt : exp (1/2 : ℝ) < 5/3 := by
    nlinarith
  have h_le : exp (1/2 : ℝ) ≤ 5/3 := le_of_lt h_lt
  have h_neg : exp (-1/2 : ℝ) = (exp (1/2 : ℝ))⁻¹ := by
    calc
      exp (-1/2 : ℝ) = exp (-(1/2 : ℝ)) := by norm_num
      _ = (exp (1/2 : ℝ))⁻¹ := Real.exp_neg _
  rw [h_neg]
  have h_inv : (5/3 : ℝ)⁻¹ = 3/5 := by norm_num
  rw [← h_inv]
  simpa using (one_div_le_one_div h_5_3_pos hpos).mpr h_le

/-- The real inequality that closes Lemma 3.10. -/
theorem small_alg (ρ : ℝ) {c : ℝ} (hc0 : 1 / 2 ≤ c) (hc1 : c ≤ 1) :
    (-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
        Rf ρ * exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) +
      -2 * (1 - c ^ 2) * Rf ρ * exp (-1 / 2) ≤ 12 := by
  have h_small_log := small_log hc0 hc1
  have h_small_exp := small_exp hc0 hc1
  have h_exp_neg_half_ge := exp_neg_half_ge
  have h_Rf_ge : ρ ^ 4 / 24 ≤ Rf ρ := Rf_ge ρ
  have h_Rf_nonneg : 0 ≤ Rf ρ := by
    have hρ4 : 0 ≤ ρ ^ 4 := by positivity
    linarith
  have hs_nonneg : 0 ≤ 1 - c ^ 2 := by
    nlinarith
  have hs_le : 1 - c ^ 2 ≤ 3/4 := by
    nlinarith
  have h_log1 : -log c ≤ 2 * (1 - c ^ 2) := h_small_log.1
  have h_log2 : -(2 * c ^ 2 * log c) ≤ 1 - c ^ 2 := h_small_log.2
  have h_log2' : -2 * c ^ 2 * log c ≤ 1 - c ^ 2 := by linarith
  have h_term1 : -log c + (1 - c ^ 2) ≤ 3 * (1 - c ^ 2) := by
    linarith
  have h_term2 : ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) ≤ ρ ^ 2 / 2 * (3 * (1 - c ^ 2) / 2) := by
    have h_inner : (1 - c ^ 2) / 2 - 2 * c ^ 2 * log c ≤ 3 * (1 - c ^ 2) / 2 := by
      linarith
    have h_nonneg : 0 ≤ ρ ^ 2 / 2 := by nlinarith [sq_nonneg ρ]
    exact mul_le_mul_of_nonneg_left h_inner h_nonneg
  have h_term3 : Rf ρ * exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) ≤
      Rf ρ * (3 / 2 * exp (-1 / 2) * (1 - c ^ 2)) := by
    calc
      Rf ρ * exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2))
          = Rf ρ * (exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2))) := by ring
      _ ≤ Rf ρ * (3 / 2 * exp (-1 / 2) * (1 - c ^ 2)) := mul_le_mul_of_nonneg_left h_small_exp h_Rf_nonneg
  have h_total : (-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
      Rf ρ * exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) +
      -2 * (1 - c ^ 2) * Rf ρ * exp (-1 / 2) ≤
      3 * (1 - c ^ 2) + ρ ^ 2 / 2 * (3 * (1 - c ^ 2) / 2) + Rf ρ * (3 / 2 * exp (-1 / 2) * (1 - c ^ 2)) +
      -2 * (1 - c ^ 2) * Rf ρ * exp (-1 / 2) := by
    nlinarith
  have h_Rf_E_ge : ρ ^ 4 / 80 ≤ (1/2 : ℝ) * Rf ρ * exp (-1 / 2) := by
    have hprod : ρ ^ 4 / 24 * (3/5 : ℝ) ≤ Rf ρ * exp (-1 / 2) := by
      have hE_nonneg : 0 ≤ exp (-1/2 : ℝ) := by positivity
      have hρ4_nonneg : 0 ≤ ρ ^ 4 := by positivity
      nlinarith
    nlinarith
  calc
    (-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
        Rf ρ * exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) +
      -2 * (1 - c ^ 2) * Rf ρ * exp (-1 / 2)
        ≤ 3 * (1 - c ^ 2) + ρ ^ 2 / 2 * (3 * (1 - c ^ 2) / 2) + Rf ρ * (3 / 2 * exp (-1 / 2) * (1 - c ^ 2)) +
          -2 * (1 - c ^ 2) * Rf ρ * exp (-1 / 2) := h_total
    _ = (1 - c ^ 2) * (3 + (3/4 : ℝ) * ρ ^ 2 - (1/2 : ℝ) * Rf ρ * exp (-1 / 2)) := by ring
    _ ≤ (1 - c ^ 2) * (3 + (3/4 : ℝ) * ρ ^ 2 - ρ ^ 4 / 80) := by
      have h_inner : 3 + (3/4 : ℝ) * ρ ^ 2 - (1/2 : ℝ) * Rf ρ * exp (-1 / 2) ≤ 3 + (3/4 : ℝ) * ρ ^ 2 - ρ ^ 4 / 80 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left h_inner hs_nonneg
    _ ≤ (1 - c ^ 2) * (57/4 : ℝ) := by
      have h_inner : 3 + (3/4 : ℝ) * ρ ^ 2 - ρ ^ 4 / 80 ≤ (57/4 : ℝ) := by
        have h_sq_nonneg : 0 ≤ (ρ ^ 2 - 30) ^ 2 := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_left h_inner hs_nonneg
    _ ≤ 12 := by
      nlinarith

/-- Lemma 3.10 of the paper (constant `12`): for `b² ≤ 3/4`, `Ghat (ρ √(1 - b²)) b ≤ G ρ + 12`. -/
theorem small_step (ρ : ℝ) {b : ℝ} (hb : b ^ 2 ≤ 3 / 4) : Ghat (ρ * √(1 - b ^ 2)) b ≤ G ρ + 12 := by
  have hb0 : 0 ≤ 1 - b ^ 2 := by nlinarith [sq_nonneg b]
  have hc2 : √(1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt hb0
  have hcn := Real.sqrt_nonneg (1 - b ^ 2)
  have hc0 : 1 / 2 ≤ √(1 - b ^ 2) := by nlinarith
  have hc1 : √(1 - b ^ 2) ≤ 1 := by nlinarith
  have hcpos : 0 < √(1 - b ^ 2) := by linarith
  have hi := integrableOn_h ρ hcpos
  rw [Ghat_subst ρ hcpos (by linarith), ← Set.Ioc_union_Ioi_eq_Ioi hc1,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi (hi.mono_set Set.Ioc_subset_Ioi_self)
      (hi.mono_set (Set.Ioi_subset_Ioi hc1))]
  have h1 := integral_P_le ρ hcpos hc1
  have h2 := tail_le ρ hcpos hc1
  have h3 := small_alg ρ hc0 hc1
  linarith

end RegretKappa.Upper
