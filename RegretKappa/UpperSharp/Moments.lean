import RegretKappa.UpperSharp.Consts

/-!
# The upper bound with the paper's constants: Gaussian moments on `(1, ∞)`

* `K0 = ∫_1^∞ e^{-θ²/2}/θ dθ` (`= E₁(1/2)/2`, the paper's `K₀`) and its enclosure
  `0.2798867 ≤ K0 ≤ 0.2798869` (`K0_ge`, `K0_le`): `R = √32`, the alternating Taylor polynomials of
  `e^{-v}` with 54 and 53 terms on `[1, R]` (`expNegT_alt`, `integral_expNegT_div`) and the tail
  `∫_R^∞ ≤ e^{-R²/2}/R² = e^{-16}/32` (`K0_tail_le`);
* `J0 = ∫_1^∞ e^{-θ²/2}/θ³ dθ` with `2 J0 + K0 = e^{-1/2}` (`J0_add`);
* the moments `mom j = ∫_1^∞ θ^j e^{-θ²/2} dθ`: `mom 1 = e^{-1/2}`,
  `mom (j + 2) = e^{-1/2} + (j + 1) mom j`.
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set Finset Filter Topology

noncomputable def expNegT (n : ℕ) (v : ℝ) : ℝ := ∑ k ∈ range n, (-v) ^ k / (k.factorial : ℝ)

noncomputable def K0 : ℝ := ∫ θ in Ioi (1 : ℝ), exp (-θ ^ 2 / 2) / θ

theorem hasDerivAt_expNegT_succ (m : ℕ) (v : ℝ) : HasDerivAt (expNegT (m + 1)) (-expNegT m v) v := by
  let A : ℕ → ℝ → ℝ := fun k v => (-v) ^ k / (k.factorial : ℝ)
  have hA_deriv : ∀ k ∈ range (m + 1), HasDerivAt (A k)
      (if k = 0 then (0 : ℝ) else -((-v) ^ (k - 1) / ((k - 1).factorial : ℝ))) v := by
    intro k hk
    rw [Finset.mem_range] at hk
    dsimp [A]
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hasDerivAt_const v (1 : ℝ)
    · rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨j, rfl⟩
      have h_neg : HasDerivAt (fun (x : ℝ) => -x) (-1) v := by
        simpa using hasDerivAt_neg' v
      have h_pow : HasDerivAt (fun (x : ℝ) => (-x) ^ (j + 1))
          (↑(j + 1) * (-v) ^ ((j + 1) - 1) * (-1)) v :=
        HasDerivAt.fun_pow h_neg (j + 1)
      have h_div : HasDerivAt (fun (x : ℝ) => (-x) ^ (j + 1) / ((j + 1).factorial : ℝ))
          ((↑(j + 1) * (-v) ^ ((j + 1) - 1) * (-1)) / ((j + 1).factorial : ℝ)) v :=
        HasDerivAt.div_const h_pow ((j + 1).factorial : ℝ)
      have h_simp : (↑(j + 1) * (-v) ^ ((j + 1) - 1) * (-1)) / ((j + 1).factorial : ℝ) =
          -((-v) ^ j / (j.factorial : ℝ)) := by
        have h_fact : ((j + 1).factorial : ℝ) = (j + 1 : ℝ) * (j.factorial : ℝ) := by
          simp [Nat.factorial_succ]
        rw [h_fact]
        have h_sub : (j + 1 : ℕ) - 1 = j := by omega
        simp [h_sub]
        field_simp [Nat.factorial_ne_zero j]
      rw [h_simp] at h_div
      exact h_div
  have h_sum_deriv : (∑ k ∈ range (m + 1), (if k = 0 then (0 : ℝ) else -((-v) ^ (k - 1) / ((k - 1).factorial : ℝ)))) =
      -expNegT m v := by
    rw [Finset.sum_range_succ']
    simp [expNegT]
  have h_sum : HasDerivAt (∑ k ∈ range (m + 1), A k) (∑ k ∈ range (m + 1),
      (if k = 0 then (0 : ℝ) else -((-v) ^ (k - 1) / ((k - 1).factorial : ℝ)))) v :=
    HasDerivAt.sum hA_deriv
  have h_fun_eq : (∑ k ∈ range (m + 1), A k) = expNegT (m + 1) := by
    ext v; simp [A, expNegT]
  simpa [h_fun_eq, h_sum_deriv] using h_sum

-- helper lemma: sum_{x=0}^m 0^x / x! = 1
theorem sum_zero_pow_div_factorial (m : ℕ) : (∑ x ∈ range (m + 1), (0 : ℝ) ^ x / (x.factorial : ℝ)) = 1 := by
  induction' m with m ih
  · simp
  · rw [Finset.sum_range_succ, ih]
    have hm : m + 1 ≠ 0 := Nat.succ_ne_zero m
    simp [zero_pow hm]

theorem expNegT_alt (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ (-1) ^ m * (exp (-v) - expNegT m v) := by
  induction' m with m ih generalizing v
  · -- base case m = 0
    simp [expNegT]
    exact Real.exp_nonneg (-v)
  · -- inductive step: m → m+1
    set g := fun (t : ℝ) => exp (-t) - expNegT (m + 1) t with hg
    have hg0 : g 0 = 0 := by
      dsimp [g, expNegT]
      simp [sum_zero_pow_div_factorial]
    have h_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) v, HasDerivAt g (-(exp (-t) - expNegT m t)) t := by
      intro t ht
      have h_exp : HasDerivAt (fun (x : ℝ) => exp (-x)) (-exp (-t)) t := by
        have h_chain : HasDerivAt (fun (x : ℝ) => -x) (-1) t := by
          simpa using hasDerivAt_neg' t
        have h := HasDerivAt.comp t (Real.hasDerivAt_exp (-t)) h_chain
        simpa [mul_comm, Function.comp_def] using h
      have h_expNegT : HasDerivAt (expNegT (m + 1)) (-expNegT m t) t :=
        hasDerivAt_expNegT_succ m t
      have h := HasDerivAt.sub h_exp h_expNegT
      have h' : (-exp (-t)) - (-expNegT m t) = -(exp (-t) - expNegT m t) := by ring
      have hg_eq : ((fun (x : ℝ) => exp (-x)) - expNegT (m + 1)) = g := by
        ext x; simp [g]
      rw [hg_eq, h'] at h
      exact h
    have h_cont : Continuous (fun (t : ℝ) => -(exp (-t) - expNegT m t)) := by
      dsimp [expNegT]
      continuity
    have h_int : IntervalIntegrable (fun (t : ℝ) => -(exp (-t) - expNegT m t)) MeasureTheory.volume 0 v :=
      h_cont.intervalIntegrable 0 v
    have h_eq : ∫ t in (0 : ℝ)..v, (-(exp (-t) - expNegT m t)) ∂ MeasureTheory.volume = g v - g 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
    rw [hg0, sub_zero] at h_eq
    -- h_eq : ∫_0^v -(exp(-t) - expNegT m t) dt = g v
    -- (-1)^(m+1) * g v = (-1)^(m+1) * ∫_0^v -(exp(-t) - expNegT m t) dt
    -- = (-1)^(m+1) * (-∫_0^v (exp(-t) - expNegT m t) dt)
    -- = -(-1)^(m+1) * ∫_0^v (exp(-t) - expNegT m t) dt
    -- = (-1)^m * ∫_0^v (exp(-t) - expNegT m t) dt
    -- = ∫_0^v (-1)^m * (exp(-t) - expNegT m t) dt ≥ 0
    have h_nonneg : 0 ≤ (-1 : ℝ) ^ (m + 1) * g v := by
      rw [← h_eq]
      rw [intervalIntegral.integral_neg]
      rw [mul_neg]
      -- goal: 0 ≤ -((-1)^(m+1) * ∫_0^v (exp(-t) - expNegT m t) dt)
      have h_pow : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by ring
      rw [h_pow]
      -- goal: 0 ≤ -((-((-1)^m)) * ∫_0^v (exp(-t) - expNegT m t) dt)
      simp
      -- goal: 0 ≤ (-1)^m * ∫_0^v (exp(-t) - expNegT m t) dt
      rw [← intervalIntegral.integral_const_mul]
      -- goal: 0 ≤ ∫_0^v (-1)^m * (exp(-t) - expNegT m t) dt
      apply intervalIntegral.integral_nonneg hv
      intro t ht
      rcases ht with ⟨ht0, ht1⟩
      -- ih : ∀ {v : ℝ}, 0 ≤ v → 0 ≤ (-1)^m * (exp(-v) - expNegT m v)
      exact ih ht0
    simpa [g] using h_nonneg

theorem expNegT_div_expand (n : ℕ) (θ : ℝ) (hθ : θ ≠ 0) :
    expNegT (n + 1) (θ ^ 2 / 2) / θ =
    1 / θ + ∑ k ∈ range n, (-1) ^ (k + 1) * θ ^ (2 * k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) := by
  rw [expNegT, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [add_div]
  simp only [div_eq_mul_inv]
  have hsum : (∑ x ∈ range n, (-(θ ^ 2 * 2⁻¹)) ^ (x + 1) * (↑(x + 1).factorial)⁻¹) * θ⁻¹ =
      ∑ x ∈ range n, (-1) ^ (x + 1) * θ ^ (2 * x + 1) / (2 ^ (x + 1) * ((x + 1).factorial : ℝ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (λ x hx => ?_)
    field_simp [hθ]
    calc
      (-(θ ^ 2 / 2)) ^ (x + 1) * 2 ^ (x + 1) = ((-1) * (θ ^ 2 / 2)) ^ (x + 1) * 2 ^ (x + 1) := by ring
      _ = (-1) ^ (x + 1) * (θ ^ 2 / 2) ^ (x + 1) * 2 ^ (x + 1) := by rw [mul_pow]
      _ = (-1) ^ (x + 1) * ((θ ^ 2) ^ (x + 1) / 2 ^ (x + 1)) * 2 ^ (x + 1) := by rw [div_pow]
      _ = (-1) ^ (x + 1) * (θ ^ 2) ^ (x + 1) := by field_simp
      _ = (-1) ^ (x + 1) * θ ^ (2 * (x + 1)) := by rw [pow_mul]
      _ = (-1) ^ (x + 1) * θ ^ (2 * x + 2) := by ring
      _ = θ * (-1) ^ (x + 1) * θ ^ (2 * x + 1) := by ring
  have hgoal : (∑ x ∈ range n, (-(θ ^ 2 * 2⁻¹)) ^ (x + 1) * (↑(x + 1).factorial)⁻¹) * θ⁻¹ + 1 * θ⁻¹ =
      1 * θ⁻¹ + ∑ x ∈ range n, (-1) ^ (x + 1) * θ ^ (2 * x + 1) / (2 ^ (x + 1) * ((x + 1).factorial : ℝ)) := by
    rw [hsum]
    ring
  exact hgoal

theorem integral_expNegT_div (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ∫ θ in (1 : ℝ)..R, expNegT (n + 1) (θ ^ 2 / 2) / θ =
      log R + ∑ k ∈ range n, (-1) ^ (k + 1) * (R ^ (2 * (k + 1)) - 1) /
        (2 ^ (k + 1) * ((k + 1).factorial : ℝ) * (2 * (k + 1))) := by
  have hRpos : 0 < R := by linarith
  have h0_notin : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) R := by
    intro h
    rcases Set.mem_uIcc.mp h with (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · linarith
    · linarith
  have hpos {θ : ℝ} (hθ : θ ∈ Set.uIcc (1 : ℝ) R) : θ ≠ 0 := by
    rcases Set.mem_uIcc.mp hθ with (⟨hθ1, hθ2⟩ | ⟨hθ1, hθ2⟩)
    · linarith
    · linarith
  have h_eq_on : Set.EqOn (λ θ => expNegT (n + 1) (θ ^ 2 / 2) / θ)
      (λ θ => 1 / θ + ∑ k ∈ range n, (-1) ^ (k + 1) * θ ^ (2 * k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ)))
      (Set.uIcc (1 : ℝ) R) := by
    intro θ hθ
    exact expNegT_div_expand n θ (hpos hθ)
  rw [intervalIntegral.integral_congr h_eq_on]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_finsetSum]
    · have h_int_one_div : ∫ θ in (1 : ℝ)..R, 1 / θ = log R := by
        rw [integral_one_div h0_notin]
        simp
      rw [h_int_one_div]
      congr 1
      refine Finset.sum_congr rfl (λ k hk => ?_)
      have h_integrand : (λ x : ℝ => (-1) ^ (k + 1) * x ^ (2 * k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) =
        (λ x : ℝ => ((-1) ^ (k + 1) / (2 ^ (k + 1) * ((k + 1).factorial : ℝ))) * x ^ (2 * k + 1)) := by
        ext x; ring
      rw [h_integrand]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_pow]
      have h_exp : (2 * k + 1 : ℕ) + 1 = 2 * (k + 1) := by omega
      have h_denom : (↑(2 * k + 1 : ℕ) + 1 : ℝ) = 2 * (k + 1 : ℝ) := by
        push_cast
        ring
      rw [h_exp, h_denom, one_pow]
      field_simp
    · intro i hi
      refine ContinuousOn.intervalIntegrable ?_
      refine Continuous.continuousOn ?_
      continuity
  · -- IntervalIntegrable (λ θ => 1/θ) volume 1 R
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro x hx
    rcases Set.mem_uIcc.mp hx with (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
    · linarith
    · linarith
  · -- IntervalIntegrable (λ θ => ∑ k, ...) volume 1 R
    refine ContinuousOn.intervalIntegrable ?_
    refine Continuous.continuousOn ?_
    continuity

theorem integrableOn_K0 : IntegrableOn (fun θ : ℝ => exp (-θ ^ 2 / 2) / θ) (Ioi 1) := by
  have h_int : Integrable (fun θ : ℝ => exp (-θ ^ 2 / 2)) volume := by
    have hb : (0 : ℝ) < 1/2 := by norm_num
    have := integrable_exp_neg_mul_sq hb
    simpa [div_eq_inv_mul, mul_comm] using this
  have h_int_restrict : Integrable (fun θ : ℝ => exp (-θ ^ 2 / 2)) (volume.restrict (Ioi 1)) :=
    h_int.restrict (s := Ioi 1)
  have h_meas : AEStronglyMeasurable (fun θ : ℝ => exp (-θ ^ 2 / 2) / θ) (volume.restrict (Ioi 1)) := by
    refine (Measurable.aestronglyMeasurable ?_).restrict
    measurability
  have h_bound : ∀ᵐ θ ∂(volume.restrict (Ioi 1)), ‖exp (-θ ^ 2 / 2) / θ‖ ≤ exp (-θ ^ 2 / 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (1 : ℝ)))] with θ hθ
    have hθpos : 0 < θ := by
      have : (1 : ℝ) < θ := hθ
      linarith
    have h_exp_nonneg : 0 ≤ exp (-θ ^ 2 / 2) := Real.exp_pos _ |>.le
    have h_div_nonneg : 0 ≤ exp (-θ ^ 2 / 2) / θ := div_nonneg h_exp_nonneg hθpos.le
    rw [Real.norm_of_nonneg h_div_nonneg]
    exact div_le_self h_exp_nonneg hθ.le
  exact h_int_restrict.mono' h_meas h_bound

theorem tendsto_exp_neg_sq_half :
    Tendsto (fun t : ℝ => exp (-t ^ 2 / 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => -t ^ 2 / 2) atTop atBot := by
    have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).atTop_div_const (two_pos (α := ℝ))
    simpa [neg_div] using this
  exact tendsto_exp_atBot.comp h

theorem integral_Ioi_mul_exp_neg_sq_half (x : ℝ) :
    ∫ u in Ioi x, u * exp (-u ^ 2 / 2) = exp (-x ^ 2 / 2) := by
  have hd : ∀ u ∈ Ioi x, HasDerivAt (fun t => -exp (-t ^ 2 / 2)) (u * exp (-u ^ 2 / 2)) u := by
    intro u _
    have := (((hasDerivAt_pow 2 u).neg).div_const 2).exp.neg
    convert this using 1
    norm_num
    ring
  have hint : IntegrableOn (fun u => u * exp (-u ^ 2 / 2)) (Ioi x) := by
    have := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine (this.congr ?_).integrableOn
    exact Eventually.of_forall fun u => by simp only; ring_nf
  have ht : Tendsto (fun t : ℝ => -exp (-t ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_sq_half.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop : Continuous fun t : ℝ => -exp (-t ^ 2 / 2)).continuousWithinAt hd hint ht]
  ring

theorem K0_tail_le {R : ℝ} (hR : 1 ≤ R) :
    ∫ θ in Ioi R, exp (-θ ^ 2 / 2) / θ ≤ exp (-R ^ 2 / 2) / R ^ 2 := by
  have hR0 : 0 < R := one_pos.trans_le hR
  have hint : IntegrableOn (fun u => u * exp (-u ^ 2 / 2)) (Ioi R) := by
    have := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine (this.congr ?_).integrableOn
    exact Eventually.of_forall fun u => by simp only; ring_nf
  calc ∫ θ in Ioi R, exp (-θ ^ 2 / 2) / θ
      ≤ ∫ θ in Ioi R, θ * exp (-θ ^ 2 / 2) / R ^ 2 := by
        refine setIntegral_mono_on (integrableOn_K0.mono_set (Ioi_subset_Ioi hR)) (hint.div_const _)
          measurableSet_Ioi fun θ hθ => ?_
        have hθ : R < θ := hθ
        have hθ0 : 0 < θ := hR0.trans hθ
        rw [div_le_div_iff₀ hθ0 (by positivity)]
        have := exp_pos (-θ ^ 2 / 2)
        nlinarith [mul_lt_mul hθ hθ.le hR0 hθ0.le]
    _ = exp (-R ^ 2 / 2) / R ^ 2 := by
        rw [integral_div, integral_Ioi_mul_exp_neg_sq_half]

theorem K0_split {R : ℝ} (hR : 1 ≤ R) :
    K0 = (∫ θ in (1 : ℝ)..R, exp (-θ ^ 2 / 2) / θ) + ∫ θ in Ioi R, exp (-θ ^ 2 / 2) / θ := by
  dsimp [K0]
  rw [← Set.Ioc_union_Ioi_eq_Ioi hR]
  rw [MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := 1) (b := R))
    measurableSet_Ioi (integrableOn_K0.mono_set Set.Ioc_subset_Ioi_self)
    (integrableOn_K0.mono_set (Set.Ioi_subset_Ioi hR))]
  rw [← intervalIntegral.integral_of_le hR]

theorem continuousOn_expNegT_div (n : ℕ) {R : ℝ} :
    ContinuousOn (fun θ : ℝ => expNegT n (θ ^ 2 / 2) / θ) (Icc 1 R) := by
  refine ContinuousOn.div ?_ continuousOn_id fun θ hθ => (lt_of_lt_of_le one_pos hθ.1).ne'
  unfold expNegT
  fun_prop

theorem continuousOn_K0_integrand {R : ℝ} :
    ContinuousOn (fun θ : ℝ => exp (-θ ^ 2 / 2) / θ) (Icc 1 R) :=
  ContinuousOn.div (by fun_prop) continuousOn_id fun θ hθ => (lt_of_lt_of_le one_pos hθ.1).ne'

theorem tail_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ ∫ θ in Ioi R, exp (-θ ^ 2 / 2) / θ :=
  setIntegral_nonneg measurableSet_Ioi fun _ hθ =>
    div_nonneg (exp_pos _).le (hR.trans (le_of_lt hθ))

/-- Lower bound on the integral over `[1, R]` from the Taylor polynomial with `m = n + 1` terms,
`m` even. -/
theorem int_ge_of_even {n : ℕ} (he : Even (n + 1)) {R : ℝ} (hR : 1 ≤ R) :
    ∫ θ in (1 : ℝ)..R, expNegT (n + 1) (θ ^ 2 / 2) / θ ≤
      ∫ θ in (1 : ℝ)..R, exp (-θ ^ 2 / 2) / θ := by
  refine intervalIntegral.integral_mono_on hR
    ((continuousOn_expNegT_div _).intervalIntegrable_of_Icc hR)
    (continuousOn_K0_integrand.intervalIntegrable_of_Icc hR) fun θ hθ => ?_
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  have h := expNegT_alt (n + 1) (v := θ ^ 2 / 2) (by positivity)
  rw [he.neg_one_pow, one_mul, ← neg_div] at h
  exact div_le_div_of_nonneg_right (by linarith) hθ0.le

/-- Upper bound on the integral over `[1, R]` from the Taylor polynomial with `m = n + 1` terms,
`m` odd. -/
theorem int_le_of_odd {n : ℕ} (ho : Odd (n + 1)) {R : ℝ} (hR : 1 ≤ R) :
    ∫ θ in (1 : ℝ)..R, exp (-θ ^ 2 / 2) / θ ≤
      ∫ θ in (1 : ℝ)..R, expNegT (n + 1) (θ ^ 2 / 2) / θ := by
  refine intervalIntegral.integral_mono_on hR
    (continuousOn_K0_integrand.intervalIntegrable_of_Icc hR)
    ((continuousOn_expNegT_div _).intervalIntegrable_of_Icc hR) fun θ hθ => ?_
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  have h := expNegT_alt (n + 1) (v := θ ^ 2 / 2) (by positivity)
  rw [ho.neg_one_pow, ← neg_div] at h
  exact div_le_div_of_nonneg_right (by linarith) hθ0.le

theorem sqrt32_sq : √(32 : ℝ) ^ 2 = 32 := Real.sq_sqrt (by norm_num)

theorem one_le_sqrt32 : (1 : ℝ) ≤ √32 := by
  rw [Real.one_le_sqrt]; norm_num

theorem log_sqrt32 : log √(32 : ℝ) = 5 / 2 * log 2 := by
  rw [Real.log_sqrt (by norm_num), show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
  push_cast; ring

theorem pow_sqrt32 (k : ℕ) : √(32 : ℝ) ^ (2 * k) = 32 ^ k := by
  rw [pow_mul, sqrt32_sq]

theorem exp_neg16_le : exp (-16 : ℝ) ≤ 1 / 7217730 := by
  have h := Real.sum_le_exp_of_nonneg (x := (16 : ℝ)) (by norm_num) 20
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem K0_ge : (0.2798867 : ℝ) ≤ K0 := by
  have hR := one_le_sqrt32
  rw [K0_split hR]
  have h1 := int_ge_of_even (n := 53) (by decide) hR
  rw [integral_expNegT_div 53 hR, log_sqrt32] at h1
  have h2 := tail_nonneg √32 (by positivity)
  have hl := Real.log_two_gt_d9
  simp only [pow_sqrt32, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

theorem K0_le : K0 ≤ 0.2798869 := by
  have hR := one_le_sqrt32
  rw [K0_split hR]
  have h1 := int_le_of_odd (n := 52) (by decide) hR
  rw [integral_expNegT_div 52 hR, log_sqrt32] at h1
  have h2 := K0_tail_le hR
  rw [sqrt32_sq] at h2
  have h3 := exp_neg16_le
  have h4 : exp (-32 / 2 : ℝ) / 32 ≤ 1 / 7217730 / 32 := by
    rw [show (-32 / 2 : ℝ) = -16 by norm_num]
    exact div_le_div_of_nonneg_right h3 (by norm_num)
  have hl := Real.log_two_lt_d9
  simp only [pow_sqrt32, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

/-- `J₀ = ∫_1^∞ e^{-θ²/2}/θ³ dθ`. -/
noncomputable def J0 : ℝ := ∫ θ in Ioi (1 : ℝ), exp (-θ ^ 2 / 2) / θ ^ 3

/-- The moments `∫_1^∞ θ^j e^{-θ²/2} dθ`. -/
noncomputable def mom (j : ℕ) : ℝ := ∫ θ in Ioi (1 : ℝ), θ ^ j * exp (-θ ^ 2 / 2)

theorem mom_one : mom 1 = exp (-1 / 2) := by
  dsimp [mom]
  have hpow : (fun (θ : ℝ) => θ ^ 1 * exp (-θ ^ 2 / 2)) = (fun (θ : ℝ) => θ * exp (-θ ^ 2 / 2)) := by
    ext θ; simp [pow_one]
  rw [hpow]
  set F := fun (θ : ℝ) => -exp (-θ ^ 2 / 2) with hF
  set F' := fun (θ : ℝ) => θ * exp (-θ ^ 2 / 2) with hF'
  have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivAt F (F' x) x := by
    intro x hx
    dsimp [F, F']
    have h_inner : HasDerivAt (fun (θ : ℝ) => -θ ^ 2 / 2) (-x) x := by
      have hsq : HasDerivAt (fun (θ : ℝ) => θ ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hneg_sq : HasDerivAt (fun (θ : ℝ) => -(θ ^ 2)) (-(2 * x)) x :=
        HasDerivAt.neg hsq
      have hdiv : HasDerivAt (fun (θ : ℝ) => -(θ ^ 2) / 2) (-(2 * x) / 2) x :=
        HasDerivAt.div_const hneg_sq 2
      have hsimp : -(2 * x) / 2 = -x := by ring
      simpa [hsimp] using hdiv
    have h_exp_comp : HasDerivAt (fun (θ : ℝ) => exp (-θ ^ 2 / 2)) (exp (-x ^ 2 / 2) * (-x)) x :=
      (Real.hasDerivAt_exp (-x ^ 2 / 2)).comp (h := fun (θ : ℝ) => -θ ^ 2 / 2) x h_inner
    have h_neg : HasDerivAt (fun (θ : ℝ) => -exp (-θ ^ 2 / 2)) (-(exp (-x ^ 2 / 2) * (-x))) x :=
      HasDerivAt.neg h_exp_comp
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using h_neg
  have hnonneg : ∀ x ∈ Set.Ioi (1 : ℝ), 0 ≤ F' x := by
    intro x hx
    dsimp [F']
    have hxpos : 0 < x := by
      have : (1 : ℝ) < x := hx
      linarith
    have hexp_pos : 0 < exp (-x ^ 2 / 2) := Real.exp_pos _
    nlinarith
  have hcont : ContinuousWithinAt F (Set.Ici (1 : ℝ)) 1 := by
    dsimp [F]
    refine Continuous.continuousWithinAt ?_
    continuity
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    dsimp [F]
    have h_sq_tendsto : Filter.Tendsto (fun (θ : ℝ) => θ ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have h_neg_sq : Filter.Tendsto (fun (θ : ℝ) => -θ ^ 2) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h_sq_tendsto
    have h_div_two : Filter.Tendsto (fun (θ : ℝ) => -θ ^ 2 / 2) Filter.atTop Filter.atBot :=
      Filter.Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 2) h_neg_sq
    have h_exp : Filter.Tendsto (fun (θ : ℝ) => exp (-θ ^ 2 / 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_div_two
    simpa [F] using h_exp.neg
  have hintegrable : MeasureTheory.IntegrableOn F' (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg hlim
  have h_eq := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hintegrable hlim
  dsimp [F, F'] at h_eq
  rw [h_eq]
  ring_nf


theorem mom_add_two (j : ℕ) : mom (j + 2) = exp (-1 / 2) + (j + 1) * mom j := by
  -- Define F(θ) = -θ^(j+1) * exp(-θ²/2), the antiderivative for integration by parts
  set F := fun (θ : ℝ) => -θ ^ (j + 1) * Real.exp (-θ ^ 2 / 2) with hF
  -- The derivative of F: F'(θ) = θ^(j+2) * exp(-θ²/2) - (j+1) * θ^j * exp(-θ²/2)
  set F' := fun (θ : ℝ) => θ ^ (j + 2) * Real.exp (-θ ^ 2 / 2) - ((j : ℝ) + 1) * θ ^ j * Real.exp (-θ ^ 2 / 2) with hF'
  -- Helper to get integrability of θ^k * exp(-θ²/2) on Ioi 1
  have h_int_term (k : ℕ) : IntegrableOn (fun (θ : ℝ) => θ ^ k * Real.exp (-θ ^ 2 / 2)) (Ioi (1 : ℝ)) volume := by
    have hs : (-1 : ℝ) < (k : ℝ) := by
      have : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have hb : (0 : ℝ) < 1/2 := by norm_num
    -- integrableOn_rpow_mul_exp_neg_mul_sq gives integrability on Ioi 0 of x^(k:ℝ) * exp(-(1/2)*x^2)
    have h_int : IntegrableOn (fun (x : ℝ) => x ^ (k : ℝ) * Real.exp (-((1/2 : ℝ)) * x ^ 2)) (Ioi (0 : ℝ)) volume :=
      integrableOn_rpow_mul_exp_neg_mul_sq hb hs
    have h_restrict : IntegrableOn (fun (x : ℝ) => x ^ (k : ℝ) * Real.exp (-((1/2 : ℝ)) * x ^ 2)) (Ioi (1 : ℝ)) volume :=
      h_int.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    -- Convert x^(k:ℝ) to x^k and adjust the exponential argument
    have h_conv : (fun (x : ℝ) => x ^ (k : ℝ) * Real.exp (-((1/2 : ℝ)) * x ^ 2))
        =ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun (x : ℝ) => x ^ k * Real.exp (-x ^ 2 / 2)) := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))] with x hx
      have hxpos : 0 < x := by
        have : x ∈ Ioi (1 : ℝ) := hx
        linarith [Set.mem_Ioi.mp this]
      have h1 : x ^ (k : ℝ) = x ^ k := Real.rpow_natCast x k
      have h2 : -((1/2 : ℝ)) * x ^ 2 = -x ^ 2 / 2 := by ring
      rw [h1, h2]
    exact h_restrict.congr_fun_ae h_conv
  -- Integrability of F' on Ioi 1
  have hF'int : IntegrableOn F' (Ioi (1 : ℝ)) volume := by
    have h_sub : F' = (fun (θ : ℝ) => θ ^ (j + 2) * Real.exp (-θ ^ 2 / 2)) - (fun (θ : ℝ) => ((j : ℝ) + 1) * (θ ^ j * Real.exp (-θ ^ 2 / 2))) := by
      ext θ; dsimp [F']; ring
    rw [h_sub]
    exact ((h_int_term (j+2)).sub ((h_int_term j).const_mul ((j : ℝ) + 1)))
  -- F is continuous at 1 from the right
  have hFcont : ContinuousWithinAt F (Ici (1 : ℝ)) (1 : ℝ) := by
    dsimp [F]
    refine Continuous.continuousWithinAt ?_
    continuity
  -- F(θ) → 0 as θ → ∞
  have hFtendsto : Filter.Tendsto F Filter.atTop (nhds (0 : ℝ)) := by
    dsimp [F]
    have h_tendsto_pow_exp : Filter.Tendsto (fun (θ : ℝ) => θ ^ (j + 1) * Real.exp (-θ)) Filter.atTop (nhds 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (j + 1)
    -- For θ ≥ 2, θ²/2 ≥ θ, so exp(-θ²/2) ≤ exp(-θ)
    have h_bound : ∀ᶠ (θ : ℝ) in Filter.atTop, θ ^ (j + 1) * Real.exp (-θ ^ 2 / 2) ≤ θ ^ (j + 1) * Real.exp (-θ) := by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with θ hθ
      have h_exp : Real.exp (-θ ^ 2 / 2) ≤ Real.exp (-θ) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      have h_pow : 0 ≤ θ ^ (j + 1) := pow_nonneg (by linarith) (j+1)
      nlinarith
    have h_nonneg : ∀ᶠ (θ : ℝ) in Filter.atTop, (0 : ℝ) ≤ θ ^ (j + 1) * Real.exp (-θ ^ 2 / 2) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with θ hθ
      have h_pow : 0 ≤ θ ^ (j + 1) := pow_nonneg hθ (j+1)
      have h_exp : 0 ≤ Real.exp (-θ ^ 2 / 2) := Real.exp_nonneg _
      nlinarith
    have h_tendsto_gaussian : Filter.Tendsto (fun (θ : ℝ) => θ ^ (j + 1) * Real.exp (-θ ^ 2 / 2)) Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tendsto_pow_exp h_nonneg h_bound
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_tendsto_gaussian.neg
  -- Derivative of F on Ioi 1
  have hFderiv (θ : ℝ) (hθ : θ ∈ Ioi (1 : ℝ)) : HasDerivAt F (F' θ) θ := by
    dsimp [F, F']
    have hpos : 0 < θ := by linarith [Set.mem_Ioi.mp hθ]
    -- derivative of θ^(j+1)
    have hderiv_pow : HasDerivAt (fun x : ℝ => x ^ (j + 1)) ((j + 1 : ℝ) * θ ^ j) θ := by
      simpa using hasDerivAt_pow (j + 1) θ
    -- derivative of exp(-θ²/2)
    have hderiv_exp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (-θ * Real.exp (-θ ^ 2 / 2)) θ := by
      have h_inner : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-θ) θ := by
        have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * θ) θ := by
          simpa using hasDerivAt_pow 2 θ
        have h_neg_sq : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * θ)) θ := by
          have h := h_sq.neg
          have : (-(fun x : ℝ => x ^ 2)) = (fun x : ℝ => -x ^ 2) := by ext x; simp
          rw [this] at h
          exact h
        have h_div : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-(2 * θ) / 2) θ := by
          simpa using h_neg_sq.div_const (2 : ℝ)
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_div
      have h_exp' : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Real.exp (-θ ^ 2 / 2) * (-θ)) θ := by
        simpa [mul_comm] using h_inner.exp
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_exp'
    -- product rule
    have hprod : HasDerivAt (fun x : ℝ => x ^ (j + 1) * Real.exp (-x ^ 2 / 2))
        (((j + 1 : ℝ) * θ ^ j) * Real.exp (-θ ^ 2 / 2) + θ ^ (j + 1) * (-θ * Real.exp (-θ ^ 2 / 2))) θ :=
      hderiv_pow.mul hderiv_exp
    -- multiply by -1 and simplify to F'
    have hneg : HasDerivAt (fun x : ℝ => -(x ^ (j + 1) * Real.exp (-x ^ 2 / 2)))
        (-(((j + 1 : ℝ) * θ ^ j) * Real.exp (-θ ^ 2 / 2) + θ ^ (j + 1) * (-θ * Real.exp (-θ ^ 2 / 2)))) θ := by
      have h := hprod.neg
      have : (-(fun x : ℝ => x ^ (j + 1) * Real.exp (-x ^ 2 / 2))) = (fun x : ℝ => -(x ^ (j + 1) * Real.exp (-x ^ 2 / 2))) := by
        ext x; simp
      rw [this] at h
      exact h
    -- Now simplify the derivative expression
    -- hneg gives: HasDerivAt (fun x => -(x^(j+1)*exp(-x²/2))) (θ^(j+1)*(θ*exp(-θ²/2)) + -((j+1)*θ^j*exp(-θ²/2))) θ
    -- We need: HasDerivAt F (F' θ) θ = HasDerivAt (fun θ => -(θ^(j+1)*exp(-θ²/2))) (θ^(j+2)*exp(-θ²/2) - (j+1)*θ^j*exp(-θ²/2)) θ
    -- These are equal by: θ^(j+1)*θ = θ^(j+2) and ring
    simpa [F', pow_succ, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using hneg
  -- Now apply integration by parts
  have h_int_eq : ∫ θ in Ioi (1 : ℝ), F' θ = (0 : ℝ) - F (1 : ℝ) :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hFcont (fun x hx => hFderiv x hx) hF'int hFtendsto
  -- Simplify both sides
  -- Left side: ∫ F' = mom(j+2) - (j+1) * mom j
  have h_left : ∫ θ in Ioi (1 : ℝ), F' θ = mom (j + 2) - ((j : ℝ) + 1) * mom j := by
    calc
      ∫ θ in Ioi (1 : ℝ), F' θ = ∫ θ in Ioi (1 : ℝ), (θ ^ (j + 2) * Real.exp (-θ ^ 2 / 2) - ((j : ℝ) + 1) * (θ ^ j * Real.exp (-θ ^ 2 / 2))) := by
        refine integral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))] with θ hθ
        dsimp [F']
        ring
      _ = (∫ θ in Ioi (1 : ℝ), θ ^ (j + 2) * Real.exp (-θ ^ 2 / 2)) - (∫ θ in Ioi (1 : ℝ), ((j : ℝ) + 1) * (θ ^ j * Real.exp (-θ ^ 2 / 2))) := by
        rw [integral_sub]
        · exact h_int_term (j+2)
        · exact (h_int_term j).const_mul ((j : ℝ) + 1)
      _ = mom (j + 2) - ((j : ℝ) + 1) * mom j := by
        dsimp [mom]
        congr 1
        rw [integral_const_mul]
  -- Right side: 0 - F(1) = exp(-1/2)
  have h_right : (0 : ℝ) - F (1 : ℝ) = Real.exp (-1 / 2) := by
    dsimp [F]
    simp
  -- Combine
  rw [h_left, h_right] at h_int_eq
  -- Rearrange: mom(j+2) - (j+1)*mom j = exp(-1/2)
  -- So mom(j+2) = exp(-1/2) + (j+1)*mom j
  linarith


theorem J0_add : 2 * J0 + K0 = exp (-1 / 2) := by
  set F : ℝ → ℝ := fun θ => -exp (-θ ^ 2 / 2) / θ ^ 2 with hF_def
  have hF_deriv (θ : ℝ) (hθ : θ ∈ Ioi (1 : ℝ)) : HasDerivAt F (2 * exp (-θ ^ 2 / 2) / θ ^ 3 + exp (-θ ^ 2 / 2) / θ) θ := by
    dsimp [F]
    have hθ_lt : 1 < θ := hθ
    have hθ_pos : θ ≠ 0 := by linarith
    have h_exp : HasDerivAt (fun x : ℝ => exp (-x ^ 2 / 2)) (-θ * exp (-θ ^ 2 / 2)) θ := by
      have h_inner : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-θ) θ := by
        have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * θ) θ := by
          simpa using hasDerivAt_pow 2 θ
        have h_neg_sq : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * θ)) θ := by
          simpa using h_sq.const_mul (-1)
        have h_div : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-(2 * θ) / 2) θ :=
          h_neg_sq.div_const 2
        simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using h_div
      have h_exp_comp := (Real.hasDerivAt_exp (-θ ^ 2 / 2)).comp θ h_inner
      convert h_exp_comp using 1
      · ext x; simp
      · ring
    have h_denom : HasDerivAt (fun x : ℝ => x ^ 2) (2 * θ) θ := by
      simpa using hasDerivAt_pow 2 θ
    have h_denom_ne : θ ^ 2 ≠ 0 := pow_ne_zero 2 hθ_pos
    have h_div := HasDerivAt.div (h_exp.neg) h_denom h_denom_ne
    -- Simplify h_div to the desired form
    have h_simplified : (θ * exp (-θ ^ 2 / 2) * θ ^ 2 + exp (-θ ^ 2 / 2) * (2 * θ)) / (θ ^ 2) ^ 2 =
        2 * exp (-θ ^ 2 / 2) / θ ^ 3 + exp (-θ ^ 2 / 2) / θ := by
      field_simp [hθ_pos]
      ring
    have h_div_simp : HasDerivAt F (2 * exp (-θ ^ 2 / 2) / θ ^ 3 + exp (-θ ^ 2 / 2) / θ) θ := by
      -- h_div : HasDerivAt ((-fun x => rexp (-x ^ 2 / 2)) / fun x => x ^ 2) ... θ
      -- F = fun θ => -rexp (-θ ^ 2 / 2) / θ ^ 2
      have h_func_eq : ((-fun x => exp (-x ^ 2 / 2)) / fun x => x ^ 2) = F := by
        ext x; simp [F]
      -- Also need to simplify the derivative expression
      simpa [F, h_simplified, h_func_eq] using h_div
    exact h_div_simp
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    have h_exp_tendsto : Tendsto (fun θ : ℝ => exp (-θ ^ 2 / 2)) atTop (𝓝 0) := by
      have h_inner : Tendsto (fun θ : ℝ => -θ ^ 2 / 2) atTop atBot := by
        have h_sq : Tendsto (fun θ : ℝ => θ ^ 2) atTop atTop :=
          tendsto_pow_atTop (by norm_num : 2 ≠ 0)
        have h_neg_sq : Tendsto (fun θ : ℝ => -θ ^ 2) atTop atBot :=
          tendsto_neg_atTop_atBot.comp h_sq
        have h := (Filter.tendsto_mul_const_atBot_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)).mpr h_neg_sq
        simpa [div_eq_mul_inv] using h
      exact tendsto_exp_atBot.comp h_inner
    have h_inv_tendsto : Tendsto (fun θ : ℝ => (θ ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    have h_neg_tendsto : Tendsto (fun θ : ℝ => -exp (-θ ^ 2 / 2)) atTop (𝓝 0) := by
      simpa using h_exp_tendsto.neg
    have h_mul : Tendsto (fun θ : ℝ => (-exp (-θ ^ 2 / 2)) * (θ ^ 2)⁻¹) atTop (𝓝 (0 * 0)) :=
      h_neg_tendsto.mul h_inv_tendsto
    have : F = fun θ => (-exp (-θ ^ 2 / 2)) * (θ ^ 2)⁻¹ := by
      ext θ; dsimp [F]; ring
    rw [this]
    simpa [mul_zero] using h_mul
  have h_deriv_nonneg (θ : ℝ) (hθ : θ ∈ Ioi (1 : ℝ)) : 0 ≤ 2 * exp (-θ ^ 2 / 2) / θ ^ 3 + exp (-θ ^ 2 / 2) / θ := by
    have hθ_pos : 0 < θ := by
      have hθ_lt : 1 < θ := hθ
      linarith
    refine add_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _)) (by positivity)) ?_
    exact div_nonneg (Real.exp_nonneg _) (by linarith)
  have h_cont : ContinuousWithinAt F (Ici (1 : ℝ)) (1 : ℝ) := by
    have h_cont_at : ContinuousAt F (1 : ℝ) := by
      dsimp [F]
      refine ContinuousAt.div ?_ ?_ (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
      · refine ContinuousAt.neg ?_
        have h : ContinuousAt (fun x : ℝ => -x ^ 2 / 2) (1 : ℝ) := by
          refine ContinuousAt.div_const ?_ 2
          exact ContinuousAt.neg (continuous_pow 2 |>.continuousAt)
        exact Real.continuous_exp.continuousAt.comp h
      · exact continuous_pow 2 |>.continuousAt
    exact h_cont_at.continuousWithinAt
  have h_int_sum : IntegrableOn (fun θ => 2 * exp (-θ ^ 2 / 2) / θ ^ 3 + exp (-θ ^ 2 / 2) / θ) (Ioi (1 : ℝ)) := by
    refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg h_cont hF_deriv h_deriv_nonneg hF_tendsto
  set f := fun θ : ℝ => 2 * exp (-θ ^ 2 / 2) / θ ^ 3 with hf_def
  set g := fun θ : ℝ => exp (-θ ^ 2 / 2) / θ with hg_def
  have hf_nonneg : 0 ≤ᵐ[Measure.restrict volume (Ioi (1 : ℝ))] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
    have hθ_pos : 0 < θ := by
      have hθ_lt : 1 < θ := hθ
      linarith
    dsimp [f]
    refine div_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _)) ?_
    positivity
  have hg_nonneg : 0 ≤ᵐ[Measure.restrict volume (Ioi (1 : ℝ))] g := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
    have hθ_pos : 0 < θ := by
      have hθ_lt : 1 < θ := hθ
      linarith
    dsimp [g]
    refine div_nonneg (Real.exp_nonneg _) (by linarith)
  have h_meas_f : AEStronglyMeasurable f (Measure.restrict volume (Ioi (1 : ℝ))) := by
    have h_cont_f : ContinuousOn f (Ioi (1 : ℝ)) := by
      dsimp [f]
      have h_cont_exp : ContinuousOn (fun x : ℝ => exp (-x ^ 2 / 2)) (Ioi (1 : ℝ)) :=
        (Real.continuous_exp.comp (by
          refine Continuous.div_const ?_ 2
          refine Continuous.neg ?_
          continuity)).continuousOn
      have h_cont_denom : ContinuousOn (fun x : ℝ => x ^ 3) (Ioi (1 : ℝ)) :=
        (continuous_id.pow 3).continuousOn
      have h_denom_ne_zero : ∀ x ∈ Ioi (1 : ℝ), x ^ 3 ≠ 0 := by
        intro x hx
        have hx_pos : 0 < x := by
          have hx_lt : 1 < x := hx
          linarith
        exact pow_ne_zero 3 (by linarith)
      have h_cont_div : ContinuousOn (fun x : ℝ => exp (-x ^ 2 / 2) / x ^ 3) (Ioi (1 : ℝ)) :=
        h_cont_exp.div h_cont_denom h_denom_ne_zero
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_cont_div.const_mul 2
    exact h_cont_f.aestronglyMeasurable measurableSet_Ioi
  have h_int_f : IntegrableOn f (Ioi (1 : ℝ)) :=
    integrable_left_of_integrable_add_of_nonneg h_meas_f hf_nonneg hg_nonneg h_int_sum
  have h_int_g : IntegrableOn g (Ioi (1 : ℝ)) :=
    integrable_right_of_integrable_add_of_nonneg h_meas_f hf_nonneg hg_nonneg h_int_sum
  calc
    2 * J0 + K0 = 2 * (∫ θ in Ioi (1 : ℝ), exp (-θ ^ 2 / 2) / θ ^ 3) +
        (∫ θ in Ioi (1 : ℝ), exp (-θ ^ 2 / 2) / θ) := rfl
    _ = (∫ θ in Ioi (1 : ℝ), 2 * (exp (-θ ^ 2 / 2) / θ ^ 3)) +
        (∫ θ in Ioi (1 : ℝ), exp (-θ ^ 2 / 2) / θ) := by
      simp [integral_const_mul]
    _ = (∫ θ in Ioi (1 : ℝ), 2 * exp (-θ ^ 2 / 2) / θ ^ 3) +
        (∫ θ in Ioi (1 : ℝ), exp (-θ ^ 2 / 2) / θ) := by
      congr 1
      refine integral_congr_ae ?_
      filter_upwards with θ
      ring
    _ = (∫ θ in Ioi (1 : ℝ), f θ) + (∫ θ in Ioi (1 : ℝ), g θ) := by
      dsimp [f, g]
    _ = ∫ θ in Ioi (1 : ℝ), (f θ + g θ) := by
      rw [integral_add h_int_f h_int_g]
    _ = ∫ θ in Ioi (1 : ℝ), (2 * exp (-θ ^ 2 / 2) / θ ^ 3 + exp (-θ ^ 2 / 2) / θ) := by
      dsimp [f, g]
    _ = exp (-1 / 2) := by
      rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto h_cont hF_deriv h_int_sum hF_tendsto]
      have : F 1 = -exp (-1 / 2) := by
        dsimp [F]
        norm_num
      simp [this]

end RegretKappa.UpperSharp
