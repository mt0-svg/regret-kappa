import RegretKappa.Upper.Defs

/-!
# Upper bound: the potential `G`

Integrability of the mixtures, and the elementary properties of `G`: nonnegative, even,
nondecreasing in `|r|` (the paper, Lemma A.1), an upper bound at `r = 2` and a lower
bound for `r ≥ 1` (the two inputs of the terminal condition and of the large steps).
-/

namespace RegretKappa.Upper

open Real MeasureTheory Set

theorem wt_pos {θ : ℝ} (hθ : 0 < θ) : 0 < wt θ := by
  unfold wt
  positivity

theorem wt_le {θ : ℝ} (hθ : 1 ≤ θ) : wt θ ≤ 3 * exp (-θ ^ 2 / 2) := by
  have hθpos : 0 < θ := by linarith
  have hθ3pos : 0 < θ ^ 3 := pow_pos hθpos 3
  have hθ3ge1 : 1 ≤ θ ^ 3 := by
    have hsq : 1 ≤ θ ^ 2 := by
      nlinarith
    nlinarith
  have h1 : 1 / θ ≤ 1 := (div_le_one hθpos).mpr hθ
  have h2 : 2 / θ ^ 3 ≤ 2 := by
    have h : 1 / θ ^ 3 ≤ 1 := (div_le_one hθ3pos).mpr hθ3ge1
    calc
      2 / θ ^ 3 = 2 * (1 / θ ^ 3) := by ring
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 2 := by norm_num
  have hsum : 1 / θ + 2 / θ ^ 3 ≤ 3 := by linarith
  have hexp_pos : 0 < exp (-θ ^ 2 / 2) := Real.exp_pos _
  calc
    wt θ = exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := rfl
    _ ≤ exp (-θ ^ 2 / 2) * 3 := mul_le_mul_of_nonneg_left hsum hexp_pos.le
    _ = 3 * exp (-θ ^ 2 / 2) := by ring

/-- A function continuous on `Ioi a` and dominated there by a Gaussian is integrable on `Ioi a`. -/
theorem integrableOn_Ioi_of_le_gauss {f : ℝ → ℝ} {a k M : ℝ} (hk : 0 < k)
    (hf : ContinuousOn f (Ioi a)) (hb : ∀ θ ∈ Ioi a, |f θ| ≤ M * exp (-k * θ ^ 2)) :
    IntegrableOn f (Ioi a) := by
  have h_int : IntegrableOn (fun θ => M * exp (-k * θ ^ 2)) (Ioi a) :=
    ((integrable_exp_neg_mul_sq hk).const_mul M).integrableOn
  have h_meas : AEStronglyMeasurable f (volume.restrict (Ioi a)) :=
    hf.aestronglyMeasurable measurableSet_Ioi
  have h_bound : ∀ᵐ θ ∂(volume.restrict (Ioi a)), ‖f θ‖ ≤ M * exp (-k * θ ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun θ hθ => by
      rw [Real.norm_eq_abs]
      exact hb θ hθ)
  exact h_int.mono' h_meas h_bound

theorem cosh_le_exp_abs_u (x : ℝ) : cosh x ≤ Real.exp (|x|) := by
  rcases em (0 ≤ x) with (hx | hx)
  · have hx' : |x| = x := abs_of_nonneg hx
    rw [hx']
    have h : Real.exp x + Real.exp (-x) ≤ 2 * Real.exp x := by
      have : Real.exp (-x) ≤ Real.exp x := by
        apply Real.exp_le_exp.mpr
        linarith
      nlinarith
    rw [Real.cosh_eq]
    nlinarith
  · have hx' : |x| = -x := abs_of_neg (not_le.mp hx)
    rw [hx']
    have h : Real.exp x + Real.exp (-x) ≤ 2 * Real.exp (-x) := by
      have : Real.exp x ≤ Real.exp (-x) := by
        apply Real.exp_le_exp.mpr
        linarith
      nlinarith
    rw [Real.cosh_eq]
    nlinarith


theorem integrableOn_G (r : ℝ) : IntegrableOn (fun θ => cosh (θ * r) * wt θ) (Ioi 1) := by
  refine integrableOn_Ioi_of_le_gauss (M := 3 * Real.exp (r ^ 2)) (by norm_num : 0 < (1/4 : ℝ)) ?_ ?_
  · -- continuity on Ioi 1
    have h_cont_cosh : ContinuousOn (fun (θ : ℝ) => cosh (θ * r)) (Ioi 1) := by
      have : Continuous (fun (θ : ℝ) => cosh (θ * r)) := by
        apply Real.continuous_cosh.comp
        continuity
      exact this.continuousOn
    have h_cont_wt : ContinuousOn wt (Ioi 1) := by
      unfold wt
      refine ContinuousOn.mul ?_ ?_
      · refine (Real.continuous_exp.comp (by continuity : Continuous (fun θ : ℝ => -θ ^ 2 / 2))).continuousOn
      · refine ContinuousOn.add ?_ ?_
        · refine (continuousOn_const.div continuousOn_id ?_)
          intro θ hθ
          have hθpos : 0 < θ := by
            have := (Set.mem_Ioi.mp hθ : 1 < θ)
            linarith
          exact hθpos.ne.symm
        · refine (continuousOn_const.div (continuousOn_id.pow 3) ?_)
          intro θ hθ
          have hθpos : 0 < θ := by
            have := (Set.mem_Ioi.mp hθ : 1 < θ)
            linarith
          exact pow_ne_zero 3 hθpos.ne.symm
    exact ContinuousOn.mul h_cont_cosh h_cont_wt
  · -- bound: |cosh(θ*r) * wt θ| ≤ (3 * exp(r²)) * exp(-(1/4) * θ²) for θ > 1
    intro θ hθ
    have hθ_gt_one : 1 < θ := Set.mem_Ioi.mp hθ
    have hθpos : 0 < θ := by linarith
    have hθ1 : 1 ≤ θ := by linarith
    have h_nonneg : 0 ≤ cosh (θ * r) * wt θ := by
      have h_cosh_pos : 0 < cosh (θ * r) := Real.cosh_pos _
      have h_wt_pos : 0 < wt θ := wt_pos hθpos
      positivity
    rw [abs_of_nonneg h_nonneg]
    have h_bound_cosh : cosh (θ * r) ≤ Real.exp (|θ * r|) := cosh_le_exp_abs_u (θ * r)
    have h_bound_wt : wt θ ≤ 3 * Real.exp (-θ ^ 2 / 2) := wt_le hθ1
    have h_abs_mul : |θ * r| = θ * |r| := by
      rw [abs_mul, abs_of_pos hθpos]
    have h_ineq : θ * |r| - θ ^ 2 / 2 ≤ r ^ 2 - θ ^ 2 / 4 := by
      have h_sq_nonneg : 0 ≤ (θ / 2 - |r|) ^ 2 := by positivity
      have h_expanded : (θ / 2 - |r|) ^ 2 = θ ^ 2 / 4 - θ * |r| + |r| ^ 2 := by ring
      rw [h_expanded] at h_sq_nonneg
      have h_sq_abs : |r| ^ 2 = r ^ 2 := sq_abs r
      rw [h_sq_abs] at h_sq_nonneg
      linarith
    have h_mul_bound : cosh (θ * r) * wt θ ≤ Real.exp (|θ * r|) * (3 * Real.exp (-θ ^ 2 / 2)) := by
      have h_cosh_nonneg : 0 ≤ cosh (θ * r) := by positivity
      have h_wt_nonneg : 0 ≤ wt θ := by
        have h_wt_pos : 0 < wt θ := wt_pos hθpos
        exact h_wt_pos.le
      exact mul_le_mul h_bound_cosh h_bound_wt h_wt_nonneg (by positivity)
    have h_exp_bound : Real.exp (|θ * r|) * (3 * Real.exp (-θ ^ 2 / 2)) = 3 * Real.exp (|θ * r| - θ ^ 2 / 2) := by
      calc
        Real.exp (|θ * r|) * (3 * Real.exp (-θ ^ 2 / 2)) = 3 * (Real.exp (|θ * r|) * Real.exp (-θ ^ 2 / 2)) := by ring
        _ = 3 * Real.exp (|θ * r| + (-θ ^ 2 / 2)) := by rw [Real.exp_add]
        _ = 3 * Real.exp (|θ * r| - θ ^ 2 / 2) := by
          rw [sub_eq_add_neg]
          ring_nf
    have h_exp_ineq : 3 * Real.exp (|θ * r| - θ ^ 2 / 2) ≤ 3 * Real.exp (r ^ 2 - θ ^ 2 / 4) := by
      have h_exp_mono : Real.exp (|θ * r| - θ ^ 2 / 2) ≤ Real.exp (r ^ 2 - θ ^ 2 / 4) :=
        Real.exp_le_exp.mpr (by
          rw [h_abs_mul]
          exact h_ineq)
      nlinarith
    have h_final_eq : 3 * Real.exp (r ^ 2 - θ ^ 2 / 4) = (3 * Real.exp (r ^ 2)) * Real.exp (-(1/4 : ℝ) * θ ^ 2) := by
      have h_exp_split : r ^ 2 - θ ^ 2 / 4 = r ^ 2 + (-(1/4 : ℝ) * θ ^ 2) := by ring
      rw [h_exp_split, Real.exp_add]
      ring
    calc
      cosh (θ * r) * wt θ ≤ Real.exp (|θ * r|) * (3 * Real.exp (-θ ^ 2 / 2)) := h_mul_bound
      _ = 3 * Real.exp (|θ * r| - θ ^ 2 / 2) := h_exp_bound
      _ ≤ 3 * Real.exp (r ^ 2 - θ ^ 2 / 4) := h_exp_ineq
      _ = (3 * Real.exp (r ^ 2)) * Real.exp (-(1/4 : ℝ) * θ ^ 2) := h_final_eq

theorem integrableOn_Ghat (a b : ℝ) (hb : b ^ 2 < 1) :
    IntegrableOn (fun θ => cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ) (Ioi 1) := by
  set κ := (1 - b ^ 2) / 2 with hκ_def
  have hκ_pos : 0 < κ := by
    have hpos : 0 < 1 - b ^ 2 := by linarith
    linarith
  have h_cosh_bound (x : ℝ) : cosh x ≤ exp (|x|) := by
    rcases em (0 ≤ x) with (hx | hx)
    · have habs : |x| = x := abs_of_nonneg hx
      rw [habs]
      rw [Real.cosh_eq]
      have h : exp (-x) ≤ exp x := by
        rw [Real.exp_le_exp]
        linarith
      linarith
    · have habs : |x| = -x := abs_of_neg (not_le.mp hx)
      rw [habs]
      rw [Real.cosh_eq]
      have hpos : 0 ≤ -x := by linarith
      have h : exp x ≤ exp (-x) := by
        rw [Real.exp_le_exp]
        linarith
      linarith
  have h_amgm (θ a κ : ℝ) (hκ : 0 < κ) : θ * |a| ≤ a ^ 2 / (2 * κ) + (κ / 2) * θ ^ 2 := by
    have hsq : (κ * θ - |a|) ^ 2 ≥ 0 := by positivity
    have habssq : |a| ^ 2 = a ^ 2 := sq_abs a
    have h_expand : (κ * θ - |a|) ^ 2 = κ ^ 2 * θ ^ 2 - 2 * κ * θ * |a| + |a| ^ 2 := by ring
    rw [h_expand] at hsq
    have h_ineq : 2 * κ * θ * |a| ≤ κ ^ 2 * θ ^ 2 + |a| ^ 2 := by linarith
    have h2κ_pos : 0 < 2 * κ := by linarith
    calc
      θ * |a| = (2 * κ * θ * |a|) / (2 * κ) := by
        field_simp [h2κ_pos.ne.symm]
      _ ≤ (κ ^ 2 * θ ^ 2 + |a| ^ 2) / (2 * κ) := by
        gcongr
      _ = (κ ^ 2 * θ ^ 2) / (2 * κ) + |a| ^ 2 / (2 * κ) := by ring
      _ = (κ / 2) * θ ^ 2 + |a| ^ 2 / (2 * κ) := by
        field_simp [hκ.ne.symm]
      _ = (κ / 2) * θ ^ 2 + a ^ 2 / (2 * κ) := by rw [habssq]
      _ = a ^ 2 / (2 * κ) + (κ / 2) * θ ^ 2 := by ring
  have h_cont : ContinuousOn (fun θ => cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ) (Ioi 1) := by
    have h_cosh_cont : Continuous fun θ : ℝ => cosh (θ * a) :=
      Real.continuous_cosh.comp (by continuity)
    have h_exp_cont : Continuous fun θ : ℝ => exp (θ ^ 2 * b ^ 2 / 2) :=
      Real.continuous_exp.comp (by continuity)
    have h_wt_cont : ContinuousOn wt (Ioi 1) := by
      unfold wt
      refine ContinuousOn.mul ?_ ?_
      · refine (Real.continuous_exp.comp (by continuity)).continuousOn
      · refine ContinuousOn.add ?_ ?_
        · refine (continuousOn_const.div continuousOn_id ?_)
          intro x hx
          exact ne_of_gt (by
            have : 1 < x := hx
            linarith)
        · refine (continuousOn_const.div (continuousOn_id.pow 3) ?_)
          intro x hx
          exact pow_ne_zero 3 (by
            have : 1 < x := hx
            linarith)
    exact ((h_cosh_cont.continuousOn.mul h_exp_cont.continuousOn).mul h_wt_cont)
  have h_bound : ∀ θ ∈ Ioi 1, |cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ| ≤
      (3 * exp (a ^ 2 / (2 * κ))) * exp (-(κ / 2) * θ ^ 2) := by
    intro θ hθ
    have hθ1 : 1 ≤ θ := le_of_lt (Set.mem_Ioi.1 hθ)
    have hθpos : 0 < θ := by linarith
    have h_nonneg : 0 ≤ cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ := by
      have h_wt_nonneg' : 0 ≤ wt θ := by
        have := wt_pos hθpos
        linarith
      positivity
    rw [abs_of_nonneg h_nonneg]
    have h_wt : wt θ ≤ 3 * exp (-θ ^ 2 / 2) := wt_le hθ1
    have h_cosh : cosh (θ * a) ≤ exp (|θ * a|) := h_cosh_bound (θ * a)
    have h_abs_mul : |θ * a| = θ * |a| := by
      rw [abs_mul, abs_of_pos hθpos]
    rw [h_abs_mul] at h_cosh
    have h_wt_nonneg' : 0 ≤ wt θ := by
      have := wt_pos hθpos
      linarith
    calc
      cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ
          ≤ exp (θ * |a|) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ := by
        gcongr
      _ ≤ exp (θ * |a|) * exp (θ ^ 2 * b ^ 2 / 2) * (3 * exp (-θ ^ 2 / 2)) := by
        gcongr
      _ = 3 * (exp (θ * |a|) * exp (θ ^ 2 * b ^ 2 / 2) * exp (-θ ^ 2 / 2)) := by ring
      _ = 3 * exp (θ * |a| + θ ^ 2 * b ^ 2 / 2 + (-θ ^ 2 / 2)) := by
        simp [Real.exp_add]
      _ = 3 * exp (θ * |a| + (θ ^ 2 * b ^ 2 / 2 - θ ^ 2 / 2)) := by ring_nf
      _ = 3 * exp (θ * |a| - θ ^ 2 * (1 - b ^ 2) / 2) := by ring_nf
      _ = 3 * exp (θ * |a| - θ ^ 2 * κ) := by
        rw [hκ_def]
        ring_nf
      _ ≤ 3 * exp ((a ^ 2 / (2 * κ) + (κ / 2) * θ ^ 2) - θ ^ 2 * κ) := by
        gcongr
        exact h_amgm θ a κ hκ_pos
      _ = 3 * exp (a ^ 2 / (2 * κ) + (κ / 2) * θ ^ 2 - κ * θ ^ 2) := by ring_nf
      _ = 3 * exp (a ^ 2 / (2 * κ) - (κ / 2) * θ ^ 2) := by ring_nf
      _ = 3 * exp ((a ^ 2 / (2 * κ)) + (-((κ / 2) * θ ^ 2))) := by ring_nf
      _ = 3 * (exp (a ^ 2 / (2 * κ)) * exp (-((κ / 2) * θ ^ 2))) := by
        rw [Real.exp_add]
      _ = 3 * exp (a ^ 2 / (2 * κ)) * exp (-(κ / 2) * θ ^ 2) := by ring_nf
      _ = (3 * exp (a ^ 2 / (2 * κ))) * exp (-(κ / 2) * θ ^ 2) := by ring_nf
  have hk_pos : 0 < κ / 2 := by linarith
  exact integrableOn_Ioi_of_le_gauss hk_pos h_cont h_bound

theorem G_nonneg (r : ℝ) : 0 ≤ G r :=
  setIntegral_nonneg measurableSet_Ioi fun _ hθ =>
    mul_nonneg (cosh_pos _).le (wt_pos (lt_trans one_pos hθ)).le

theorem G_neg (r : ℝ) : G (-r) = G r := by
  simp only [G, mul_neg, cosh_neg]

theorem G_abs (r : ℝ) : G |r| = G r := by
  rcases abs_choice r with h | h <;> rw [h]
  exact G_neg r

/-- `G` is nondecreasing in `|r|`. -/
theorem G_mono {r r' : ℝ} (h : |r| ≤ |r'|) : G r ≤ G r' := by
  unfold G
  refine MeasureTheory.setIntegral_mono_on (integrableOn_G r) (integrableOn_G r') measurableSet_Ioi ?_
  intro θ hθ
  have hθpos : 0 < θ := by
    have : 1 < θ := Set.mem_Ioi.mp hθ
    linarith
  have hwt_nonneg : 0 ≤ wt θ := (wt_pos hθpos).le
  have h_cosh : cosh (θ * r) ≤ cosh (θ * r') := by
    rw [Real.cosh_le_cosh]
    calc
      |θ * r| = |θ| * |r| := abs_mul θ r
      _ = θ * |r| := by rw [abs_of_pos hθpos]
      _ ≤ θ * |r'| := mul_le_mul_of_nonneg_left h (by linarith)
      _ = |θ| * |r'| := by rw [abs_of_pos hθpos]
      _ = |θ * r'| := (abs_mul θ r').symm
  nlinarith

/-- `G 2 ≤ 3 e² √(2π) < 60`. -/
theorem G_two_le : G 2 ≤ 60 := by
  unfold G
  -- cosh x ≤ exp x for x ≥ 0
  have h_cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : cosh x ≤ Real.exp x := by
    rw [Real.cosh_eq]
    have h_exp_neg : Real.exp (-x) ≤ Real.exp x := by
      rw [Real.exp_le_exp]
      linarith
    nlinarith
  -- For θ > 1, we have θ ≥ 0, so 2θ ≥ 0
  have h_bound : ∀ θ ∈ Ioi 1, cosh (θ * 2) * wt θ ≤ 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2)) := by
    intro θ hθ
    have hθ_nonneg : 0 ≤ θ := by
      have : 1 < θ := Set.mem_Ioi.mp hθ
      linarith
    have hθ_ge_one : 1 ≤ θ := by
      have : 1 < θ := Set.mem_Ioi.mp hθ
      linarith
    have h_cosh : cosh (θ * 2) ≤ Real.exp (θ * 2) := h_cosh_le_exp (by nlinarith)
    have h_wt : wt θ ≤ 3 * Real.exp (-θ ^ 2 / 2) := wt_le hθ_ge_one
    have h_pos_wt : 0 ≤ wt θ := by linarith [wt_pos (by linarith : 0 < θ)]
    have h_prod : cosh (θ * 2) * wt θ ≤ Real.exp (θ * 2) * (3 * Real.exp (-θ ^ 2 / 2)) := by
      exact mul_le_mul h_cosh h_wt h_pos_wt (by linarith [Real.exp_pos (θ * 2)])
    have h_expand : Real.exp (θ * 2) * Real.exp (-θ ^ 2 / 2) = Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2)) := by
      calc
        Real.exp (θ * 2) * Real.exp (-θ ^ 2 / 2) = Real.exp (θ * 2 + (-θ ^ 2 / 2)) := by rw [Real.exp_add]
        _ = Real.exp (2 * θ - θ ^ 2 / 2) := by ring_nf
        _ = Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2)) := by
          have h : 2 * θ - θ ^ 2 / 2 = 2 + (-((θ - 2) ^ 2 / 2)) := by ring
          rw [h, Real.exp_add]
    calc
      cosh (θ * 2) * wt θ ≤ Real.exp (θ * 2) * (3 * Real.exp (-θ ^ 2 / 2)) := h_prod
      _ = 3 * (Real.exp (θ * 2) * Real.exp (-θ ^ 2 / 2)) := by ring
      _ = 3 * (Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) := by rw [h_expand]
      _ = 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2)) := by ring
  -- Integrability of the bounding function
  have h_int_bound : Integrable (fun θ : ℝ => Real.exp (-((θ - 2) ^ 2 / 2))) volume := by
    have h_pos : 0 < (1/2 : ℝ) := by norm_num
    have h_int' : Integrable (fun θ : ℝ => Real.exp (-(1/2 : ℝ) * θ ^ 2)) volume :=
      integrable_exp_neg_mul_sq h_pos
    have h_eq : (fun θ : ℝ => Real.exp (-((θ - 2) ^ 2 / 2))) =
        (fun θ : ℝ => Real.exp (-(1/2 : ℝ) * θ ^ 2)) ∘ (fun θ : ℝ => θ - 2) := by
      ext θ
      have : (θ - 2) ^ 2 / 2 = (1/2 : ℝ) * (θ - 2) ^ 2 := by ring
      simp [this, mul_comm]
    rw [h_eq]
    exact h_int'.comp_sub_right 2
  have h_int_bound_mul : Integrable (fun θ : ℝ => 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) volume :=
    h_int_bound.const_mul (3 * Real.exp 2)
  -- Integrate over Ioi 1
  have h_int_Ioi : (∫ θ in Ioi 1, cosh (θ * 2) * wt θ) ≤
      (∫ θ in Ioi 1, 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) := by
    refine setIntegral_mono_on (integrableOn_G 2)
      (h_int_bound_mul.integrableOn) measurableSet_Ioi h_bound
  -- Extend to integral over ℝ
  have h_int_R : (∫ θ in Ioi 1, 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) ≤
      (∫ θ, 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) := by
    have h_nonneg : 0 ≤ᵐ[volume] (fun θ : ℝ => 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) := by
      filter_upwards with θ
      positivity
    exact setIntegral_le_integral h_int_bound_mul h_nonneg
  -- Compute the Gaussian integral
  have h_gaussian : (∫ θ, Real.exp (-((θ - 2) ^ 2 / 2))) = Real.sqrt (2 * π) := by
    calc
      (∫ θ, Real.exp (-((θ - 2) ^ 2 / 2))) = (∫ θ, Real.exp (-(1/2 : ℝ) * (θ - 2) ^ 2)) := by
        refine integral_congr_ae ?_
        filter_upwards with θ
        ring_nf
      _ = (∫ θ, Real.exp (-(1/2 : ℝ) * θ ^ 2)) := by
        rw [integral_sub_right_eq_self (fun θ => Real.exp (-(1/2 : ℝ) * θ ^ 2)) 2]
      _ = Real.sqrt (Real.pi / (1/2 : ℝ)) := by rw [integral_gaussian (1/2)]
      _ = Real.sqrt (2 * π) := by ring_nf
  -- Put everything together
  have h_total : (∫ θ, 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) = 3 * Real.exp 2 * Real.sqrt (2 * π) := by
    calc
      (∫ θ, 3 * Real.exp 2 * Real.exp (-((θ - 2) ^ 2 / 2))) = (3 * Real.exp 2) * (∫ θ, Real.exp (-((θ - 2) ^ 2 / 2))) := by
        rw [integral_const_mul_of_integrable h_int_bound]
      _ = (3 * Real.exp 2) * Real.sqrt (2 * π) := by rw [h_gaussian]
      _ = 3 * Real.exp 2 * Real.sqrt (2 * π) := by ring
  rw [h_total] at h_int_R
  -- Now we need: 3 * exp(2) * sqrt(2π) ≤ 60
  have h_num : 3 * Real.exp 2 * Real.sqrt (2 * π) ≤ 60 := by
    have h_exp2 : Real.exp 2 < (2.7182818286 : ℝ) ^ 2 := by
      have h_exp1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h_pos : 0 < Real.exp 1 := Real.exp_pos 1
      have h_eq : Real.exp 2 = (Real.exp 1) ^ 2 := by
        calc
          Real.exp 2 = Real.exp (1 + 1) := by ring_nf
          _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
          _ = (Real.exp 1) ^ 2 := by ring
      rw [h_eq]
      nlinarith
    have h_sqrt : Real.sqrt (2 * π) < 2.51 := by
      have h_pi : π < 3.15 := Real.pi_lt_d2
      have h_lt : 2 * π < 6.3001 := by nlinarith
      have h_nonneg : 0 ≤ 2 * π := by positivity
      calc
        Real.sqrt (2 * π) < Real.sqrt (6.3001) := Real.sqrt_lt_sqrt h_nonneg h_lt
        _ = 2.51 := by norm_num
    have h_pos_exp : 0 < Real.exp 2 := Real.exp_pos 2
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (2 * π) := Real.sqrt_nonneg _
    have h_bound1 : 3 * Real.exp 2 * Real.sqrt (2 * π) < 3 * ((2.7182818286 : ℝ) ^ 2) * 2.51 := by
      nlinarith
    have h_bound2 : 3 * ((2.7182818286 : ℝ) ^ 2) * 2.51 ≤ 60 := by norm_num
    linarith
  nlinarith

/-- For `r ≥ 1`, `G r ≥ e^{r²/2 - 1/2} / (2 (r + 1))` (the window `θ ∈ (r, r + 1]`). -/
theorem G_lower {r : ℝ} (hr : 1 ≤ r) : exp (r ^ 2 / 2 - 1 / 2) / (2 * (r + 1)) ≤ G r := by
  set m := exp (r ^ 2 / 2 - 1 / 2) / (2 * (r + 1)) with hm
  have hr_pos : 0 < r := by linarith
  have hr1_pos : 0 < r + 1 := by linarith
  have h_vol_fin : volume (Ioc r (r + 1)) ≠ ⊤ := by
    simp
  -- The integrand is nonnegative on Ioi 1
  have h_nonneg : ∀ θ, θ ∈ Ioi 1 → 0 ≤ cosh (θ * r) * wt θ := by
    intro θ hθ
    have hθ_pos : 0 < θ := by
      have : 1 < θ := hθ
      linarith
    have h_cosh_nonneg : 0 ≤ cosh (θ * r) := by
      rw [Real.cosh_eq]
      positivity
    have h_wt_nonneg : 0 ≤ wt θ := by
      have h := wt_pos hθ_pos
      linarith
    nlinarith
  have h_nonneg_ae : 0 ≤ᵐ[volume.restrict (Ioi 1)] (fun θ => cosh (θ * r) * wt θ) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi h_nonneg
  -- Ioc r (r+1) ⊆ Ioi 1 as an AE inclusion
  have h_subset : Ioc r (r + 1) ≤ᵐ[volume] Ioi 1 := by
    have h : Ioc r (r + 1) ⊆ Ioi 1 := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      refine Set.mem_Ioi.mpr ?_
      linarith
    exact h.eventuallyLE
  -- Restrict the integral to Ioc r (r+1)
  have h_int_G : IntegrableOn (fun θ => cosh (θ * r) * wt θ) (Ioi 1) := integrableOn_G r
  have h_int_restrict : ∫ θ in Ioc r (r + 1), cosh (θ * r) * wt θ ≤ G r := by
    calc
      ∫ θ in Ioc r (r + 1), cosh (θ * r) * wt θ ≤ ∫ θ in Ioi 1, cosh (θ * r) * wt θ :=
        setIntegral_mono_set h_int_G h_nonneg_ae h_subset
      _ = G r := rfl
  -- On Ioc r (r+1), the integrand is ≥ m
  have h_bound : ∀ θ, θ ∈ Ioc r (r + 1) → m ≤ cosh (θ * r) * wt θ := by
    intro θ hθ
    rcases hθ with ⟨hθ_gt, hθ_le⟩
    have hθ_pos : 0 < θ := by linarith
    have h_diff_pos : 0 < θ - r := by linarith
    have h_diff_le_one : θ - r ≤ 1 := by linarith
    -- cosh(θ*r) ≥ exp(θ*r)/2
    have h_cosh_ge : exp (θ * r) / 2 ≤ cosh (θ * r) := by
      rw [Real.cosh_eq]
      have h_exp_pos : 0 < exp (-(θ * r)) := Real.exp_pos _
      nlinarith
    -- wt(θ) ≥ exp(-θ²/2) / (r+1)
    have h_wt_ge : exp (-(θ ^ 2) / 2) / (r + 1) ≤ wt θ := by
      unfold wt
      have h_denom : 1 / θ + 2 / θ ^ 3 ≥ 1 / θ := by
        have h_nonneg_extra : 0 ≤ 2 / θ ^ 3 := by positivity
        nlinarith
      have h_inv_le : 1 / (r + 1) ≤ 1 / θ := by
        refine (one_div_le_one_div hr1_pos hθ_pos).mpr ?_
        linarith
      calc
        exp (-(θ ^ 2) / 2) / (r + 1) = exp (-(θ ^ 2) / 2) * (1 / (r + 1)) := by ring
        _ ≤ exp (-(θ ^ 2) / 2) * (1 / θ) := by
          have h_exp_nonneg : 0 ≤ exp (-(θ ^ 2) / 2) := by positivity
          nlinarith
        _ ≤ exp (-(θ ^ 2) / 2) * (1 / θ + 2 / θ ^ 3) := by
          have h_exp_nonneg : 0 ≤ exp (-(θ ^ 2) / 2) := by positivity
          nlinarith
        _ = wt θ := rfl
    -- Combine: integrand ≥ exp(θ*r - θ²/2) / (2*(r+1))
    have h_integrand_ge : exp (θ * r - θ ^ 2 / 2) / (2 * (r + 1)) ≤ cosh (θ * r) * wt θ := by
      have h_exp_eq : exp (θ * r - θ ^ 2 / 2) = exp (θ * r) * exp (-(θ ^ 2) / 2) := by
        calc
          exp (θ * r - θ ^ 2 / 2) = exp (θ * r + (-(θ ^ 2 / 2))) := by ring_nf
          _ = exp (θ * r + (-(θ ^ 2) / 2)) := by ring_nf
          _ = exp (θ * r) * exp (-(θ ^ 2) / 2) := by rw [Real.exp_add]
      have h_mul : (exp (θ * r) / 2) * (exp (-(θ ^ 2) / 2) / (r + 1)) ≤ cosh (θ * r) * wt θ := by
        have h_nonneg_left : 0 ≤ exp (θ * r) / 2 := by positivity
        have h_nonneg_right : 0 ≤ exp (-(θ ^ 2) / 2) / (r + 1) := by positivity
        have h_nonneg_cosh : 0 ≤ cosh (θ * r) := by
          rw [Real.cosh_eq]
          positivity
        have h_nonneg_wt : 0 ≤ wt θ := by
          have h := wt_pos hθ_pos
          linarith
        exact mul_le_mul h_cosh_ge h_wt_ge h_nonneg_right h_nonneg_cosh
      calc
        exp (θ * r - θ ^ 2 / 2) / (2 * (r + 1)) = (exp (θ * r) * exp (-(θ ^ 2) / 2)) / (2 * (r + 1)) := by
          rw [h_exp_eq]
        _ = (exp (θ * r) / 2) * (exp (-(θ ^ 2) / 2) / (r + 1)) := by
          field_simp
        _ ≤ cosh (θ * r) * wt θ := h_mul
    -- Now: θ*r - θ²/2 = r²/2 - (θ-r)²/2 ≥ r²/2 - 1/2
    have h_exp_arg_ge : r ^ 2 / 2 - 1 / 2 ≤ θ * r - θ ^ 2 / 2 := by
      have h_eq : θ * r - θ ^ 2 / 2 = r ^ 2 / 2 - (θ - r) ^ 2 / 2 := by
        ring
      rw [h_eq]
      have h_sq_bound : (θ - r) ^ 2 ≤ 1 := by
        nlinarith
      nlinarith
    have h_exp_ge : exp (r ^ 2 / 2 - 1 / 2) ≤ exp (θ * r - θ ^ 2 / 2) :=
      Real.exp_le_exp.mpr h_exp_arg_ge
    -- Put it all together
    calc
      m = exp (r ^ 2 / 2 - 1 / 2) / (2 * (r + 1)) := rfl
      _ ≤ exp (θ * r - θ ^ 2 / 2) / (2 * (r + 1)) :=
        div_le_div_of_nonneg_right h_exp_ge (by positivity)
      _ ≤ cosh (θ * r) * wt θ := h_integrand_ge
  -- Compute ∫_Ioc m = m
  have h_int_m : ∫ θ in Ioc r (r + 1), m = m := by
    calc
      ∫ θ in Ioc r (r + 1), m = (volume.real (Ioc r (r + 1))) • m := setIntegral_const m
      _ = ((r + 1) - r) • m := by
        have h_vol : volume (Ioc r (r + 1)) = ENNReal.ofReal ((r + 1) - r) := by
          simp
        -- volume.real s = (volume s).toReal
        rw [show volume.real (Ioc r (r + 1)) = (volume (Ioc r (r + 1))).toReal from rfl]
        rw [h_vol]
        simp
      _ = 1 • m := by ring
      _ = m := by simp
  -- Now use setIntegral_mono_on to bound the integral
  have h_int_on_const : IntegrableOn (fun _ : ℝ => m) (Ioc r (r + 1)) := by
    refine integrableOn_const (hC := ?_) (hs := h_vol_fin)
    simp
  have h_int_on_G : IntegrableOn (fun θ => cosh (θ * r) * wt θ) (Ioc r (r + 1)) :=
    h_int_G.mono_set (by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      refine Set.mem_Ioi.mpr ?_
      linarith)
  have h_int_bound : ∫ θ in Ioc r (r + 1), m ≤ ∫ θ in Ioc r (r + 1), cosh (θ * r) * wt θ :=
    setIntegral_mono_on h_int_on_const h_int_on_G measurableSet_Ioc h_bound
  -- Combine everything
  calc
    m = ∫ θ in Ioc r (r + 1), m := by rw [h_int_m]
    _ ≤ ∫ θ in Ioc r (r + 1), cosh (θ * r) * wt θ := h_int_bound
    _ ≤ G r := h_int_restrict

end RegretKappa.Upper
