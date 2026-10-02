import RegretKappa.UnknownBT.UnknownB.Basic
import RegretKappa.UpperSharp.Assembly

/-!
# Unknown `B`: the facts about the potential

In the units of `RegretKappa.Upper` (`G = Γ/2`, `Γ = Gam`). The facts on the prediction and the
Lipschitz bound used by the running-maximum learner:

* `G1`, `G2`: the first two derivatives of `G` under the integral sign (`hasDerivAt_G`,
  `hasDerivAt_G1`);
* `log (l + G)` is convex for `l ≥ 0` (`convexOn_log_G`): the discriminant of
  `t ↦ ∫ (t² + 2 t θ tanh-free + θ²) …` (`disc_G`), that is Cauchy-Schwarz under the integral;
* the prediction `Upper.eta l a b` is odd in `a` (`eta_neg_left`), nonnegative for `a, b ≥ 0`
  (`eta_nonneg`) and nondecreasing in `a` for `b ≥ 0` (`eta_mono`);
* `G x - G z ≤ 2 Dg(1) (x - z)` on `0 ≤ z ≤ x ≤ 1` (`G_sub_le`), from the convexity of
  `Y ↦ G √Y` of regret-kappa (`UpperSharp.G_sqrt_sub_le`), hence the Lipschitz bound of the
  potential on `[-1, 1]` (`psi_lip`).
-/

namespace RegretKappa.UnknownBT.UB

open Real MeasureTheory Set RegretKappa RegretKappa.UpperSharp

/-- The derivative of `G`: `G1 r = ∫_1^∞ θ sinh(θ r) wt(θ) dθ`. -/
noncomputable def G1 (r : ℝ) : ℝ := ∫ θ in Ioi 1, θ * sinh (θ * r) * Upper.wt θ

/-- The second derivative of `G`: `G2 r = ∫_1^∞ θ² cosh(θ r) wt(θ) dθ`. -/
noncomputable def G2 (r : ℝ) : ℝ := ∫ θ in Ioi 1, θ ^ 2 * cosh (θ * r) * Upper.wt θ

theorem measurable_wt : Measurable Upper.wt := by
  unfold Upper.wt; fun_prop

theorem cosh_le_of_ball {θ r s : ℝ} (hθ : 0 ≤ θ) (hs : s ∈ Metric.ball r 1) :
    cosh (θ * s) ≤ cosh (θ * (|r| + 1)) := by
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hθ,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |r| + 1)]
  refine mul_le_mul_of_nonneg_left ?_ hθ
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have := abs_sub_abs_le_abs_sub s r
  linarith

theorem abs_sinh_le_cosh (x : ℝ) : |sinh x| ≤ cosh x := by
  rw [Real.abs_sinh, ← Real.cosh_abs x]
  exact (Real.sinh_lt_cosh _).le

theorem integrableOn_G1 (r : ℝ) :
    IntegrableOn (fun θ => θ * sinh (θ * r) * Upper.wt θ) (Ioi 1) := by
  have hb := integrableOn_pow_cosh_wt 1 r
  refine hb.mono' ?_ ?_
  · exact ((by fun_prop : Measurable fun θ : ℝ => θ * sinh (θ * r)).mul
      measurable_wt).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hθ0 : 0 < θ := lt_trans one_pos hθ
    have hw := (Upper.wt_pos hθ0).le
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hθ0.le, Real.norm_of_nonneg hw, pow_one,
      Real.norm_eq_abs]
    have := abs_sinh_le_cosh (θ * r)
    gcongr

theorem hasDerivAt_G (r : ℝ) : HasDerivAt Upper.G (G1 r) r := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun θ => cosh (θ * s) * Upper.wt θ)
      (volume.restrict (Ioi 1)) := fun s =>
    ((by fun_prop : Measurable fun θ : ℝ => cosh (θ * s)).mul measurable_wt).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun s θ => cosh (θ * s) * Upper.wt θ)
    (F' := fun s θ => θ * sinh (θ * s) * Upper.wt θ) (x₀ := r)
    (bound := fun θ => θ ^ 1 * cosh (θ * (|r| + 1)) * Upper.wt θ) (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall hmeas) (Upper.integrableOn_G r)
    (integrableOn_G1 r).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun θ hθ s hs => by
      have hθ0 : 0 < θ := lt_trans one_pos hθ
      have hw := (Upper.wt_pos hθ0).le
      rw [norm_mul, norm_mul, Real.norm_of_nonneg hθ0.le, Real.norm_of_nonneg hw, pow_one,
        Real.norm_eq_abs]
      have h1 := abs_sinh_le_cosh (θ * s)
      have h2 := cosh_le_of_ball hθ0.le hs
      gcongr
      exact h1.trans h2))
    (integrableOn_pow_cosh_wt 1 (|r| + 1))
    (Filter.Eventually.of_forall fun θ s _ => by
      have h := ((hasDerivAt_id' s).const_mul θ).cosh.mul_const (Upper.wt θ)
      convert h using 1
      ring)
  exact key.2

theorem hasDerivAt_G1 (r : ℝ) : HasDerivAt G1 (G2 r) r := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun θ => θ * sinh (θ * s) * Upper.wt θ)
      (volume.restrict (Ioi 1)) := fun s => (integrableOn_G1 s).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun s θ => θ * sinh (θ * s) * Upper.wt θ)
    (F' := fun s θ => θ ^ 2 * cosh (θ * s) * Upper.wt θ) (x₀ := r)
    (bound := fun θ => θ ^ 2 * cosh (θ * (|r| + 1)) * Upper.wt θ) (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall hmeas) (integrableOn_G1 r)
    (integrableOn_pow_cosh_wt 2 r).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun θ hθ s hs => by
      have hθ0 : 0 < θ := lt_trans one_pos hθ
      have hw := (Upper.wt_pos hθ0).le
      rw [Real.norm_of_nonneg (by have := cosh_pos (θ * s); positivity)]
      have h2 := cosh_le_of_ball hθ0.le hs
      gcongr))
    (integrableOn_pow_cosh_wt 2 (|r| + 1))
    (Filter.Eventually.of_forall fun θ s _ => by
      have h := (((hasDerivAt_id' s).const_mul θ).sinh.const_mul θ).mul_const (Upper.wt θ)
      convert h using 1
      ring)
  exact key.2

theorem G1_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ G1 r :=
  setIntegral_nonneg measurableSet_Ioi fun θ hθ => by
    have hθ0 : 0 < θ := lt_trans one_pos hθ
    have := (Upper.wt_pos hθ0).le
    have : 0 ≤ sinh (θ * r) := Real.sinh_nonneg_iff.2 (mul_nonneg hθ0.le hr)
    positivity

theorem G_zero_le (r : ℝ) : Upper.G 0 ≤ Upper.G r := Upper.G_mono (by simp)

theorem G_pos (r : ℝ) : 0 < Upper.G r :=
  lt_of_lt_of_le (by rw [G_zero]; exact exp_pos _) (G_zero_le r)

theorem G2_nonneg (r : ℝ) : 0 ≤ G2 r :=
  setIntegral_nonneg measurableSet_Ioi fun θ hθ => by
    have hθ0 : 0 < θ := lt_trans one_pos hθ
    have := (Upper.wt_pos hθ0).le
    have := cosh_pos (θ * r)
    positivity

/-- Cauchy-Schwarz under the integral, in discriminant form. -/
theorem disc_G {l : ℝ} (hl : 0 ≤ l) (r : ℝ) : G1 r ^ 2 ≤ (l + Upper.G r) * G2 r := by
  have hq : ∀ t : ℝ, 0 ≤ Upper.G r * (t * t) + 2 * G1 r * t + G2 r := by
    intro t
    have hi0 := Upper.integrableOn_G r
    have hi1 := integrableOn_G1 r
    have hi2 := integrableOn_pow_cosh_wt 2 r
    have e : Upper.G r * (t * t) + 2 * G1 r * t + G2 r = ∫ θ in Ioi 1,
        (cosh (θ * r) * Upper.wt θ * (t * t) + θ * sinh (θ * r) * Upper.wt θ * (2 * t) +
          θ ^ 2 * cosh (θ * r) * Upper.wt θ) := by
      have hA : IntegrableOn (fun θ => cosh (θ * r) * Upper.wt θ * (t * t) +
          θ * sinh (θ * r) * Upper.wt θ * (2 * t)) (Ioi 1) := (hi0.mul_const _).add (hi1.mul_const _)
      have hB : IntegrableOn (fun θ => cosh (θ * r) * Upper.wt θ * (t * t)) (Ioi 1) :=
        hi0.mul_const _
      have hC : IntegrableOn (fun θ => θ * sinh (θ * r) * Upper.wt θ * (2 * t)) (Ioi 1) :=
        hi1.mul_const _
      rw [integral_add hA hi2, integral_add hB hC, integral_mul_const, integral_mul_const]
      unfold Upper.G G1 G2
      ring
    rw [e]
    refine setIntegral_nonneg measurableSet_Ioi fun θ hθ => ?_
    have hθ0 : 0 < θ := lt_trans one_pos hθ
    have hw := (Upper.wt_pos hθ0).le
    have hp : 0 ≤ cosh (θ * r) * (t * t + θ ^ 2) + 2 * t * θ * sinh (θ * r) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      nlinarith [mul_nonneg (exp_pos (θ * r)).le (sq_nonneg (t + θ)),
        mul_nonneg (exp_pos (-(θ * r))).le (sq_nonneg (t - θ))]
    have : cosh (θ * r) * Upper.wt θ * (t * t) + θ * sinh (θ * r) * Upper.wt θ * (2 * t) +
        θ ^ 2 * cosh (θ * r) * Upper.wt θ =
        Upper.wt θ * (cosh (θ * r) * (t * t + θ ^ 2) + 2 * t * θ * sinh (θ * r)) := by ring
    rw [this]
    exact mul_nonneg hw hp
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hG2 := G2_nonneg r
  nlinarith [mul_nonneg hl hG2]

theorem convexOn_log_G {l : ℝ} (hl : 0 ≤ l) :
    ConvexOn ℝ univ (fun v => Real.log (l + Upper.G v)) := by
  exact
    convex_log Upper.G G1 G2 l (fun v => by have := G_pos v; linarith) hasDerivAt_G
      hasDerivAt_G1 (disc_G hl)

theorem eta_neg_left (l a b : ℝ) : Upper.eta l (-a) b = -Upper.eta l a b := by
  unfold Upper.eta
  have h1 : (-a) + b = -(a - b) := by ring
  have h2 : (-a) - b = -(a + b) := by ring
  rw [h1, h2]
  rw [Upper.G_neg, Upper.G_neg]
  have h3 : (l + Upper.G (a - b)) / (l + Upper.G (a + b)) = ((l + Upper.G (a + b)) / (l + Upper.G (a - b)))⁻¹ := by
    rw [← inv_div]
  rw [h3, Real.log_inv, neg_div, UpperSharp.clip_neg]

theorem eta_le_one (l a b : ℝ) : Upper.eta l a b ≤ 1 := by
  unfold Upper.eta Upper.clip
  exact max_le (by norm_num) (min_le_left _ _)

theorem eta_nonneg {l : ℝ} (hl : 0 < l) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Upper.eta l a b := by
  have ha_add_b_nonneg : 0 ≤ a + b := add_nonneg ha hb
  have h_abs_sub_le_abs_add : |a - b| ≤ |a + b| := by
    calc
      |a - b| ≤ |a| + |b| := abs_sub _ _
      _ = a + b := by rw [abs_of_nonneg ha, abs_of_nonneg hb]
      _ = |a + b| := by rw [abs_of_nonneg ha_add_b_nonneg]
  have hG : Upper.G (a - b) ≤ Upper.G (a + b) :=
    RegretKappa.Upper.G_mono h_abs_sub_le_abs_add
  have h_denom_pos : 0 < l + Upper.G (a - b) := by
    linarith [hl, RegretKappa.Upper.G_nonneg (a - b)]
  have h_ratio_ge_one : 1 ≤ (l + Upper.G (a + b)) / (l + Upper.G (a - b)) := by
    rw [one_le_div h_denom_pos]
    linarith
  have h_log_nonneg : 0 ≤ Real.log ((l + Upper.G (a + b)) / (l + Upper.G (a - b))) :=
    Real.log_nonneg h_ratio_ge_one
  have h_half_nonneg : 0 ≤ Real.log ((l + Upper.G (a + b)) / (l + Upper.G (a - b))) / 2 := by
    nlinarith
  have h_min_nonneg : 0 ≤ min 1 (Real.log ((l + Upper.G (a + b)) / (l + Upper.G (a - b))) / 2) := by
    have h_one_nonneg : (0 : ℝ) ≤ 1 := by norm_num
    exact le_min h_one_nonneg h_half_nonneg
  dsimp [Upper.eta, Upper.clip]
  exact le_trans h_min_nonneg (le_max_right _ _)

theorem clip_le_clip {z z' : ℝ} (h : z ≤ z') : Upper.clip z ≤ Upper.clip z' := by
  unfold Upper.clip
  exact max_le_max (le_refl _) (min_le_min (le_refl _) h)

theorem eta_mono {l : ℝ} (hl : 0 < l) {a a' b : ℝ} (haa : a' ≤ a) (hb : 0 ≤ b) :
    Upper.eta l a' b ≤ Upper.eta l a b := by
  unfold Upper.eta
  apply clip_le_clip
  have hpos : ∀ r : ℝ, 0 < l + Upper.G r := by
    intro r
    have hG : 0 ≤ Upper.G r := Upper.G_nonneg r
    linarith
  have hpos_ne : ∀ r : ℝ, l + Upper.G r ≠ 0 := fun r => (hpos r).ne'
  have h_conv : ConvexOn ℝ Set.univ (fun v => Real.log (l + Upper.G v)) :=
    convexOn_log_G hl.le
  set x₁ := a' - b with hx₁
  set x₂ := a + b with hx₂
  set y₁ := a' + b with hy₁
  set y₂ := a - b with hy₂
  have h1 : x₁ ≤ y₁ := by dsimp [x₁, y₁]; linarith
  have h2 : y₁ ≤ x₂ := by dsimp [y₁, x₂]; linarith
  have h3 : x₁ ≤ y₂ := by dsimp [x₁, y₂]; linarith
  have h4 : y₂ ≤ x₂ := by dsimp [y₂, x₂]; linarith
  have hs : y₁ + y₂ = x₁ + x₂ := by dsimp [x₁, x₂, y₁, y₂]; ring
  have h_ineq := convex_two_point (fun v => Real.log (l + Upper.G v)) h_conv x₁ x₂ y₁ y₂ h1 h2 h3 h4 hs
  have h_sub : Real.log (l + Upper.G y₁) - Real.log (l + Upper.G x₁) ≤
      Real.log (l + Upper.G x₂) - Real.log (l + Upper.G y₂) := by
    linarith
  have h_logdiv_left : Real.log ((l + Upper.G y₁) / (l + Upper.G x₁)) =
      Real.log (l + Upper.G y₁) - Real.log (l + Upper.G x₁) :=
    Real.log_div (hpos_ne y₁) (hpos_ne x₁)
  have h_logdiv_right : Real.log ((l + Upper.G x₂) / (l + Upper.G y₂)) =
      Real.log (l + Upper.G x₂) - Real.log (l + Upper.G y₂) :=
    Real.log_div (hpos_ne x₂) (hpos_ne y₂)
  have h_log_ineq : Real.log ((l + Upper.G y₁) / (l + Upper.G x₁)) ≤
      Real.log ((l + Upper.G x₂) / (l + Upper.G y₂)) := by
    rw [h_logdiv_left, h_logdiv_right]
    exact h_sub
  have hpos_ratio_left : 0 < (l + Upper.G y₁) / (l + Upper.G x₁) := div_pos (hpos y₁) (hpos x₁)
  have hpos_ratio_right : 0 < (l + Upper.G x₂) / (l + Upper.G y₂) := div_pos (hpos x₂) (hpos y₂)
  have h_ratio : (l + Upper.G y₁) / (l + Upper.G x₁) ≤ (l + Upper.G x₂) / (l + Upper.G y₂) :=
    ((Real.log_le_log_iff hpos_ratio_left hpos_ratio_right).mp h_log_ineq)
  have h_div2 : Real.log ((l + Upper.G y₁) / (l + Upper.G x₁)) / 2 ≤
      Real.log ((l + Upper.G x₂) / (l + Upper.G y₂)) / 2 := by
    have : Real.log ((l + Upper.G y₁) / (l + Upper.G x₁)) ≤
        Real.log ((l + Upper.G x₂) / (l + Upper.G y₂)) := h_log_ineq
    linarith
  dsimp [x₁, x₂, y₁, y₂] at h_div2
  exact h_div2

/-- The Lipschitz bound of `G` on `[0, 1]`. -/
theorem G_sub_le {x z : ℝ} (hz : 0 ≤ z) (hzx : z ≤ x) (hx : x ≤ 1) :
    Upper.G x - Upper.G z ≤ 2 * Dg 1 * (x - z) := by
  have hx_nonneg : 0 ≤ x := hz.trans hzx
  by_cases hx0 : x = 0
  · have hz0 : z = 0 := by linarith
    subst hx0 hz0
    simp
  · have hx_pos : 0 < x := by
      by_contra! h
      exact hx0 (le_antisymm h hx_nonneg)
    have hx_sq_pos : 0 < x ^ 2 := pow_pos hx_pos 2
    have hx_sq_le_one : x ^ 2 ≤ 1 := by
      nlinarith
    have hz_sq_nonneg : 0 ≤ z ^ 2 := pow_two_nonneg z
    have hz_sq_le_x_sq : z ^ 2 ≤ x ^ 2 := by
      nlinarith
    have h_sqrt_x : Real.sqrt (x ^ 2) = x := Real.sqrt_sq hx_nonneg
    have h_sqrt_z : Real.sqrt (z ^ 2) = z := Real.sqrt_sq hz
    have h_G_sub := G_sqrt_sub_le hz_sq_nonneg hz_sq_le_x_sq hx_sq_pos
    rw [h_sqrt_x, h_sqrt_z] at h_G_sub
    have h_x_sq_sub_z_sq_le : x ^ 2 - z ^ 2 ≤ 2 * (x - z) := by
      have h_sum_le_two : x + z ≤ 2 := by linarith
      have h_nonneg : 0 ≤ x - z := by linarith
      nlinarith
    have h_Dg_nonneg : 0 ≤ Dg (x ^ 2) := Dg_nonneg hx_sq_pos
    have h_mul1 : (x ^ 2 - z ^ 2) * Dg (x ^ 2) ≤ (2 * (x - z)) * Dg (x ^ 2) :=
      mul_le_mul_of_nonneg_right h_x_sq_sub_z_sq_le h_Dg_nonneg
    have h_Dg_mono : Dg (x ^ 2) ≤ Dg 1 := Dg_mono hx_sq_pos hx_sq_le_one
    have h_nonneg_2x_sub_z : 0 ≤ 2 * (x - z) := by nlinarith
    have h_mul2 : (2 * (x - z)) * Dg (x ^ 2) ≤ (2 * (x - z)) * Dg 1 :=
      mul_le_mul_of_nonneg_left h_Dg_mono h_nonneg_2x_sub_z
    calc
      Upper.G x - Upper.G z ≤ (x ^ 2 - z ^ 2) * Dg (x ^ 2) := h_G_sub
      _ ≤ (2 * (x - z)) * Dg (x ^ 2) := h_mul1
      _ ≤ (2 * (x - z)) * Dg 1 := h_mul2
      _ = 2 * Dg 1 * (x - z) := by ring

/-- The Lipschitz constant of the potential `2 log((l + G w)/A)` on `[-1, 1]`. -/
noncomputable def lipB : ℝ := 4 * Dg 1 / exp (-1 / 2)

theorem psi_lip {l A x z : ℝ} (hl : 0 ≤ l) (hA : 0 < A) (hx : |x| ≤ 1) (hzx : |z| ≤ |x|) :
    2 * Real.log ((l + Upper.G x) / A) - 2 * Real.log ((l + Upper.G z) / A) ≤
      lipB * (|x| - |z|) := by
  have hx_abs_nonneg : 0 ≤ |x| := abs_nonneg _
  have hz_abs_nonneg : 0 ≤ |z| := abs_nonneg _
  have hGx_eq : Upper.G x = Upper.G |x| := by rw [Upper.G_abs]
  have hGz_eq : Upper.G z = Upper.G |z| := by rw [Upper.G_abs]
  rw [hGx_eq, hGz_eq]
  have hg0_pos : 0 < Upper.G 0 := by
    rw [G_zero]
    exact Real.exp_pos _
  have hg0_le_gz : Upper.G 0 ≤ Upper.G |z| :=
    Upper.G_mono (by simp)
  have hgz_le_gx : Upper.G |z| ≤ Upper.G |x| := by
    have h_abs_abs : |(|z|)| ≤ |(|x|)| := by
      simpa [abs_of_nonneg hz_abs_nonneg, abs_of_nonneg hx_abs_nonneg] using hzx
    exact Upper.G_mono h_abs_abs
  have h_ub := lip_log l (Upper.G |x|) (Upper.G |z|) (Upper.G 0) A hl hg0_pos hg0_le_gz hgz_le_gx hA
  have h_final : 2 * (Upper.G |x| - Upper.G |z|) / Upper.G 0 ≤ lipB * (|x| - |z|) := by
    have h_sub : Upper.G |x| - Upper.G |z| ≤ 2 * Dg 1 * (|x| - |z|) :=
      G_sub_le hz_abs_nonneg hzx hx
    have hg0_pos' : 0 < Upper.G 0 := by rw [G_zero]; exact Real.exp_pos _
    have h_num : 2 * (Upper.G |x| - Upper.G |z|) ≤ 2 * (2 * Dg 1 * (|x| - |z|)) := by
      nlinarith
    calc
      2 * (Upper.G |x| - Upper.G |z|) / Upper.G 0 ≤ 2 * (2 * Dg 1 * (|x| - |z|)) / Upper.G 0 :=
        div_le_div_of_nonneg_right h_num (by linarith)
      _ = (4 * Dg 1 / Upper.G 0) * (|x| - |z|) := by ring
      _ = lipB * (|x| - |z|) := by
        rw [lipB, G_zero]
  exact h_ub.trans h_final

end RegretKappa.UnknownBT.UB
