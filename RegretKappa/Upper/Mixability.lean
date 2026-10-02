import RegretKappa.Upper.Gamma

/-!
# Upper bound: mixability of the square loss on the mixtures

The paper, Sections 3.3 and 3.4. For `|η| ≤ 1` the two-point
inequality `(1 + η) e^{x - η} + (1 - η) e^{-(x - η)} ≤ 2 e^{x²/2 - η²/2}` (Hoeffding's lemma for
a two-point law, the paper's Lemma A.3) holds for every real `x`; integrated against the mixture it
gives `(1 + η) e^{-η} A₊ + (1 - η) e^{η} A₋ ≤ 2 e^{-η²/2} Z` with `A_± = λ + G(a ± b)` and
`Z = λ + Ghat a b`, and the learner's clipped `η` then makes both terms at most `e^{-η²/2} Z`
(Lemma A.4 and Corollary A.5). Convexity of `exp` reduces an outcome `y ∈ [-1, 1]` to the
endpoints (Lemma A.2).
-/

namespace RegretKappa.Upper

open Real MeasureTheory Set

/-- Convexity of `exp` between `-z` and `z`. -/
theorem exp_mul_le {y : ℝ} (hy : |y| ≤ 1) (z : ℝ) :
    exp (y * z) ≤ (1 + y) / 2 * exp z + (1 - y) / 2 * exp (-z) := by
  have hy' : -1 ≤ y ∧ y ≤ 1 := abs_le.mp hy
  rcases hy' with ⟨hyle, hyge⟩
  set a := (1 + y) / 2 with ha
  set b := (1 - y) / 2 with hb
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    nlinarith
  have hsum : a + b = 1 := by
    dsimp [a, b]
    ring
  have h_eq : y * z = a * z + b * (-z) := by
    dsimp [a, b]
    ring
  have h := convexOn_exp.2 (mem_univ z) (mem_univ (-z)) ha_nonneg hb_nonneg hsum
  simpa [smul_eq_mul, h_eq] using h

open ProbabilityTheory in
/-- Hoeffding's lemma for the two-point law `p δ_{1-p} + (1-p) δ_{-p}`. -/
theorem two_point_mgf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    p * exp (t * (1 - p)) + (1 - p) * exp (t * (-p)) ≤ exp (t ^ 2 / 8) := by
  set μ : Measure ℝ := ENNReal.ofReal p • Measure.dirac (1 - p) +
    ENNReal.ofReal (1 - p) • Measure.dirac (-p) with hμ
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [hμ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp0 (by linarith)]
    simp
  have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂μ = p * f (1 - p) + (1 - p) * f (-p) := by
    intro f
    rw [hμ, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
      smul_eq_mul]
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hX : ∀ᵐ x ∂μ, x ∈ Set.Icc (-p) (1 - p) := by
    rw [hμ, ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      exact (ae_dirac_iff measurableSet_Icc).2 ⟨by linarith, by linarith⟩
    · refine Measure.ae_smul_measure ?_ _
      exact (ae_dirac_iff measurableSet_Icc).2 ⟨by linarith, by linarith⟩
  have hmean : μ[id] = 0 := by
    rw [hint]
    simp only [id]
    ring
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := id) aemeasurable_id hX hmean
  have h := hsub.mgf_le t
  rw [mgf, hint] at h
  have hn : (((‖(1 - p) - (-p)‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 / 4 := by
    rw [show (1 - p) - (-p) = (1 : ℝ) by ring]
    simp
    norm_num
  rw [hn] at h
  simp only [id] at h
  calc p * exp (t * (1 - p)) + (1 - p) * exp (t * (-p)) = p * exp (t * (1 - p)) + (1 - p) * exp (t * (-p)) := rfl
    _ ≤ exp (1 / 4 * t ^ 2 / 2) := h
    _ = exp (t ^ 2 / 8) := by ring_nf

/-- Hoeffding's lemma for a two-point law, in the form used for mixability at rate `1/2`. -/
theorem two_point {η : ℝ} (hη : |η| ≤ 1) (x : ℝ) :
    (1 + η) * exp (x - η) + (1 - η) * exp (-(x - η)) ≤ 2 * exp (x ^ 2 / 2 - η ^ 2 / 2) := by
  have h := abs_le.1 hη
  have hm := two_point_mgf (p := (1 + η) / 2) (by linarith) (by linarith) (2 * (x - η))
  have hE : 0 < exp (η * (x - η)) := exp_pos _
  have k1 : exp (η * (x - η)) * exp (2 * (x - η) * (1 - (1 + η) / 2)) = exp (x - η) := by
    rw [← exp_add]; congr 1; ring
  have k2 : exp (η * (x - η)) * exp (2 * (x - η) * -((1 + η) / 2)) = exp (-(x - η)) := by
    rw [← exp_add]; congr 1; ring
  have k3 : exp (η * (x - η)) * exp ((2 * (x - η)) ^ 2 / 8) = exp (x ^ 2 / 2 - η ^ 2 / 2) := by
    rw [← exp_add]; congr 1; ring
  rw [← k1, ← k2, ← k3]
  nlinarith [mul_le_mul_of_nonneg_left hm hE.le]

theorem abs_clip_le (z : ℝ) : |clip z| ≤ 1 := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- The learner's clipped choice satisfies both inequalities of the two-point game whenever
every `η ∈ [-1, 1]` satisfies their average. -/
theorem mix_alg {p q Z : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : ∀ η : ℝ, |η| ≤ 1 → (1 + η) * exp (-η) * p + (1 - η) * exp η * q ≤ 2 * exp (-η ^ 2 / 2) * Z) :
    exp (-clip (log (p / q) / 2)) * p ≤ exp (-clip (log (p / q) / 2) ^ 2 / 2) * Z ∧
      exp (clip (log (p / q) / 2)) * q ≤ exp (-clip (log (p / q) / 2) ^ 2 / 2) * Z := by
  have hdivpos : 0 < p / q := div_pos hp hq
  set r := log (p / q) / 2 with hr_def
  have h2r : 2 * r = log (p / q) := by
    dsimp [r]
    ring
  have hexp2r : exp (2 * r) = p / q := by
    rw [h2r, Real.exp_log hdivpos]
  have hexpr_eq : exp r * exp r = p / q := by
    rw [← Real.exp_add]
    have : r + r = 2 * r := by ring
    rw [this, hexp2r]
  have h_eq_m : exp (-r) * p = exp r * q := by
    calc
      exp (-r) * p = exp (-r) * (q * (p / q)) := by field_simp [hq.ne']
      _ = exp (-r) * (q * exp (2 * r)) := by rw [hexp2r]
      _ = exp (-r) * q * exp (2 * r) := by ring
      _ = q * (exp (-r) * exp (2 * r)) := by ring
      _ = q * exp (-r + 2 * r) := by rw [Real.exp_add]
      _ = q * exp r := by ring_nf
      _ = exp r * q := mul_comm _ _
  have h_clip_eq_r (hle1 : r ≤ 1) (hge_neg1 : -1 ≤ r) : clip r = r := by
    dsimp [clip]
    rw [min_eq_right hle1, max_eq_right hge_neg1]
  have h_clip_eq_one (hgt1 : 1 < r) : clip r = 1 := by
    dsimp [clip]
    rw [min_eq_left (by linarith : (1 : ℝ) ≤ r), max_eq_right (by norm_num : (-1 : ℝ) ≤ (1 : ℝ))]
  have h_clip_eq_neg_one (hlt_neg1 : r < -1) : clip r = -1 := by
    dsimp [clip]
    rw [min_eq_right (by linarith : r ≤ (1 : ℝ)), max_eq_left (by linarith : r ≤ (-1 : ℝ))]
  by_cases hle1 : r ≤ 1
  · by_cases hge_neg1 : -1 ≤ r
    · -- Case: -1 ≤ r ≤ 1
      have hclip : clip r = r := h_clip_eq_r hle1 hge_neg1
      have habs : |r| ≤ 1 := abs_le.mpr ⟨hge_neg1, hle1⟩
      have h_ineq := h r habs
      have hm : exp (-r) * p = exp r * q := h_eq_m
      have hsum : (1 + r) * exp (-r) * p + (1 - r) * exp r * q = 2 * (exp (-r) * p) := by
        calc
          (1 + r) * exp (-r) * p + (1 - r) * exp r * q
              = (1 + r) * (exp (-r) * p) + (1 - r) * (exp r * q) := by ring
          _ = (1 + r) * (exp (-r) * p) + (1 - r) * (exp (-r) * p) := by rw [hm]
          _ = ((1 + r) + (1 - r)) * (exp (-r) * p) := by ring
          _ = 2 * (exp (-r) * p) := by ring
      have h_main : exp (-r) * p ≤ exp (-r ^ 2 / 2) * Z := by
        have htemp : 2 * (exp (-r) * p) ≤ 2 * exp (-r ^ 2 / 2) * Z := by
          linarith
        linarith
      have h_second : exp r * q ≤ exp (-r ^ 2 / 2) * Z := by
        rw [← hm]
        exact h_main
      rw [hclip]
      exact And.intro h_main h_second
    · -- Case: r < -1
      have hclip : clip r = -1 := h_clip_eq_neg_one (by linarith)
      have habs : |(-1 : ℝ)| ≤ 1 := by
        simp [abs_one]
      have h_ineq := h (-1 : ℝ) habs
      have h_second : exp (-1 : ℝ) * q ≤ exp (-((-1 : ℝ) ^ 2) / 2) * Z := by
        have htemp : 2 * exp (-1 : ℝ) * q ≤ 2 * exp (-((-1 : ℝ) ^ 2) / 2) * Z := by
          calc
            2 * exp (-1 : ℝ) * q = (1 + (-1 : ℝ)) * exp (-(-1 : ℝ)) * p + (1 - (-1 : ℝ)) * exp (-1 : ℝ) * q := by ring
            _ ≤ 2 * exp (-((-1 : ℝ) ^ 2) / 2) * Z := h_ineq
        linarith
      have h_first_lt : exp (-(-1 : ℝ)) * p < exp (-((-1 : ℝ) ^ 2) / 2) * Z := by
        have h_exp_lt : exp (2 * r) < exp (-2 : ℝ) :=
          (Real.exp_lt_exp).mpr (by linarith : 2 * r < (-2 : ℝ))
        have h_pq_lt : p / q < exp (-2 : ℝ) := by
          rw [← hexp2r]
          exact h_exp_lt
        have hp_lt : p < exp (-2 : ℝ) * q := by
          calc
            p = (p / q) * q := by field_simp [hq.ne']
            _ < exp (-2 : ℝ) * q := mul_lt_mul_of_pos_right h_pq_lt hq
        calc
          exp (-(-1 : ℝ)) * p = exp (1 : ℝ) * p := by norm_num
          _ < exp (1 : ℝ) * (exp (-2 : ℝ) * q) := by
            exact mul_lt_mul_of_pos_left hp_lt (Real.exp_pos _)
          _ = (exp (1 : ℝ) * exp (-2 : ℝ)) * q := by ring
          _ = exp ((1 : ℝ) + (-2 : ℝ)) * q := by rw [Real.exp_add]
          _ = exp (-1 : ℝ) * q := by norm_num
          _ ≤ exp (-((-1 : ℝ) ^ 2) / 2) * Z := h_second
      have h_first : exp (-(-1 : ℝ)) * p ≤ exp (-((-1 : ℝ) ^ 2) / 2) * Z := le_of_lt h_first_lt
      rw [hclip]
      exact And.intro h_first h_second
  · -- Case: r > 1
    have hclip : clip r = 1 := h_clip_eq_one (by linarith)
    have habs : |(1 : ℝ)| ≤ 1 := by
      simp
    have h_ineq := h 1 habs
    have hfirst : exp (-1 : ℝ) * p ≤ exp (-(1 : ℝ) ^ 2 / 2) * Z := by
      have htemp : 2 * exp (-1 : ℝ) * p ≤ 2 * exp (-(1/2 : ℝ)) * Z := by
        calc
          2 * exp (-1 : ℝ) * p = (1 + (1 : ℝ)) * exp (-1 : ℝ) * p + (1 - (1 : ℝ)) * exp (1 : ℝ) * q := by ring
          _ ≤ 2 * exp (-(1 : ℝ) ^ 2 / 2) * Z := h_ineq
          _ = 2 * exp (-(1/2 : ℝ)) * Z := by norm_num
      linarith
    have hsecond : exp (1 : ℝ) * q ≤ exp (-(1 : ℝ) ^ 2 / 2) * Z := by
      have h_exp_lt : exp (2 : ℝ) < exp (2 * r) :=
        (Real.exp_lt_exp).mpr (by linarith : (2 : ℝ) < 2 * r)
      have h_pq_gt : exp (2 : ℝ) < p / q := by
        rw [← hexp2r]
        exact h_exp_lt
      have hp_gt : exp (2 : ℝ) * q < p := by
        calc
          exp (2 : ℝ) * q < (p / q) * q := mul_lt_mul_of_pos_right h_pq_gt hq
          _ = p := by field_simp [hq.ne']
      have hpr_lt : exp (1 : ℝ) * q < exp (-1 : ℝ) * p := by
        calc
          exp (1 : ℝ) * q = (exp (-1 : ℝ) * exp (2 : ℝ)) * q := by
            rw [← Real.exp_add]
            norm_num
          _ = exp (-1 : ℝ) * (exp (2 : ℝ) * q) := by ring
          _ < exp (-1 : ℝ) * p :=
            mul_lt_mul_of_pos_left hp_gt (Real.exp_pos _)
      calc
        exp (1 : ℝ) * q ≤ exp (-1 : ℝ) * p := le_of_lt hpr_lt
        _ ≤ exp (-(1 : ℝ) ^ 2 / 2) * Z := hfirst
    rw [hclip]
    exact And.intro hfirst hsecond

/-- Pointwise form of the reduction to the endpoints `y = ±1`. -/
theorem cosh_convex_pt (η a b θ : ℝ) {y : ℝ} (hy : |y| ≤ 1) :
    exp (-(η * y)) * cosh (θ * (a + b * y)) ≤
      (1 + y) / 2 * exp (-η) * cosh (θ * (a + b)) + (1 - y) / 2 * exp η * cosh (θ * (a - b)) := by
  rw [Real.cosh_eq (θ * (a + b * y)), Real.cosh_eq (θ * (a + b)), Real.cosh_eq (θ * (a - b))]
  have h1 := exp_mul_le hy (θ * b - η)
  have h2 := exp_mul_le hy (-θ * b - η)
  have hpos1 : 0 ≤ exp (θ * a) := by positivity
  have hpos2 : 0 ≤ exp (-θ * a) := by positivity
  have hLHS : exp (-(η * y)) * ((exp (θ * (a + b * y)) + exp (-(θ * (a + b * y)))) / 2) =
      (exp (θ * a) * exp (y * (θ * b - η)) + exp (-θ * a) * exp (y * (-θ * b - η))) / 2 := by
    calc
      exp (-(η * y)) * ((exp (θ * (a + b * y)) + exp (-(θ * (a + b * y)))) / 2)
          = (exp (-(η * y)) * exp (θ * (a + b * y)) + exp (-(η * y)) * exp (-(θ * (a + b * y)))) / 2 := by ring_nf
      _ = (exp (-(η * y) + θ * (a + b * y)) + exp ((-(η * y)) + (-(θ * (a + b * y))))) / 2 := by
        rw [← Real.exp_add (-(η * y)) (θ * (a + b * y)), ← Real.exp_add (-(η * y)) (-(θ * (a + b * y)))]
      _ = (exp (θ * a + y * (θ * b - η)) + exp (-θ * a + y * (-θ * b - η))) / 2 := by ring_nf
      _ = (exp (θ * a) * exp (y * (θ * b - η)) + exp (-θ * a) * exp (y * (-θ * b - η))) / 2 := by
        rw [Real.exp_add (θ * a) (y * (θ * b - η)), Real.exp_add (-θ * a) (y * (-θ * b - η))]
  rw [hLHS]
  have hRHS : (1 + y) / 2 * exp (-η) * ((exp (θ * (a + b)) + exp (-(θ * (a + b)))) / 2) +
      (1 - y) / 2 * exp η * ((exp (θ * (a - b)) + exp (-(θ * (a - b)))) / 2) =
      ((1 + y) / 4 * exp (-η) * (exp (θ * (a + b)) + exp (-(θ * (a + b)))) +
       (1 - y) / 4 * exp η * (exp (θ * (a - b)) + exp (-(θ * (a - b))))) := by ring_nf
  rw [hRHS]
  have hineq1 : exp (θ * a) * exp (y * (θ * b - η)) ≤
      exp (θ * a) * ((1 + y) / 2 * exp (θ * b - η) + (1 - y) / 2 * exp (-(θ * b - η))) := by
    nlinarith
  have h2' : exp (y * (-θ * b - η)) ≤ (1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (θ * b + η) := by
    have h := exp_mul_le hy (-θ * b - η)
    -- h : exp (y * (-θ * b - η)) ≤ (1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (-(-θ * b - η))
    -- rewrite the last term
    have hneg : -(-θ * b - η) = θ * b + η := by ring
    simpa [hneg, add_comm] using h
  have hineq2 : exp (-θ * a) * exp (y * (-θ * b - η)) ≤
      exp (-θ * a) * ((1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (θ * b + η)) := by
    nlinarith
  have hsum : (exp (θ * a) * exp (y * (θ * b - η)) + exp (-θ * a) * exp (y * (-θ * b - η))) / 2 ≤
      (exp (θ * a) * ((1 + y) / 2 * exp (θ * b - η) + (1 - y) / 2 * exp (-(θ * b - η))) +
       exp (-θ * a) * ((1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (θ * b + η))) / 2 := by
    nlinarith
  have h_eq : (exp (θ * a) * ((1 + y) / 2 * exp (θ * b - η) + (1 - y) / 2 * exp (-(θ * b - η))) +
       exp (-θ * a) * ((1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (θ * b + η))) / 2 =
      ((1 + y) / 4 * exp (-η) * (exp (θ * (a + b)) + exp (-(θ * (a + b)))) +
       (1 - y) / 4 * exp η * (exp (θ * (a - b)) + exp (-(θ * (a - b))))) := by
    have h2pos : (2 : ℝ) ≠ 0 := by norm_num
    rw [div_eq_iff_mul_eq h2pos]
    -- Goal: ((1 + y) / 4 * exp (-η) * (exp (θ * (a + b)) + exp (-(θ * (a + b)))) +
    --        (1 - y) / 4 * exp η * (exp (θ * (a - b)) + exp (-(θ * (a - b))))) * 2 =
    --       exp (θ * a) * ((1 + y) / 2 * exp (θ * b - η) + (1 - y) / 2 * exp (-(θ * b - η))) +
    --       exp (-θ * a) * ((1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (θ * b + η))
    calc
      ((1 + y) / 4 * exp (-η) * (exp (θ * (a + b)) + exp (-(θ * (a + b)))) +
       (1 - y) / 4 * exp η * (exp (θ * (a - b)) + exp (-(θ * (a - b))))) * 2
          = (1 + y) / 2 * exp (-η) * (exp (θ * (a + b)) + exp (-(θ * (a + b)))) +
            (1 - y) / 2 * exp η * (exp (θ * (a - b)) + exp (-(θ * (a - b)))) := by ring
      _ = (1 + y) / 2 * exp (-η) * (exp (θ * a + θ * b) + exp (-θ * a - θ * b)) +
          (1 - y) / 2 * exp η * (exp (θ * a - θ * b) + exp (-θ * a + θ * b)) := by ring_nf
      _ = (1 + y) / 2 * (exp (θ * a + θ * b - η) + exp (-θ * a - θ * b - η)) +
          (1 - y) / 2 * (exp (θ * a - θ * b + η) + exp (-θ * a + θ * b + η)) := by
        simp [Real.exp_add, sub_eq_add_neg]
        ring
      _ = (1 + y) / 2 * (exp (θ * a) * exp (θ * b - η) + exp (-θ * a) * exp (-θ * b - η)) +
          (1 - y) / 2 * (exp (θ * a) * exp (-(θ * b - η)) + exp (-θ * a) * exp (θ * b + η)) := by
        simp [Real.exp_add, sub_eq_add_neg]
        ring_nf
      _ = exp (θ * a) * ((1 + y) / 2 * exp (θ * b - η) + (1 - y) / 2 * exp (-(θ * b - η))) +
          exp (-θ * a) * ((1 + y) / 2 * exp (-θ * b - η) + (1 - y) / 2 * exp (θ * b + η)) := by ring
  apply le_trans hsum
  rw [h_eq]

/-- Pointwise form of the two-point inequality on the mixture. -/
theorem cosh_tangent_pt (a b θ : ℝ) {η : ℝ} (hη : |η| ≤ 1) :
    (1 + η) * exp (-η) * cosh (θ * (a + b)) + (1 - η) * exp η * cosh (θ * (a - b)) ≤
      2 * exp (-η ^ 2 / 2) * (cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2)) := by
  have h1 := two_point hη (θ * b)
  have h2 := two_point hη (-(θ * b))
  have e1 : exp (θ * b - η) = exp (θ * b) * exp (-η) := by rw [← exp_add]; ring_nf
  have e2 : exp (-(θ * b - η)) = exp (-(θ * b)) * exp η := by rw [← exp_add]; ring_nf
  have e3 : exp (-(θ * b) - η) = exp (-(θ * b)) * exp (-η) := by rw [← exp_add]; ring_nf
  have e4 : exp (-(-(θ * b) - η)) = exp (θ * b) * exp η := by rw [← exp_add]; ring_nf
  have e5 : exp ((θ * b) ^ 2 / 2 - η ^ 2 / 2) = exp (θ ^ 2 * b ^ 2 / 2) * exp (-η ^ 2 / 2) := by
    rw [← exp_add]; ring_nf
  have e6 : exp ((-(θ * b)) ^ 2 / 2 - η ^ 2 / 2) = exp (θ ^ 2 * b ^ 2 / 2) * exp (-η ^ 2 / 2) := by
    rw [← exp_add]; ring_nf
  rw [e1, e2, e5] at h1
  rw [e3, e4, e6] at h2
  have c1 : cosh (θ * (a + b)) = (exp (θ * a) * exp (θ * b) + exp (-(θ * a)) * exp (-(θ * b))) / 2 := by
    rw [cosh_eq, ← exp_add, ← exp_add]; ring_nf
  have c2 : cosh (θ * (a - b)) = (exp (θ * a) * exp (-(θ * b)) + exp (-(θ * a)) * exp (θ * b)) / 2 := by
    rw [cosh_eq, ← exp_add, ← exp_add]; ring_nf
  have c3 : cosh (θ * a) = (exp (θ * a) + exp (-(θ * a))) / 2 := cosh_eq _
  rw [c1, c2, c3]
  have hA := (exp_pos (θ * a)).le
  have hA' := (exp_pos (-(θ * a))).le
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hA']

/-- A pointwise inequality between nonnegative combinations integrates. -/
theorem setIntegral_comb_le {s : Set ℝ} (hs : MeasurableSet s) {f g h : ℝ → ℝ} {c₀ c₁ c₂ : ℝ}
    (hf : IntegrableOn f s) (hg : IntegrableOn g s) (hh : IntegrableOn h s)
    (hpt : ∀ θ ∈ s, c₀ * f θ ≤ c₁ * g θ + c₂ * h θ) :
    c₀ * (∫ θ in s, f θ) ≤ c₁ * (∫ θ in s, g θ) + c₂ * ∫ θ in s, h θ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.const_mul _) (hh.const_mul _)]
  exact setIntegral_mono_on (hf.const_mul _) ((hg.const_mul _).add (hh.const_mul _)) hs hpt

/-- The same with the combination on the left. -/
theorem setIntegral_comb_ge {s : Set ℝ} (hs : MeasurableSet s) {f g h : ℝ → ℝ} {c₀ c₁ c₂ : ℝ}
    (hf : IntegrableOn f s) (hg : IntegrableOn g s) (hh : IntegrableOn h s)
    (hpt : ∀ θ ∈ s, c₁ * g θ + c₂ * h θ ≤ c₀ * f θ) :
    c₁ * (∫ θ in s, g θ) + c₂ * (∫ θ in s, h θ) ≤ c₀ * ∫ θ in s, f θ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.const_mul _) (hh.const_mul _)]
  exact setIntegral_mono_on ((hg.const_mul _).add (hh.const_mul _)) (hf.const_mul _) hs hpt

theorem G_convex (η a b : ℝ) {y : ℝ} (hy : |y| ≤ 1) :
    exp (-(η * y)) * G (a + b * y) ≤
      (1 + y) / 2 * exp (-η) * G (a + b) + (1 - y) / 2 * exp η * G (a - b) := by
  unfold G
  refine setIntegral_comb_le measurableSet_Ioi (integrableOn_G _) (integrableOn_G _)
    (integrableOn_G _) fun θ hθ => ?_
  have hw := (wt_pos (lt_trans one_pos hθ)).le
  have := mul_le_mul_of_nonneg_right (cosh_convex_pt η a b θ hy) hw
  linarith

theorem G_tangent (a : ℝ) {b η : ℝ} (hb : b ^ 2 < 1) (hη : |η| ≤ 1) :
    (1 + η) * exp (-η) * G (a + b) + (1 - η) * exp η * G (a - b) ≤ 2 * exp (-η ^ 2 / 2) * Ghat a b := by
  unfold G Ghat
  refine setIntegral_comb_ge measurableSet_Ioi (integrableOn_Ghat a b hb) (integrableOn_G _)
    (integrableOn_G _) fun θ hθ => ?_
  have hw := (wt_pos (lt_trans one_pos hθ)).le
  have := mul_le_mul_of_nonneg_right (cosh_tangent_pt a b θ hη) hw
  linarith

/-- The learner's step against any majorant `M` of the two-point averages. -/
theorem mix_step {lam a b y M : ℝ} (hlam : 0 < lam) (hy : |y| ≤ 1)
    (hM : ∀ η : ℝ, |η| ≤ 1 →
      (1 + η) * exp (-η) * (lam + G (a + b)) + (1 - η) * exp η * (lam + G (a - b)) ≤
        2 * exp (-η ^ 2 / 2) * M) :
    exp (eta lam a b ^ 2 / 2 - eta lam a b * y) * (lam + G (a + b * y)) ≤ M := by
  have hp : 0 < lam + G (a + b) := add_pos_of_pos_of_nonneg hlam (G_nonneg _)
  have hq : 0 < lam + G (a - b) := add_pos_of_pos_of_nonneg hlam (G_nonneg _)
  have h1 : exp (-eta lam a b) * (lam + G (a + b)) ≤ exp (-eta lam a b ^ 2 / 2) * M :=
    (mix_alg hp hq hM).1
  have h2 : exp (eta lam a b) * (lam + G (a - b)) ≤ exp (-eta lam a b ^ 2 / 2) * M :=
    (mix_alg hp hq hM).2
  set η := eta lam a b
  have hy' := abs_le.1 hy
  have hc := G_convex η a b hy
  have he : exp (-(η * y)) ≤ (1 + y) / 2 * exp (-η) + (1 - y) / 2 * exp η := by
    have := exp_mul_le hy (-η)
    rwa [neg_neg, mul_neg, mul_comm] at this
  have key : exp (-(η * y)) * (lam + G (a + b * y)) ≤ exp (-η ^ 2 / 2) * M := by
    have k1 := mul_le_mul_of_nonneg_right he hlam.le
    have k2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ (1 + y) / 2)
    have k3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ (1 - y) / 2)
    nlinarith
  calc exp (η ^ 2 / 2 - η * y) * (lam + G (a + b * y))
        = exp (η ^ 2 / 2) * (exp (-(η * y)) * (lam + G (a + b * y))) := by
          rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (η ^ 2 / 2) * (exp (-η ^ 2 / 2) * M) := mul_le_mul_of_nonneg_left key (exp_pos _).le
    _ = M := by rw [← mul_assoc, ← exp_add]; ring_nf; simp

/-- The two-point inequality at `x = 0`. -/
theorem two_point_zero {η : ℝ} (hη : |η| ≤ 1) :
    (1 + η) * exp (-η) + (1 - η) * exp η ≤ 2 * exp (-η ^ 2 / 2) := by
  have := two_point hη 0
  simpa [neg_div] using this

/-- Mixability (Corollary A.5 of the paper). -/
theorem mix_small {lam a b y : ℝ} (hlam : 0 < lam) (hy : |y| ≤ 1) (hb : b ^ 2 < 1) :
    exp (eta lam a b ^ 2 / 2 - eta lam a b * y) * (lam + G (a + b * y)) ≤ lam + Ghat a b := by
  refine mix_step hlam hy fun η hη => ?_
  have h0 := mul_le_mul_of_nonneg_right (two_point_zero hη) hlam.le
  have ht := G_tangent a hb hη
  nlinarith

/-- The learner does at least as well as the prediction `0` (case `s ≥ 2/3` of the paper). -/
theorem mix_large {lam a b y : ℝ} (hlam : 0 < lam) (hy : |y| ≤ 1) :
    exp (eta lam a b ^ 2 / 2 - eta lam a b * y) * (lam + G (a + b * y)) ≤
      lam + max (G (a + b)) (G (a - b)) := by
  refine mix_step hlam hy fun η hη => ?_
  have hη' := abs_le.1 hη
  have hm : 0 ≤ lam + max (G (a + b)) (G (a - b)) :=
    add_nonneg hlam.le ((G_nonneg _).trans (le_max_left _ _))
  have h0 := mul_le_mul_of_nonneg_right (two_point_zero hη) hm
  have e1 : (1 + η) * exp (-η) * (lam + G (a + b)) ≤ (1 + η) * exp (-η) * (lam + max (G (a + b)) (G (a - b))) :=
    mul_le_mul_of_nonneg_left (by linarith [le_max_left (G (a + b)) (G (a - b))])
      (mul_nonneg (by linarith) (exp_pos _).le)
  have e2 : (1 - η) * exp η * (lam + G (a - b)) ≤ (1 - η) * exp η * (lam + max (G (a + b)) (G (a - b))) :=
    mul_le_mul_of_nonneg_left (by linarith [le_max_right (G (a + b)) (G (a - b))])
      (mul_nonneg (by linarith) (exp_pos _).le)
  nlinarith

end RegretKappa.Upper
