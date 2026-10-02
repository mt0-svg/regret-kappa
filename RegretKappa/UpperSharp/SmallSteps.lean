import RegretKappa.UpperSharp.Weights
import RegretKappa.Upper.SmallSteps

/-!
# Theorem 3.1 with the paper's constants: small steps (the paper, Lemma 3.10)

In the units of `Upper` (`G = Γ/2`): for `b² ≤ 2/3` and every `ρ`,
`Ghat (ρ √(1 - b²)) b ≤ G ρ + 2.8857/2` (`small_step_sharp`).

With `c = √(1 - b²)`, `s = b² = 1 - c²` and `x = c² ∈ [1/3, 1]`, the substitution `u = c θ`
(`Upper.Ghat_subst`, the paper's Lemma 3.9) splits `Ghat (ρ c) b - G ρ` into the cutoff drift on
`(c, 1]` and the drift on `(1, ∞)`, as in the paper's proof of Lemma 3.10. No power series of
`Γ` is used:

* on `(c, 1]`, `cosh(uρ) ≤ 1 + u²ρ²/2 + u⁴ Rf(ρ)` and `e^{-u²/2} ≤ e^{-c²/2}`
  (`integral_P_pt_sharp`), then the antiderivative (`Upper.integral_P_ftc`), the chord bound
  `-log(1 - s) ≤ (3/2) log 3 · s` and the monotonicity in `x` of `e^{-x/2}(1/2 + ℓ₀ x)` and of
  `e^{-x/2}(1/4 + 5x/4)` (`exp_mul_affine_le`): this gives the paper's bounds on `D₀`, `D₁` and,
  for all the terms of order at least four at once, `D_n ≤ 3 e^{-1/2} s`;
* on `(1, ∞)`, the drift is `-2 s H(ρ)` with `H(ρ) = ∫_1^∞ cosh(uρ) e^{-u²/2}/u³` (`tail_eq`), and
  `H(ρ) ≥ ∑_{n ≤ 4} H_n ρ^{2n}/(2n)! + H_5 R₄(ρ)` with `R₄` the terms of order at least ten of
  `cosh` (`H_ge`), `H_0 = J0`, `H_1 = K0`, `H_2, H_3, H_4, H_5 = 1, 3, 13, 79` times `e^{-1/2}`;
* the result is `s f(ρ²)/2` with the paper's quartic `f`, whose coefficients are bounded by
  rationals, and `max f ≤ 4.32855` (`quartic_le`, certificate in
  `code/lean-upper-sharp/out/quartic.txt`), so `s f/2 ≤ (2/3)(4.32855/2) = 2.8857/2`.
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set Finset Filter Topology

/-- The terms of order at least ten of `cosh`. -/
noncomputable def R4 (z : ℝ) : ℝ :=
  cosh z - (1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 + z ^ 8 / 40320)

/-! ### Leaves -/

theorem R4_scale_ge {u : ℝ} (hu : 1 ≤ u) (z : ℝ) : u ^ 10 * R4 z ≤ R4 (u * z) := by
  have hu_nonneg : 0 ≤ u := by linarith
  -- define the term function
  set f : ℕ → ℝ := fun n => z ^ (2 * n) / ((2 * n).factorial : ℝ) with hf
  have hcosh := Real.hasSum_cosh z
  -- hcosh : HasSum (fun n => z ^ (2 * n) / ↑(2 * n).factorial) (cosh z)
  have hsum_range : (∑ i ∈ Finset.range 5, f i) = 1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 + z ^ 8 / 40320 := by
    simp [f, Finset.sum_range_succ]
    norm_num
  have hR4_eq : R4 z = cosh z - (∑ i ∈ Finset.range 5, f i) := by
    rw [R4, hsum_range]
  have htail : HasSum (fun n : ℕ => z ^ (2 * (n + 5)) / ((2 * (n + 5)).factorial : ℝ)) (R4 z) := by
    have h := ((hasSum_nat_add_iff (k := 5) (f := f) (g := R4 z)).mpr ?_)
    · simpa [f] using h
    · -- need: HasSum f (R4 z + ∑ i ∈ range 5, f i)
      have : R4 z + (∑ i ∈ Finset.range 5, f i) = cosh z := by
        rw [hR4_eq]
        ring
      rw [this]
      exact hcosh
  -- Similarly for u*z
  set g : ℕ → ℝ := fun n => (u * z) ^ (2 * n) / ((2 * n).factorial : ℝ) with hg
  have hcosh_uz := Real.hasSum_cosh (u * z)
  have htail_uz : HasSum (fun n : ℕ => (u * z) ^ (2 * (n + 5)) / ((2 * (n + 5)).factorial : ℝ)) (R4 (u * z)) := by
    have h := ((hasSum_nat_add_iff (k := 5) (f := g) (g := R4 (u * z))).mpr ?_)
    · simpa [g] using h
    · have hR4_uz_eq : R4 (u * z) = cosh (u * z) - (∑ i ∈ Finset.range 5, g i) := by
        rw [R4]
        have hsum_range_uz : (∑ i ∈ Finset.range 5, g i) = 1 + (u * z) ^ 2 / 2 + (u * z) ^ 4 / 24 + (u * z) ^ 6 / 720 + (u * z) ^ 8 / 40320 := by
          simp [g, Finset.sum_range_succ]
          norm_num
        rw [hsum_range_uz]
      have : R4 (u * z) + (∑ i ∈ Finset.range 5, g i) = cosh (u * z) := by
        rw [hR4_uz_eq]
        ring
      rw [this]
      exact hcosh_uz
  -- Now we have HasSum for both series. Compare termwise.
  have hterm_le : ∀ n : ℕ, u ^ 10 * (z ^ (2 * (n + 5)) / ((2 * (n + 5)).factorial : ℝ)) ≤
      ((u * z) ^ (2 * (n + 5)) / ((2 * (n + 5)).factorial : ℝ)) := by
    intro n
    have h_nonneg : 0 ≤ z ^ (2 * (n + 5)) := by
      have : 0 ≤ z ^ 2 := sq_nonneg z
      have : z ^ (2 * (n + 5)) = (z ^ 2) ^ (n + 5) := by ring
      rw [this]
      exact pow_nonneg (sq_nonneg z) (n + 5)
    have h_pow : u ^ 10 ≤ u ^ (2 * (n + 5)) := by
      have : 10 ≤ 2 * (n + 5) := by omega
      exact pow_le_pow_right₀ hu this
    calc
      u ^ 10 * (z ^ (2 * (n + 5)) / ((2 * (n + 5)).factorial : ℝ))
          = (u ^ 10 * z ^ (2 * (n + 5))) / ((2 * (n + 5)).factorial : ℝ) := by ring
      _ ≤ (u ^ (2 * (n + 5)) * z ^ (2 * (n + 5))) / ((2 * (n + 5)).factorial : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ (by norm_num : 0 ≤ ((2 * (n + 5)).factorial : ℝ))
        exact mul_le_mul_of_nonneg_right h_pow h_nonneg
      _ = ((u * z) ^ (2 * (n + 5))) / ((2 * (n + 5)).factorial : ℝ) := by ring
  -- Now apply hasSum_le
  have h_sum_mul : HasSum (fun n : ℕ => u ^ 10 * (z ^ (2 * (n + 5)) / ((2 * (n + 5)).factorial : ℝ))) (u ^ 10 * R4 z) := by
    simpa [htail.tsum_eq] using htail.mul_left (u ^ 10)
  have h_le := hasSum_le hterm_le h_sum_mul htail_uz
  -- h_le : u ^ 10 * R4 z ≤ R4 (u * z)
  exact h_le

theorem quartic_le {x : ℝ} (hx : 0 ≤ x) :
    486921756490106881 / 200000000000000000 + 74300499467509331 / 100000000000000000 * x -
      6065306597 / 240000000000 * x ^ 2 - 6065306597 / 800000000000 * x ^ 3 -
      42457146179 / 57600000000000 * x ^ 4 ≤ (4.32855 : ℝ) := by
  set r : ℝ := 3968325 / 1000000 with hr
  set r' : ℝ := 3624531215780403677704827 / 913363816960000000000000 with hr'
  set b2 : ℝ := 6065306597 / 240000000000 with hb2
  set b3 : ℝ := 6065306597 / 800000000000 with hb3
  set b4 : ℝ := 42457146179 / 57600000000000 with hb4
  set C0 : ℝ := 432855/100000 - (486921756490106881/200000000000000000 + 74300499467509331/100000000000000000 * r - 6065306597/240000000000 * r ^ 2 - 6065306597/800000000000 * r ^ 3 - 42457146179/57600000000000 * r ^ 4) - b2 * (r - r') ^ 2 with hC0
  have hC0pos : 0 ≤ C0 := by
    unfold C0 r r' b2
    norm_num
  have hb2pos : 0 ≤ b2 := by
    unfold b2
    norm_num
  have hb3pos : 0 ≤ b3 := by
    unfold b3
    norm_num
  have hb4pos : 0 ≤ b4 := by
    unfold b4
    norm_num
  have hrpos : 0 ≤ r := by
    unfold r
    norm_num
  have hinner_nonneg : 0 ≤ b3 * (x + 2 * r) + b4 * (x ^ 2 + 2 * r * x + 3 * r ^ 2) := by
    have hx2r : 0 ≤ x + 2 * r := by nlinarith
    have hx2 : 0 ≤ x ^ 2 + 2 * r * x + 3 * r ^ 2 := by nlinarith
    nlinarith
  have h_sq_nonneg : 0 ≤ (x - r) ^ 2 := pow_two_nonneg _
  have h_last_nonneg : 0 ≤ (x - r) ^ 2 * (b3 * (x + 2 * r) + b4 * (x ^ 2 + 2 * r * x + 3 * r ^ 2)) := by
    nlinarith
  have hidentity : (4.32855 : ℝ) - (486921756490106881 / 200000000000000000 + 74300499467509331 / 100000000000000000 * x -
      6065306597 / 240000000000 * x ^ 2 - 6065306597 / 800000000000 * x ^ 3 -
      42457146179 / 57600000000000 * x ^ 4) = C0 + b2 * (x - r') ^ 2 + (x - r) ^ 2 * (b3 * (x + 2 * r) + b4 * (x ^ 2 + 2 * r * x + 3 * r ^ 2)) := by
    unfold C0 r r' b2 b3 b4
    ring
  have h_diff_nonneg : 0 ≤ (4.32855 : ℝ) - (486921756490106881 / 200000000000000000 + 74300499467509331 / 100000000000000000 * x -
      6065306597 / 240000000000 * x ^ 2 - 6065306597 / 800000000000 * x ^ 3 -
      42457146179 / 57600000000000 * x ^ 4) := by
    rw [hidentity]
    nlinarith
  linarith

theorem integral_P_pt_sharp (ρ : ℝ) {c u : ℝ} (hc0 : 0 < c) (hcu : c < u) (hu1 : u ≤ 1) :
    cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) ≤
      exp (-c ^ 2 / 2) * ((1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) +
        Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u)) := by
  have hu0 : 0 ≤ u := by linarith
  have hu_pos : 0 < u := by linarith
  have hcu_sq : c ^ 2 < u ^ 2 := by
    nlinarith
  have h_exp : exp (-u ^ 2 / 2) ≤ exp (-c ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h_w_pos : 0 < 1 / u + 2 * c ^ 2 / u ^ 3 := by
    positivity
  have h_cosh_nonneg : 0 ≤ cosh (u * ρ) := by positivity
  have h_cosh_eq : cosh (u * ρ) = 1 + (u * ρ) ^ 2 / 2 + Upper.Rf (u * ρ) := by
    dsimp [Upper.Rf]
    ring
  have h_Rf_scale : Upper.Rf (u * ρ) ≤ u ^ 4 * Upper.Rf ρ :=
    Upper.Rf_scale_le hu0 hu1 ρ
  have h_cosh_le : cosh (u * ρ) ≤ 1 + (u * ρ) ^ 2 / 2 + u ^ 4 * Upper.Rf ρ := by
    linarith
  set w := 1 / u + 2 * c ^ 2 / u ^ 3 with hw_def
  have h_mul_nonneg : 0 ≤ cosh (u * ρ) * w := by
    nlinarith
  have h_mul_exp : cosh (u * ρ) * exp (-u ^ 2 / 2) * w ≤ cosh (u * ρ) * exp (-c ^ 2 / 2) * w := by
    nlinarith
  have h_mul_bound : cosh (u * ρ) * exp (-c ^ 2 / 2) * w ≤
      exp (-c ^ 2 / 2) * (w + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) + Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u)) := by
    have hpos_exp : 0 ≤ exp (-c ^ 2 / 2) := by positivity
    have h1 : cosh (u * ρ) * w ≤ (1 + (u * ρ) ^ 2 / 2 + u ^ 4 * Upper.Rf ρ) * w := by
      nlinarith
    have h2 : (1 + (u * ρ) ^ 2 / 2 + u ^ 4 * Upper.Rf ρ) * w =
        w + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) + Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u) := by
      dsimp [w]
      field_simp [hu_pos.ne.symm]
    calc
      cosh (u * ρ) * exp (-c ^ 2 / 2) * w = exp (-c ^ 2 / 2) * (cosh (u * ρ) * w) := by ring
      _ ≤ exp (-c ^ 2 / 2) * ((1 + (u * ρ) ^ 2 / 2 + u ^ 4 * Upper.Rf ρ) * w) :=
        mul_le_mul_of_nonneg_left h1 hpos_exp
      _ = exp (-c ^ 2 / 2) * (w + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) + Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u)) := by rw [h2]
  calc
    cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)
        = cosh (u * ρ) * exp (-u ^ 2 / 2) * w := by rw [hw_def]
    _ ≤ cosh (u * ρ) * exp (-c ^ 2 / 2) * w := h_mul_exp
    _ ≤ exp (-c ^ 2 / 2) * (w + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) + Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u)) := h_mul_bound
    _ = exp (-c ^ 2 / 2) * ((1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) +
        Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u)) := by rw [hw_def]

theorem tail_eq (ρ : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∫ u in Ioi 1, cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)) - Upper.G ρ =
      -2 * (1 - c ^ 2) * ∫ u in Ioi 1, cosh (u * ρ) * exp (-u ^ 2 / 2) / u ^ 3 := by
  unfold Upper.G Upper.wt
  have h_int_A : IntegrableOn (fun u => cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3)) (Ioi 1) :=
    (Upper.integrableOn_h ρ hc0).mono_set (Ioi_subset_Ioi hc1)
  have h_int_B : IntegrableOn (fun u => cosh (u * ρ) * (exp (-u ^ 2 / 2) * (1 / u + 2 / u ^ 3))) (Ioi 1) := by
    simpa [Upper.wt] using Upper.integrableOn_G ρ
  rw [← integral_sub h_int_A h_int_B]
  have h_integrand : (fun a => cosh (a * ρ) * exp (-a ^ 2 / 2) * (1 / a + 2 * c ^ 2 / a ^ 3) -
      cosh (a * ρ) * (exp (-a ^ 2 / 2) * (1 / a + 2 / a ^ 3))) =
      (fun a => -2 * (1 - c ^ 2) * (cosh (a * ρ) * exp (-a ^ 2 / 2) / a ^ 3)) := by
    ext a
    ring
  rw [h_integrand]
  rw [integral_const_mul]

/-! ### The terms of high order of `cosh` -/

theorem R4_nonneg (z : ℝ) : 0 ≤ R4 z := by
  have h := sum_le_hasSum (range 5)
    (fun i _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)) (Real.hasSum_cosh z)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  unfold R4
  norm_num at h ⊢
  linarith

theorem Rf_eq (z : ℝ) : Upper.Rf z = z ^ 4 / 24 + z ^ 6 / 720 + z ^ 8 / 40320 + R4 z := by
  unfold Upper.Rf R4
  ring

/-! ### The drift on `(1, ∞)` -/

theorem integrableOn_J0 : IntegrableOn (fun θ : ℝ => exp (-θ ^ 2 / 2) / θ ^ 3) (Ioi 1) := by
  refine integrableOn_K0.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun θ hθ => pow_ne_zero 3 (lt_trans one_pos hθ).ne'
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_)
    have hθ : 1 < θ := hθ
    have he := exp_pos (-θ ^ 2 / 2)
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    calc θ = θ ^ 1 := (pow_one θ).symm
      _ ≤ θ ^ 3 := pow_le_pow_right₀ hθ.le (by norm_num)

theorem mom_three : mom 3 = exp (-1 / 2) * 3 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, mom_odd]; norm_num [kk]

theorem mom_five : mom 5 = exp (-1 / 2) * 13 := by
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, mom_odd]; norm_num [kk]

theorem mom_seven : mom 7 = exp (-1 / 2) * 79 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, mom_odd]; norm_num [kk]

/-- `H(ρ) ≥ ∑_{n ≤ 4} H_n ρ^{2n}/(2n)! + H_5 R₄(ρ)`. -/
theorem H_ge (ρ : ℝ) :
    J0 + K0 * (ρ ^ 2 / 2) + mom 1 * (ρ ^ 4 / 24) + mom 3 * (ρ ^ 6 / 720) + mom 5 * (ρ ^ 8 / 40320) +
        mom 7 * R4 ρ ≤ ∫ u in Ioi 1, cosh (u * ρ) * exp (-u ^ 2 / 2) / u ^ 3 := by
  set e : ℝ → ℝ := fun u => exp (-u ^ 2 / 2) with he
  have i0 := integrableOn_J0
  have i1 := integrableOn_K0
  have im := integrableOn_pow_exp
  have iH : IntegrableOn (fun u => cosh (u * ρ) * exp (-u ^ 2 / 2) / u ^ 3) (Ioi 1) := by
    refine (Upper.integrableOn_G ρ).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ContinuousOn.div (by fun_prop) (by fun_prop) fun θ hθ =>
        pow_ne_zero 3 (lt_trans one_pos hθ).ne'
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu : 1 < u := hu
      have hu0 : 0 < u := by linarith
      rw [Real.norm_of_nonneg (by positivity)]
      unfold Upper.wt
      have hc := cosh_pos (u * ρ)
      have hE := exp_pos (-u ^ 2 / 2)
      have h3 : 0 < u ^ 3 := by positivity
      rw [div_le_iff₀ h3]
      have : 1 ≤ u ^ 3 * (1 / u + 2 / u ^ 3) := by
        field_simp
        nlinarith [pow_pos hu0 2]
      nlinarith [mul_pos hc hE]
  have hL : ∫ u in Ioi 1, (exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u) +
      ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2)) + ρ ^ 6 / 720 * (u ^ 3 * exp (-u ^ 2 / 2)) +
      ρ ^ 8 / 40320 * (u ^ 5 * exp (-u ^ 2 / 2)) + R4 ρ * (u ^ 7 * exp (-u ^ 2 / 2))) =
      J0 + K0 * (ρ ^ 2 / 2) + mom 1 * (ρ ^ 4 / 24) + mom 3 * (ρ ^ 6 / 720) +
        mom 5 * (ρ ^ 8 / 40320) + mom 7 * R4 ρ := by
    have a1 : IntegrableOn (fun u : ℝ => ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u)) (Ioi 1) :=
      i1.const_mul _
    have a2 : IntegrableOn (fun u : ℝ => ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2))) (Ioi 1) :=
      (im 1).const_mul _
    have a3 : IntegrableOn (fun u : ℝ => ρ ^ 6 / 720 * (u ^ 3 * exp (-u ^ 2 / 2))) (Ioi 1) :=
      (im 3).const_mul _
    have a4 : IntegrableOn (fun u : ℝ => ρ ^ 8 / 40320 * (u ^ 5 * exp (-u ^ 2 / 2))) (Ioi 1) :=
      (im 5).const_mul _
    have a5 : IntegrableOn (fun u : ℝ => R4 ρ * (u ^ 7 * exp (-u ^ 2 / 2))) (Ioi 1) :=
      (im 7).const_mul _
    have b1 : IntegrableOn (fun u : ℝ => exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u))
      (Ioi 1) := i0.add a1
    have b2 : IntegrableOn (fun u : ℝ => exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u) +
      ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2))) (Ioi 1) := b1.add a2
    have b3 : IntegrableOn (fun u : ℝ => exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u) +
      ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2)) + ρ ^ 6 / 720 * (u ^ 3 * exp (-u ^ 2 / 2))) (Ioi 1) :=
      b2.add a3
    have b4 : IntegrableOn (fun u : ℝ => exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u) +
      ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2)) + ρ ^ 6 / 720 * (u ^ 3 * exp (-u ^ 2 / 2)) +
      ρ ^ 8 / 40320 * (u ^ 5 * exp (-u ^ 2 / 2))) (Ioi 1) := b3.add a4
    rw [integral_add b4 a5, integral_add b3 a4, integral_add b2 a3, integral_add b1 a2,
      integral_add i0 a1, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul]
    simp only [J0, K0, mom]
    ring
  rw [← hL]
  refine setIntegral_mono_on ?_ iH measurableSet_Ioi fun u hu => ?_
  · exact ((((i0.add (i1.const_mul (ρ ^ 2 / 2))).add ((im 1).const_mul (ρ ^ 4 / 24))).add
      ((im 3).const_mul (ρ ^ 6 / 720))).add ((im 5).const_mul (ρ ^ 8 / 40320))).add
      ((im 7).const_mul (R4 ρ))
  · have hu : 1 < u := hu
    have hu0 : 0 < u := by linarith
    have hR := R4_scale_ge hu.le ρ
    have hE := exp_pos (-u ^ 2 / 2)
    have hc : cosh (u * ρ) = 1 + (u * ρ) ^ 2 / 2 + (u * ρ) ^ 4 / 24 + (u * ρ) ^ 6 / 720 +
        (u * ρ) ^ 8 / 40320 + R4 (u * ρ) := by unfold R4; ring
    have h3 : 0 < u ^ 3 := by positivity
    rw [le_div_iff₀ h3, hc]
    have key : u ^ 3 * (exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u) +
        ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2)) + ρ ^ 6 / 720 * (u ^ 3 * exp (-u ^ 2 / 2)) +
        ρ ^ 8 / 40320 * (u ^ 5 * exp (-u ^ 2 / 2)) + R4 ρ * (u ^ 7 * exp (-u ^ 2 / 2))) =
        (1 + (u * ρ) ^ 2 / 2 + (u * ρ) ^ 4 / 24 + (u * ρ) ^ 6 / 720 + (u * ρ) ^ 8 / 40320 +
          u ^ 10 * R4 ρ) * exp (-u ^ 2 / 2) := by
      field_simp
    calc (exp (-u ^ 2 / 2) / u ^ 3 + ρ ^ 2 / 2 * (exp (-u ^ 2 / 2) / u) +
        ρ ^ 4 / 24 * (u ^ 1 * exp (-u ^ 2 / 2)) + ρ ^ 6 / 720 * (u ^ 3 * exp (-u ^ 2 / 2)) +
        ρ ^ 8 / 40320 * (u ^ 5 * exp (-u ^ 2 / 2)) + R4 ρ * (u ^ 7 * exp (-u ^ 2 / 2))) * u ^ 3
        = (1 + (u * ρ) ^ 2 / 2 + (u * ρ) ^ 4 / 24 + (u * ρ) ^ 6 / 720 + (u * ρ) ^ 8 / 40320 +
          u ^ 10 * R4 ρ) * exp (-u ^ 2 / 2) := by rw [mul_comm, key]
      _ ≤ (1 + (u * ρ) ^ 2 / 2 + (u * ρ) ^ 4 / 24 + (u * ρ) ^ 6 / 720 + (u * ρ) ^ 8 / 40320 +
          R4 (u * ρ)) * exp (-u ^ 2 / 2) := by gcongr
      _ = _ := by ring

/-! ### The drift on `(c, 1]` -/

theorem integral_P_le_sharp (ρ : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ u in Ioc c 1, cosh (u * ρ) * exp (-u ^ 2 / 2) * (1 / u + 2 * c ^ 2 / u ^ 3) ≤
      exp (-c ^ 2 / 2) * ((-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
        Upper.Rf ρ * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2))) := by
  have hne : ∀ x ∈ Icc c 1, x ≠ 0 := fun x hx => (lt_of_lt_of_le hc0 hx.1).ne'
  have hint : IntegrableOn (fun u : ℝ => (1 / u + 2 * c ^ 2 / u ^ 3) + ρ ^ 2 / 2 * (u + 2 * c ^ 2 / u) +
      Upper.Rf ρ * (u ^ 3 + 2 * c ^ 2 * u)) (Ioc c 1) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) (continuousOn_const.mul
      (continuousOn_id.add ?_))) (by fun_prop)
    · exact continuousOn_const.div continuousOn_id hne
    · exact continuousOn_const.div (continuousOn_id.pow 3) fun x hx => pow_ne_zero 3 (hne x hx)
    · exact continuousOn_const.div continuousOn_id hne
  rw [← Upper.integral_P_ftc ρ (Upper.Rf ρ) hc0 hc1, ← integral_const_mul]
  exact setIntegral_mono_on ((Upper.integrableOn_h ρ hc0).mono_set Ioc_subset_Ioi_self)
    (hint.const_mul _) measurableSet_Ioc fun u hu => integral_P_pt_sharp ρ hc0 hu.1 hu.2

/-! ### The algebra -/

/-- `e^{-x/2} (α + β x) ≤ e^{-1/2} (α + β)` on `[0, 1]` when `2 (α + β x) ≤ (α + β)(1 + x)`, from
`e^{(1-x)/2} ≤ 2/(1 + x)`. -/
theorem exp_mul_affine_le {x α β : ℝ} (hx0 : 0 ≤ x) (hpos : 0 ≤ α + β * x)
    (h : 2 * (α + β * x) ≤ (α + β) * (1 + x)) :
    exp (-x / 2) * (α + β * x) ≤ exp (-1 / 2) * (α + β) := by
  have h1 : 1 - (1 - x) / 2 ≤ exp (-((1 - x) / 2)) := by
    have := Real.add_one_le_exp (-((1 - x) / 2)); linarith
  have hsplit : exp (-x / 2) = exp (-1 / 2) * exp ((1 - x) / 2) := by
    rw [← exp_add]; ring_nf
  have h2 : exp ((1 - x) / 2) * (1 + x) ≤ 2 := by
    have hp : 0 < exp ((1 - x) / 2) := exp_pos _
    have hm : exp ((1 - x) / 2) * exp (-((1 - x) / 2)) = 1 := by rw [← exp_add]; simp
    nlinarith
  have hE := exp_pos (-1 / 2 : ℝ)
  have hq := exp_pos ((1 - x) / 2)
  rw [hsplit]
  have : exp ((1 - x) / 2) * (α + β * x) * 2 ≤ 2 * (α + β) := by
    nlinarith [mul_le_mul_of_nonneg_left h hq.le, mul_le_mul_of_nonneg_right h2 hpos]
  nlinarith

/-- The coefficients of the bound of Lemma 3.10: the polynomial in `ρ²` is at most
`4.32855/2`, from `quartic_le`. -/
theorem coeffs_le (ρ : ℝ) :
    (exp (-1 / 6) * (3 / 2 * log 3 / 2 + 1) - 2 * J0) +
      (exp (-1 / 2) * (1 / 2 + 3 / 2 * log 3) - 2 * K0) * (ρ ^ 2 / 2) -
      exp (-1 / 2) / 2 * ((ρ ^ 2) ^ 2 / 24) - 9 * exp (-1 / 2) / 2 * ((ρ ^ 2) ^ 3 / 720) -
      49 * exp (-1 / 2) / 2 * ((ρ ^ 2) ^ 4 / 40320) ≤ 4.32855 / 2 := by
  have hy : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hq := quartic_le hy
  have hE := exp_neg_half_bounds
  have hE6 := exp_neg_sixth_le
  have hK := K0_le
  have hK' := K0_ge
  have hJ := J0_add
  have hl3 := log_three_lt
  have hl3' : (1 : ℝ) < log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hc0' : exp (-1 / 6) * (3 / 2 * log 3 / 2 + 1) - 2 * J0 ≤
      486921756490106881 / 200000000000000000 / 2 := by
    have h := mul_le_mul hE6 (by linarith : 3 / 2 * log 3 / 2 + 1 ≤ 3 / 2 * 1.0986123 / 2 + 1)
      (by linarith) (by norm_num)
    linarith
  have hc1' : exp (-1 / 2) * (1 / 2 + 3 / 2 * log 3) - 2 * K0 ≤
      74300499467509331 / 100000000000000000 := by
    have h := mul_le_mul hE.2 (by linarith : 1 / 2 + 3 / 2 * log 3 ≤ 1 / 2 + 3 / 2 * 1.0986123)
      (by linarith) (by norm_num)
    linarith
  have hc1y := mul_le_mul_of_nonneg_right hc1' (by positivity : 0 ≤ ρ ^ 2 / 2)
  have hy2 := mul_le_mul_of_nonneg_right hE.1 (by positivity : 0 ≤ (ρ ^ 2) ^ 2)
  have hy3 := mul_le_mul_of_nonneg_right hE.1 (by positivity : 0 ≤ (ρ ^ 2) ^ 3)
  have hy4 := mul_le_mul_of_nonneg_right hE.1 (by positivity : 0 ≤ (ρ ^ 2) ^ 4)
  linear_combination hc0' + hc1y + (1 / 48) * hy2 + (9 / 1440) * hy3 + (49 / 80640) * hy4 +
    (1 / 2) * hq

/-- The real inequality that closes Lemma 3.10, in the units of `G`, with `s = 1 - c²`,
`x = c²`, `y = ρ²`. -/
theorem small_alg_sharp (ρ : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hc3 : 1 / 3 ≤ c ^ 2) (H : ℝ)
    (hH : J0 + K0 * (ρ ^ 2 / 2) + mom 1 * (ρ ^ 4 / 24) + mom 3 * (ρ ^ 6 / 720) +
      mom 5 * (ρ ^ 8 / 40320) + mom 7 * R4 ρ ≤ H) :
    exp (-c ^ 2 / 2) * ((-log c + (1 - c ^ 2)) + ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
        Upper.Rf ρ * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2))) + -2 * (1 - c ^ 2) * H ≤
      2.8857 / 2 := by
  have hs0 : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hs1 : 1 - c ^ 2 ≤ 2 / 3 := by linarith
  have hx1 : c ^ 2 ≤ 1 := by nlinarith
  have hx0 : 0 ≤ c ^ 2 := sq_nonneg c
  -- the logarithms: `log c = log (1 - s)/2` and the chord bound
  have hlogc : log c = log (1 - (1 - c ^ 2)) / 2 := by
    rw [show 1 - (1 - c ^ 2) = c ^ 2 by ring, Real.log_pow]; push_cast; ring
  have hchord := chord_log hs0 hs1
  have hl3 := log_three_lt
  have hl3' : (1 : ℝ) < log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hlc : log c ≤ 0 := Real.log_nonpos hc0.le hc1
  have hA0 : -log c + (1 - c ^ 2) ≤ (1 - c ^ 2) * (3 / 2 * log 3 / 2 + 1) := by
    rw [hlogc]; nlinarith
  have hA1 : (1 - c ^ 2) / 2 - 2 * c ^ 2 * log c ≤ (1 - c ^ 2) * (1 / 2 + 3 / 2 * log 3 * c ^ 2) := by
    rw [hlogc]; nlinarith [mul_le_mul_of_nonneg_left hchord hx0]
  have hA2 : (1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2) = (1 - c ^ 2) * (1 / 4 + 5 / 4 * c ^ 2) := by
    ring
  -- the exponential factors
  have he0 : exp (-c ^ 2 / 2) ≤ exp (-1 / 6) := Real.exp_le_exp.2 (by linarith)
  have hP : exp (-c ^ 2 / 2) * (-log c + (1 - c ^ 2)) ≤
      exp (-1 / 6) * (3 / 2 * log 3 / 2 + 1) * (1 - c ^ 2) := by
    have hA0' : 0 ≤ -log c + (1 - c ^ 2) := by linarith
    calc exp (-c ^ 2 / 2) * (-log c + (1 - c ^ 2))
        ≤ exp (-1 / 6) * ((1 - c ^ 2) * (3 / 2 * log 3 / 2 + 1)) :=
          mul_le_mul he0 hA0 hA0' (exp_pos _).le
      _ = _ := by ring
  have hQ : exp (-c ^ 2 / 2) * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) ≤
      exp (-1 / 2) * (1 / 2 + 3 / 2 * log 3) * (1 - c ^ 2) := by
    have hm := exp_mul_affine_le (α := 1 / 2) (β := 3 / 2 * log 3) hx0 (by nlinarith)
      (by nlinarith)
    calc exp (-c ^ 2 / 2) * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c)
        ≤ exp (-c ^ 2 / 2) * ((1 - c ^ 2) * (1 / 2 + 3 / 2 * log 3 * c ^ 2)) :=
          mul_le_mul_of_nonneg_left hA1 (exp_pos _).le
      _ = (1 - c ^ 2) * (exp (-c ^ 2 / 2) * (1 / 2 + 3 / 2 * log 3 * c ^ 2)) := by ring
      _ ≤ (1 - c ^ 2) * (exp (-1 / 2) * (1 / 2 + 3 / 2 * log 3)) := mul_le_mul_of_nonneg_left hm hs0
      _ = _ := by ring
  have hR : exp (-c ^ 2 / 2) * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2)) ≤
      3 / 2 * exp (-1 / 2) * (1 - c ^ 2) := by
    have hm := exp_mul_affine_le (α := 1 / 4) (β := 5 / 4) hx0 (by nlinarith) (by nlinarith)
    rw [hA2]
    calc exp (-c ^ 2 / 2) * ((1 - c ^ 2) * (1 / 4 + 5 / 4 * c ^ 2))
        = (1 - c ^ 2) * (exp (-c ^ 2 / 2) * (1 / 4 + 5 / 4 * c ^ 2)) := by ring
      _ ≤ (1 - c ^ 2) * (exp (-1 / 2) * (1 / 4 + 5 / 4)) := mul_le_mul_of_nonneg_left hm hs0
      _ = _ := by ring
  -- the moments and the terms of high order
  have hm1 := mom_one
  have hm3 := mom_three
  have hm5 := mom_five
  have hm7 := mom_seven
  have hRf := Rf_eq ρ
  have hR4 := R4_nonneg ρ
  have hy : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hRf0 : 0 ≤ Upper.Rf ρ := (by positivity : (0 : ℝ) ≤ ρ ^ 4 / 24).trans (Upper.Rf_ge ρ)
  -- `F = f(ρ²)/2` with the paper's quartic `f`
  have hFdef : ∃ F : ℝ, F = (exp (-1 / 6) * (3 / 2 * log 3 / 2 + 1) - 2 * J0) +
      (exp (-1 / 2) * (1 / 2 + 3 / 2 * log 3) - 2 * K0) * (ρ ^ 2 / 2) -
      exp (-1 / 2) / 2 * ((ρ ^ 2) ^ 2 / 24) - 9 * exp (-1 / 2) / 2 * ((ρ ^ 2) ^ 3 / 720) -
      49 * exp (-1 / 2) / 2 * ((ρ ^ 2) ^ 4 / 40320) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ := hFdef
  have t1 := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ ρ ^ 2 / 2)
  have t2 := mul_le_mul_of_nonneg_left hR hRf0
  have t3 := mul_le_mul_of_nonneg_left hH (by linarith : 0 ≤ 2 * (1 - c ^ 2))
  have t4 : 0 ≤ (1 - c ^ 2) * exp (-1 / 2) * R4 ρ := by
    have := exp_pos (-1 / 2 : ℝ); positivity
  have hmain : exp (-c ^ 2 / 2) * ((-log c + (1 - c ^ 2)) +
      ρ ^ 2 / 2 * ((1 - c ^ 2) / 2 - 2 * c ^ 2 * log c) +
      Upper.Rf ρ * ((1 - c ^ 4) / 4 + c ^ 2 * (1 - c ^ 2))) + -2 * (1 - c ^ 2) * H ≤
      (1 - c ^ 2) * F := by
    rw [hF]
    linear_combination hP + t1 + t2 + t3 + (313 / 2) * t4 +
      (3 / 2 * exp (-1 / 2) * (1 - c ^ 2)) * hRf - (2 * (1 - c ^ 2) * (ρ ^ 4 / 24)) * hm1 -
      (2 * (1 - c ^ 2) * (ρ ^ 6 / 720)) * hm3 - (2 * (1 - c ^ 2) * (ρ ^ 8 / 40320)) * hm5 -
      (2 * (1 - c ^ 2) * R4 ρ) * hm7
  -- the quartic
  have hFle : F ≤ 4.32855 / 2 := hF ▸ coeffs_le ρ
  have hfin : (1 - c ^ 2) * F ≤ 2.8857 / 2 := by
    rcases le_or_gt F 0 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos hs0 h
      linarith
    · have := mul_le_mul_of_nonneg_right hs1 h.le
      linarith
  linarith

/-- **Small steps** (the paper, Lemma 3.10, in the units of `G`): for `b² ≤ 2/3`,
`Ghat (ρ √(1 - b²)) b ≤ G ρ + 2.8857/2`. -/
theorem small_step_sharp (ρ : ℝ) {b : ℝ} (hb : b ^ 2 ≤ 2 / 3) :
    Upper.Ghat (ρ * √(1 - b ^ 2)) b ≤ Upper.G ρ + 2.8857 / 2 := by
  have hb0 : 0 ≤ 1 - b ^ 2 := by nlinarith [sq_nonneg b]
  have hc2 : √(1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt hb0
  have hcn := Real.sqrt_nonneg (1 - b ^ 2)
  have hc3 : 1 / 3 ≤ √(1 - b ^ 2) ^ 2 := by rw [hc2]; linarith
  have hc1 : √(1 - b ^ 2) ≤ 1 := by nlinarith [sq_nonneg b]
  have hcpos : 0 < √(1 - b ^ 2) := by
    rcases eq_or_lt_of_le hcn with h | h
    · rw [← h] at hc3; norm_num at hc3
    · exact h
  have hi := Upper.integrableOn_h ρ hcpos
  rw [Upper.Ghat_subst ρ hcpos (by linarith), ← Set.Ioc_union_Ioi_eq_Ioi hc1,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi (hi.mono_set Set.Ioc_subset_Ioi_self)
      (hi.mono_set (Set.Ioi_subset_Ioi hc1))]
  have h1 := integral_P_le_sharp ρ hcpos hc1
  have h2 := tail_eq ρ hcpos hc1
  have h3 := small_alg_sharp ρ hcpos hc1 hc3 _ (H_ge ρ)
  linarith

end RegretKappa.UpperSharp
