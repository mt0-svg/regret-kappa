import RegretKappa.UpperSharp.Moments
import RegretKappa.UpperSharp.Statement
import RegretKappa.Upper.Gamma

/-!
# Theorem 3.1 with the paper's constants: the terminal condition

The paper, Lemma 3.4: for `ρ ≥ 2`, `√(2π) e^{ρ²/2} ≤ (ρ + 1) Γ(ρ)` (`terminal_ineq`), and so
`C (λ₀ + Γ(ρ)) ≥ e^{ρ²/2}` for `|ρ| ≤ √T`, that is `Φ₀(ρ) ≥ ρ²` (`terminal_sharp`). With
`γ(θ) = e^{-(θ-ρ)²/2}`, `Z = ∫_1^∞ γ`, `M = ∫_1^∞ θγ = ρ Z + e^{-(ρ-1)²/2}` and
`I = ∫_1^∞ γ/θ`: `e^{ρ²/2} I ≤ Γ(ρ)` (`Gam_ge_int`); the tangent `1/θ ≥ 2a - a²θ` at `a = Z/M`
gives `I ≥ Z²/M` (`tangent_int`); the
Mills ratio bound `√(2π) - Z ≤ e^{-(ρ-1)²/2}/(ρ - 1)` (`Z_add_lower`, `lower_tail_le`);
`Z ≥ √(2π)/2 + ∫_0^1 e^{-u²/2} ≥ √(2π)/2 + 0.8556` (`Z_ge`, `int01_ge`); and the number
`2φ(1)/N(1) + φ(1)/N(1)² < 1` of the paper, in the form `mills_num`.
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set Finset Filter Topology

/-! ### Numbers -/

/-- The Mills constant of Lemma 3.4: `2E/A + √(2π)E/A² < 1` for `E ≤ e^{-1/2}` (rational
bound) and `A ≥ √(2π)/2 + 0.8556`. -/
theorem mills_num {E A : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 0.6065306598)
    (hA : √(2 * π) / 2 + 0.8556 ≤ A) :
    2 * E / A + √(2 * π) * E / A ^ 2 < 1 := by
  obtain ⟨hs1, hs2⟩ := sqrt_two_pi_bounds
  have hA0 : 2.108914 ≤ A := by linarith
  have hApos : 0 < A := by linarith
  have h1 : 2 * E / A ≤ 2 * 0.6065306598 / 2.108914 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hA0
  have h2 : √(2 * π) * E / A ^ 2 ≤ 2.506629 * 0.6065306598 / 2.108914 ^ 2 :=
    div_le_div₀ (by norm_num) (mul_le_mul hs2 hE hE0 (by norm_num)) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hA0 2)
  have h3 : (2 * 0.6065306598 / 2.108914 + 2.506629 * 0.6065306598 / 2.108914 ^ 2 : ℝ) < 1 := by
    norm_num
  linarith

/-- `e^{-v} ≥ 1 - v + v²/2 - v³/6 + v⁴/24 - v⁵/120` for `v ≥ 0`. -/
theorem exp_neg_ge_quintic {v : ℝ} (hv : 0 ≤ v) :
    1 - v + v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 24 - v ^ 5 / 120 ≤ exp (-v) := by
  have h := expNegT_alt 6 hv
  simp only [expNegT, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- `∫_0^1 e^{-u²/2} du ≥ 0.8556`, from the quintic Taylor bound of `e^{-v}`. -/
theorem int01_ge : (0.8556 : ℝ) ≤ ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) := by
  have hle : ∫ u in (0 : ℝ)..1, (1 - (u ^ 2 / 2) + (u ^ 2 / 2) ^ 2 / 2 - (u ^ 2 / 2) ^ 3 / 6 + (u ^ 2 / 2) ^ 4 / 24 - (u ^ 2 / 2) ^ 5 / 120) ≤
      ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) fun u _ => ?_
    have := exp_neg_ge_quintic (v := u ^ 2 / 2) (by positivity)
    rw [neg_div]; exact this
  have hval : ∫ u in (0 : ℝ)..1, (1 - (u ^ 2 / 2) + (u ^ 2 / 2) ^ 2 / 2 - (u ^ 2 / 2) ^ 3 / 6 + (u ^ 2 / 2) ^ 4 / 24 - (u ^ 2 / 2) ^ 5 / 120) =
      1 - 1 / 6 + 1 / 40 - 1 / 336 + 1 / 3456 - 1 / 42240 := by
    have e : ∀ u : ℝ, 1 - (u ^ 2 / 2) + (u ^ 2 / 2) ^ 2 / 2 - (u ^ 2 / 2) ^ 3 / 6 + (u ^ 2 / 2) ^ 4 / 24 - (u ^ 2 / 2) ^ 5 / 120 =
        1 - (1 / 2) * u ^ 2 + (1 / 8) * u ^ 4 - (1 / 48) * u ^ 6 + (1 / 384) * u ^ 8 - (1 / 3840) * u ^ 10 := fun u => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · simp [integral_pow]; norm_num
    all_goals first
      | exact intervalIntegral.intervalIntegrable_const
      | (apply Continuous.intervalIntegrable; fun_prop)
  rw [hval] at hle
  linarith [show (0.8556 : ℝ) ≤ 1 - 1 / 6 + 1 / 40 - 1 / 336 + 1 / 3456 - 1 / 42240 by norm_num]


/-! ### Gaussian integrals on half-lines -/

/-- `∫_0^∞ e^{-u²/2} du = √(2π)/2`. -/
theorem gauss_Ioi_zero : ∫ u in Ioi (0 : ℝ), exp (-u ^ 2 / 2) = √(2 * π) / 2 := by
  have h := integral_gaussian_Ioi (1/2 : ℝ)
  have h_eq : (fun u : ℝ => exp (-u ^ 2 / 2)) = (fun u : ℝ => exp (-(1/2 : ℝ) * u ^ 2)) := by
    ext u; ring_nf
  rw [h_eq, h]
  ring_nf

/-- The Mills ratio bound `∫_x^∞ e^{-u²/2} du ≤ e^{-x²/2}/x` for `x > 0`. -/
theorem gauss_tail_le {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi x, exp (-u ^ 2 / 2) ≤ exp (-x ^ 2 / 2) / x := by
  have hx' : 0 ≤ x := le_of_lt hx
  -- exp(-u²/2) ≥ 0 for all u
  have h_exp_nonneg : ∀ u : ℝ, 0 ≤ exp (-(u ^ 2) / 2) := fun u => exp_nonneg _
  -- On Ioi x, u ≥ x > 0, so 1 ≤ u/x, hence exp(-u²/2) ≤ (u/x) * exp(-u²/2)
  have h_bound : ∀ u ∈ Ioi x, exp (-(u ^ 2) / 2) ≤ (u / x) * exp (-(u ^ 2) / 2) := by
    intro u hu
    have hu_pos : 0 < u := by linarith [Set.mem_Ioi.mp hu, hx]
    have h_one_le_div : 1 ≤ u / x := by
      rw [one_le_div hx]
      exact le_of_lt (Set.mem_Ioi.mp hu)
    calc
      exp (-(u ^ 2) / 2) = 1 * exp (-(u ^ 2) / 2) := by ring
      _ ≤ (u / x) * exp (-(u ^ 2) / 2) := by
        nlinarith [exp_nonneg (-(u ^ 2) / 2)]
  -- integrability of exp(-u²/2) on Ioi x
  have h_int_left : IntegrableOn (fun u => exp (-(u ^ 2) / 2)) (Ioi x) := by
    have h_int : Integrable (fun u => exp (-((1/2 : ℝ)) * u ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))
    have h_eq : (fun u => exp (-(u ^ 2) / 2)) = (fun u => exp (-((1/2 : ℝ)) * u ^ 2)) := by
      ext u; ring_nf
    rw [h_eq]
    exact h_int.integrableOn
  -- integrability of (u/x) * exp(-u²/2) on Ioi x, via F(u) = -exp(-u²/2)
  have h_int_right : IntegrableOn (fun u => (u / x) * exp (-(u ^ 2) / 2)) (Ioi x) := by
    have h_int_F' : IntegrableOn (fun u => u * exp (-(u ^ 2) / 2)) (Ioi x) := by
      set F := fun u => -exp (-(u ^ 2) / 2) with hF
      set F' := fun u => u * exp (-(u ^ 2) / 2) with hF'
      refine integrableOn_Ioi_deriv_of_nonneg (g := F) (g' := F') (l := 0) ?_ ?_ ?_ ?_
      · -- F is continuous on Ici x
        have h_cont : ContinuousOn F (Ici x) := by
          dsimp [F]
          refine (Continuous.neg ?_).continuousOn
          refine Real.continuous_exp.comp ?_
          continuity
        exact h_cont.continuousWithinAt (Set.mem_Ici.mpr (le_refl x))
      · -- derivative of F at u in Ioi x is F' u
        intro u hu
        dsimp [F, F']
        have h_deriv_sq : HasDerivAt (fun t => t ^ 2) (2 * u) u := by
          simpa using hasDerivAt_pow 2 u
        have h_deriv_neg_sq_div_two : HasDerivAt (fun t => -(t ^ 2) / 2) (-u) u := by
          have h_neg : HasDerivAt (fun t => -(t ^ 2)) (-(2 * u)) u := by
            apply h_deriv_sq.neg
          have h_div := h_neg.div_const 2
          simpa [show (-(2 * u) / 2) = (-u) by ring] using h_div
        have h_deriv_exp : HasDerivAt (fun t => exp (-(t ^ 2) / 2))
            (exp (-(u ^ 2) / 2) * (-u)) u := by
          simpa using h_deriv_neg_sq_div_two.exp
        have h_deriv_F : HasDerivAt (fun t => -exp (-(t ^ 2) / 2))
            (-(exp (-(u ^ 2) / 2) * (-u))) u := by
          apply h_deriv_exp.neg
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_deriv_F
      · -- F' u ≥ 0 on Ioi x
        intro u hu
        dsimp [F']
        have hu_pos : 0 < u := by linarith [Set.mem_Ioi.mp hu, hx]
        nlinarith [exp_nonneg (-(u ^ 2) / 2)]
      · -- F(u) → 0 as u → ∞
        dsimp [F]
        have h_sq_tendsto : Tendsto (fun (u : ℝ) => u ^ 2 / 2) atTop atTop := by
          have h_sq : Tendsto (fun u => u ^ 2) atTop atTop :=
            Filter.tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0)
          exact h_sq.atTop_div_const (by norm_num : 0 < (2 : ℝ))
        have h_exp_tendsto : Tendsto (fun u => exp (-(u ^ 2 / 2))) atTop (nhds 0) := by
          refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (f := fun (u : ℝ) => u ^ 2 / 2) ?_).congr ?_
          · exact h_sq_tendsto
          · intro u; rfl
        simpa [neg_div] using h_exp_tendsto.neg
    -- Now (u/x) * exp(-u²/2) = (1/x) * (u * exp(-u²/2))
    have h_eq : (fun u => (u / x) * exp (-(u ^ 2) / 2)) =
        (fun u => (1/x) * (u * exp (-(u ^ 2) / 2))) := by
      ext u; ring
    rw [h_eq]
    exact h_int_F'.const_mul (1/x)
  -- Apply setIntegral_mono_on
  have h_meas : MeasurableSet (Ioi x) := measurableSet_Ioi
  have h_int_ineq := setIntegral_mono_on h_int_left h_int_right h_meas h_bound
  -- Now compute the RHS integral: ∫ (u/x) * exp(-u²/2) = exp(-x²/2) / x
  have h_int_rhs_eq : ∫ u in Ioi x, (u / x) * exp (-(u ^ 2) / 2) = exp (-(x ^ 2) / 2) / x := by
    calc
      ∫ u in Ioi x, (u / x) * exp (-(u ^ 2) / 2) = ∫ u in Ioi x, ((1/x) * (u * exp (-(u ^ 2) / 2))) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
        intro u hu
        ring
      _ = (1/x) * ∫ u in Ioi x, u * exp (-(u ^ 2) / 2) := by
        rw [integral_const_mul]
      _ = (1/x) * exp (-(x ^ 2) / 2) := by
        have h_key : ∫ u in Ioi x, u * exp (-(u ^ 2) / 2) = exp (-(x ^ 2) / 2) := by
          set F := fun u => -exp (-(u ^ 2) / 2) with hF
          set F' := fun u => u * exp (-(u ^ 2) / 2) with hF'
          have h_cont : ContinuousWithinAt F (Ici x) x := by
            dsimp [F]
            refine Continuous.continuousWithinAt ?_
            refine Continuous.neg ?_
            refine Real.continuous_exp.comp ?_
            continuity
          have h_deriv : ∀ u ∈ Ioi x, HasDerivAt F (F' u) u := by
            intro u hu
            dsimp [F, F']
            have h_deriv_sq : HasDerivAt (fun t => t ^ 2) (2 * u) u := by
              simpa using hasDerivAt_pow 2 u
            have h_deriv_neg_sq_div_two : HasDerivAt (fun t => -(t ^ 2) / 2) (-u) u := by
              have h_neg : HasDerivAt (fun t => -(t ^ 2)) (-(2 * u)) u := by
                apply h_deriv_sq.neg
              have h_div := h_neg.div_const 2
              simpa [show (-(2 * u) / 2) = (-u) by ring] using h_div
            have h_deriv_exp : HasDerivAt (fun t => exp (-(t ^ 2) / 2))
                (exp (-(u ^ 2) / 2) * (-u)) u := by
              simpa using h_deriv_neg_sq_div_two.exp
            have h_deriv_F : HasDerivAt (fun t => -exp (-(t ^ 2) / 2))
                (-(exp (-(u ^ 2) / 2) * (-u))) u := by
              apply h_deriv_exp.neg
            simpa [mul_comm, mul_left_comm, mul_assoc] using h_deriv_F
          have h_int_F' : IntegrableOn F' (Ioi x) := by
            dsimp [F']
            refine integrableOn_Ioi_deriv_of_nonneg (g := F) (g' := fun u => u * exp (-(u ^ 2) / 2)) (l := 0) ?_ h_deriv ?_ ?_
            · have h_cont_on : ContinuousOn F (Ici x) := by
                dsimp [F]
                refine Continuous.neg ?_ |>.continuousOn
                refine Real.continuous_exp.comp ?_
                continuity
              exact h_cont_on.continuousWithinAt (Set.mem_Ici.mpr (le_refl x))
            · intro u hu
              have hu_pos : 0 < u := by linarith [Set.mem_Ioi.mp hu, hx]
              nlinarith [exp_nonneg (-(u ^ 2) / 2)]
            · dsimp [F]
              have h_sq_tendsto : Tendsto (fun (u : ℝ) => u ^ 2 / 2) atTop atTop := by
                have h_sq : Tendsto (fun u => u ^ 2) atTop atTop :=
                  Filter.tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0)
                exact h_sq.atTop_div_const (by norm_num : 0 < (2 : ℝ))
              have h_exp_tendsto : Tendsto (fun u => exp (-(u ^ 2 / 2))) atTop (nhds 0) := by
                refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (f := fun (u : ℝ) => u ^ 2 / 2) ?_).congr ?_
                · exact h_sq_tendsto
                · intro u; rfl
              simpa [neg_div] using h_exp_tendsto.neg
          have h_tendsto : Tendsto F atTop (nhds 0) := by
            dsimp [F]
            have h_sq_tendsto : Tendsto (fun (u : ℝ) => u ^ 2 / 2) atTop atTop := by
              have h_sq : Tendsto (fun u => u ^ 2) atTop atTop :=
                Filter.tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0)
              exact h_sq.atTop_div_const (by norm_num : 0 < (2 : ℝ))
            have h_exp_tendsto : Tendsto (fun u => exp (-(u ^ 2 / 2))) atTop (nhds 0) := by
              refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (f := fun (u : ℝ) => u ^ 2 / 2) ?_).congr ?_
              · exact h_sq_tendsto
              · intro u; rfl
            simpa [neg_div] using h_exp_tendsto.neg
          rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_int_F' h_tendsto]
          dsimp [F]
          simp
        rw [h_key]
      _ = exp (-(x ^ 2) / 2) / x := by ring
  -- Combine
  linarith

/-- `∫_{-∞}^1 γ + ∫_1^∞ γ = √(2π)` for `γ(θ) = e^{-(θ-ρ)²/2}`. -/
theorem Z_add_lower (ρ : ℝ) :
    (∫ θ in Iic 1, exp (-(θ - ρ) ^ 2 / 2)) + ∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2) = √(2 * π) := by
  have h_disjoint : Disjoint (Iic (1 : ℝ)) (Ioi (1 : ℝ)) :=
    Set.Iic_disjoint_Ioi (le_refl 1)
  have h_meas_Iic : MeasurableSet (Iic (1 : ℝ)) :=
    measurableSet_Iic
  have h_meas_Ioi : MeasurableSet (Ioi (1 : ℝ)) :=
    measurableSet_Ioi
  have h_union : Iic (1 : ℝ) ∪ Ioi (1 : ℝ) = Set.univ :=
    Set.Iic_union_Ioi
  have hb : 0 < (1/2 : ℝ) := by norm_num
  have h_int_gauss : Integrable (fun (x : ℝ) => exp (-(1/2 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have h_int_shifted : Integrable (fun (x : ℝ) => exp (-(1/2 : ℝ) * (x - ρ) ^ 2)) :=
    h_int_gauss.comp_sub_right ρ
  have h_eq_fun : (fun (θ : ℝ) => exp (-(θ - ρ) ^ 2 / 2)) =
                 (fun (θ : ℝ) => exp (-(1/2 : ℝ) * (θ - ρ) ^ 2)) := by
    ext θ; ring_nf
  have h_int : Integrable (fun (θ : ℝ) => exp (-(θ - ρ) ^ 2 / 2)) := by
    rw [h_eq_fun]
    exact h_int_shifted
  have h_intOn_Iic : IntegrableOn (fun (θ : ℝ) => exp (-(θ - ρ) ^ 2 / 2)) (Iic 1) :=
    h_int.integrableOn
  have h_intOn_Ioi : IntegrableOn (fun (θ : ℝ) => exp (-(θ - ρ) ^ 2 / 2)) (Ioi 1) :=
    h_int.integrableOn
  calc
    (∫ θ in Iic 1, exp (-(θ - ρ) ^ 2 / 2)) + ∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2)
        = ∫ θ in Iic 1 ∪ Ioi 1, exp (-(θ - ρ) ^ 2 / 2) := by
      rw [MeasureTheory.setIntegral_union h_disjoint h_meas_Ioi h_intOn_Iic h_intOn_Ioi]
    _ = ∫ θ in Set.univ, exp (-(θ - ρ) ^ 2 / 2) := by rw [h_union]
    _ = ∫ θ, exp (-(θ - ρ) ^ 2 / 2) := by rw [MeasureTheory.setIntegral_univ]
    _ = ∫ θ, exp (-(1/2 : ℝ) * (θ - ρ) ^ 2) := by rw [h_eq_fun]
    _ = ∫ θ, exp (-(1/2 : ℝ) * θ ^ 2) := by
      rw [MeasureTheory.integral_sub_right_eq_self (fun (θ : ℝ) => exp (-(1/2 : ℝ) * θ ^ 2)) ρ]
    _ = √(π / (1/2 : ℝ)) := by rw [integral_gaussian (1/2 : ℝ)]
    _ = √(2 * π) := by ring_nf

/-- The Mills ratio bound for the lower part: `∫_{-∞}^1 γ ≤ e^{-(ρ-1)²/2}/(ρ - 1)` for `ρ > 1`. -/
theorem lower_tail_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∫ θ in Iic 1, exp (-(θ - ρ) ^ 2 / 2) ≤ exp (-(ρ - 1) ^ 2 / 2) / (ρ - 1) := by
  have hpos : 0 < ρ - 1 := by linarith
  have hmeas : MeasurableSet (Iic (1 : ℝ)) := measurableSet_Iic
  set f := fun (θ : ℝ) => exp (-(θ - ρ) ^ 2 / 2) with hf
  set f' := fun (θ : ℝ) => (ρ - θ) * exp (-(θ - ρ) ^ 2 / 2) with hf'
  -- pointwise inequality: for θ ≤ 1, f(θ) ≤ f'(θ) / (ρ-1)
  have hineq : ∀ θ ∈ Iic (1 : ℝ), f θ ≤ f' θ / (ρ - 1) := by
    intro θ hθ
    have hθle : θ ≤ 1 := hθ
    have hnum : ρ - 1 ≤ ρ - θ := by linarith
    have hpos' : 0 < ρ - θ := by linarith
    have h_exp_nonneg : 0 ≤ exp (-(θ - ρ) ^ 2 / 2) := by positivity
    -- from ρ-1 ≤ ρ-θ and ρ-1 > 0, we get 1 ≤ (ρ-θ)/(ρ-1)
    -- so f(θ) = f(θ) * 1 ≤ f(θ) * (ρ-θ)/(ρ-1) = f'(θ)/(ρ-1)
    have h_div : 1 ≤ (ρ - θ) / (ρ - 1) := by
      refine (one_le_div ?_).mpr hnum
      exact hpos
    have h_mul : f θ * 1 ≤ f θ * ((ρ - θ) / (ρ - 1)) :=
      mul_le_mul_of_nonneg_left h_div h_exp_nonneg
    calc
      f θ = f θ * 1 := by ring
      _ ≤ f θ * ((ρ - θ) / (ρ - 1)) := h_mul
      _ = f' θ / (ρ - 1) := by
        dsimp [f, f']
        ring
  have h_int_f : IntegrableOn f (Iic (1 : ℝ)) := by
    have h_int : Integrable (fun (x : ℝ) => exp (-(1/2 : ℝ) * x ^ 2)) := by
      simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    have h_int_sub : Integrable (fun (θ : ℝ) => exp (-(1/2 : ℝ) * (θ - ρ) ^ 2)) :=
      h_int.comp_sub_right ρ
    have h_eq : f = fun (θ : ℝ) => exp (-(1/2 : ℝ) * (θ - ρ) ^ 2) := by
      ext θ; dsimp [f]; ring_nf
    rw [h_eq]
    exact h_int_sub.integrableOn
  have h_int_f' : IntegrableOn f' (Iic (1 : ℝ)) := by
    -- f'(θ) = (ρ-θ) * exp(-(θ-ρ)²/2) = -(θ-ρ) * exp(-(1/2)*(θ-ρ)²)
    have h_int : Integrable (fun (x : ℝ) => x * exp (-(1/2 : ℝ) * x ^ 2)) := by
      simpa using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    have h_int_sub : Integrable (fun (θ : ℝ) => (θ - ρ) * exp (-(1/2 : ℝ) * (θ - ρ) ^ 2)) :=
      h_int.comp_sub_right ρ
    -- f'(θ) = -(θ-ρ) * exp(-(1/2)*(θ-ρ)²)
    have h_eq : f' = fun (θ : ℝ) => -((θ - ρ) * exp (-(1/2 : ℝ) * (θ - ρ) ^ 2)) := by
      ext θ
      dsimp [f']
      ring_nf
    rw [h_eq]
    exact h_int_sub.neg.integrableOn
  have h_cont : ContinuousWithinAt f (Iic (1 : ℝ)) 1 := by
    have h_cont_all : Continuous f := by
      dsimp [f]
      refine Real.continuous_exp.comp ?_
      continuity
    exact h_cont_all.continuousWithinAt
  have h_deriv : ∀ x ∈ Iio (1 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    dsimp [f, f']
    -- f(x) = exp(g(x)) where g(x) = -(x-ρ)²/2
    -- f'(x) = exp(g(x)) * g'(x) = exp(g(x)) * (-(x-ρ)) = (ρ-x) * exp(g(x))
    have h_g : HasDerivAt (fun (θ : ℝ) => -(θ - ρ) ^ 2 / 2) (-(x - ρ)) x := by
      have h_sub : HasDerivAt (fun (θ : ℝ) => θ - ρ) 1 x := by
        simpa using (hasDerivAt_id x).sub_const ρ
      have h_sq : HasDerivAt (fun (θ : ℝ) => (θ - ρ) ^ 2) (2 * (x - ρ)) x := by
        have h := HasDerivAt.pow h_sub 2
        have h_eq : (fun (θ : ℝ) => (θ - ρ) ^ 2) = ((fun (θ : ℝ) => θ - ρ) ^ 2) := by ext; simp
        simpa [h_eq, mul_comm] using h
      -- -(θ-ρ)²/2 = (1/2) * (-(θ-ρ)²)
      -- derivative = (1/2) * (-(2*(x-ρ))) = -(x-ρ)
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (h_sq.neg.const_mul (1/2 : ℝ))
    -- now apply exp rule: HasDerivAt (exp ∘ g) (exp(g(x)) * g'(x))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_g.exp
  have h_tendsto : Filter.Tendsto f Filter.atBot (nhds 0) := by
    dsimp [f]
    -- exp(-(θ-ρ)²/2) → 0 as θ → -∞ because -(θ-ρ)²/2 → -∞
    have h_inner : Filter.Tendsto (fun (θ : ℝ) => -(θ - ρ) ^ 2 / 2) Filter.atBot Filter.atBot := by
      -- as θ → -∞, (θ-ρ)² → ∞, so -(θ-ρ)²/2 → -∞
      have h_sub_tendsto : Filter.Tendsto (fun (θ : ℝ) => θ - ρ) Filter.atBot Filter.atBot := by
        simpa [sub_eq_add_neg] using
          Filter.tendsto_atBot_add_const_right Filter.atBot (-ρ) (Filter.tendsto_id (x := Filter.atBot))
      -- -(θ-ρ) → ∞ as θ → -∞
      have h_neg_sub_tendsto : Filter.Tendsto (fun (θ : ℝ) => -(θ - ρ)) Filter.atBot Filter.atTop :=
        Filter.tendsto_neg_atBot_atTop.comp h_sub_tendsto
      -- (-(θ-ρ))² → ∞ as θ → -∞
      have h_sq_tendsto : Filter.Tendsto (fun (θ : ℝ) => (-(θ - ρ)) ^ 2) Filter.atBot Filter.atTop :=
        (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h_neg_sub_tendsto
      -- (θ-ρ)² = (-(θ-ρ))², so (θ-ρ)² → ∞
      have h_sq_tendsto' : Filter.Tendsto (fun (θ : ℝ) => (θ - ρ) ^ 2) Filter.atBot Filter.atTop := by
        -- h_sq_tendsto has (-(θ-ρ))² which simplifies to (ρ-θ)²
        -- but we need (θ-ρ)², and (ρ-θ)² = (θ-ρ)²
        simpa [sq, show ∀ (a b : ℝ), (a - b) ^ 2 = (b - a) ^ 2 by intro a b; ring] using h_sq_tendsto
      -- -(θ-ρ)² → -∞
      have h_neg_sq_tendsto : Filter.Tendsto (fun (θ : ℝ) => -(θ - ρ) ^ 2) Filter.atBot Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot.comp h_sq_tendsto'
      -- -(θ-ρ)²/2 = (-(θ-ρ)²) * (1/2) → -∞
      simpa [div_eq_mul_inv] using
        h_neg_sq_tendsto.atBot_mul_const (by norm_num : (0 : ℝ) < 1/2)
    -- exp(-∞) = 0
    exact Real.tendsto_exp_atBot.comp h_inner
  -- integral equality: ∫_{Iic 1} f' = f(1) - 0 = exp(-(1-ρ)²/2) = exp(-(ρ-1)²/2)
  have h_int_eq : ∫ θ in Iic (1 : ℝ), f' θ = exp (-(ρ - 1) ^ 2 / 2) := by
    have := integral_Iic_of_hasDerivAt_of_tendsto h_cont h_deriv h_int_f' h_tendsto
    -- this gives ∫ f' = f(1) - 0 = exp(-(1-ρ)²/2)
    -- and (1-ρ)² = (ρ-1)²
    rw [this]
    dsimp [f]
    ring_nf
  -- now apply setIntegral_mono_on
  have h_int_div : IntegrableOn (fun θ => f' θ / (ρ - 1)) (Iic (1 : ℝ)) := by
    -- f' is integrable, so dividing by constant preserves integrability
    exact h_int_f'.div_const (ρ - 1)
  calc
    ∫ θ in Iic (1 : ℝ), f θ ≤ ∫ θ in Iic (1 : ℝ), f' θ / (ρ - 1) :=
      setIntegral_mono_on (hf := h_int_f) (hg := h_int_div) hmeas hineq
    _ = (∫ θ in Iic (1 : ℝ), f' θ) / (ρ - 1) := by
      rw [integral_div (ρ - 1) f']
    _ = exp (-(ρ - 1) ^ 2 / 2) / (ρ - 1) := by rw [h_int_eq]

/-- `Z = ∫_1^∞ γ ≥ √(2π)/2 + ∫_0^1 e^{-u²/2}` for `ρ ≥ 2`. -/
theorem Z_ge {ρ : ℝ} (hρ : 2 ≤ ρ) :
    √(2 * π) / 2 + ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) ≤ ∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2) := by
  have hRHS : ∫ θ in Set.Ioi 1, exp (-(θ - ρ) ^ 2 / 2) = ∫ u in Set.Ioi (1 - ρ), exp (-u ^ 2 / 2) := by
    have h_indicator (x : ℝ) : (Set.Ioi 1).indicator (fun θ => exp (-(θ - ρ) ^ 2 / 2)) (x + ρ) =
        (Set.Ioi (1 - ρ)).indicator (fun u => exp (-u ^ 2 / 2)) x := by
      dsimp [Set.indicator]
      by_cases h : 1 < x + ρ
      · have h' : 1 - ρ < x := by linarith
        simp [h, h']
      · have h' : ¬ (1 - ρ < x) := by linarith
        simp [h, h']
    calc
      ∫ θ in Set.Ioi 1, exp (-(θ - ρ) ^ 2 / 2) = ∫ θ, (Set.Ioi 1).indicator (fun θ => exp (-(θ - ρ) ^ 2 / 2)) θ := by
        rw [integral_indicator measurableSet_Ioi]
      _ = ∫ u, (Set.Ioi 1).indicator (fun θ => exp (-(θ - ρ) ^ 2 / 2)) (u + ρ) := by
        rw [integral_add_right_eq_self]
      _ = ∫ u, (Set.Ioi (1 - ρ)).indicator (fun u => exp (-u ^ 2 / 2)) u := by
        apply integral_congr_ae
        filter_upwards with u
        exact h_indicator u
      _ = ∫ u in Set.Ioi (1 - ρ), exp (-u ^ 2 / 2) := by
        rw [integral_indicator measurableSet_Ioi]
  rw [hRHS]
  have h_int : IntegrableOn (fun u => exp (-u ^ 2 / 2)) (Ioi (1 - ρ)) := by
    have h_int' : Integrable (fun u => exp (-u ^ 2 / 2)) := by
      have : (fun u => exp (-u ^ 2 / 2)) = (fun u => exp (-(1/2 : ℝ) * u ^ 2)) := by
        ext u; ring_nf
      rw [this]
      exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    exact h_int'.integrableOn
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 - ρ))] (fun u => exp (-u ^ 2 / 2)) := by
    filter_upwards with u
    positivity
  have h_le : Ioi (-1 : ℝ) ≤ᵐ[volume] Ioi (1 - ρ) := by
    filter_upwards with x hx
    have hx' : -1 < x := hx
    have : 1 - ρ ≤ -1 := by linarith
    have hx'' : 1 - ρ < x := by linarith
    exact hx''
  have h_mono : ∫ u in Ioi (-1 : ℝ), exp (-u ^ 2 / 2) ≤ ∫ u in Ioi (1 - ρ), exp (-u ^ 2 / 2) :=
    setIntegral_mono_set h_int h_nonneg h_le
  have h_split : ∫ u in Ioi (-1 : ℝ), exp (-u ^ 2 / 2) = √(2 * π) / 2 + ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) := by
    have h_split' : Ioi (-1 : ℝ) = Ioc (-1 : ℝ) 0 ∪ Ioi 0 := by
      ext x; constructor
      · intro hx
        have hx' : -1 < x := hx
        by_cases hx0 : x ≤ 0
        · exact Or.inl ⟨hx', hx0⟩
        · have hx0' : 0 < x := by linarith
          exact Or.inr hx0'
      · intro hx
        rcases hx with (⟨hxl, hxr⟩ | hxr)
        · exact hxl
        · show -1 < x
          have hxr' : 0 < x := hxr
          linarith
    have h_disjoint : Disjoint (Ioc (-1 : ℝ) 0) (Ioi 0) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext x; constructor
      · intro hx
        exfalso
        rcases hx with ⟨⟨hx1, hx2⟩, hx3⟩
        have hx3' : 0 < x := hx3
        linarith
      · intro hx
        exfalso
        exact hx.elim
    have h_meas1 : MeasurableSet (Ioc (-1 : ℝ) 0) := measurableSet_Ioc
    have h_meas2 : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
    have h_int' : Integrable (fun u => exp (-u ^ 2 / 2)) := by
      have : (fun u => exp (-u ^ 2 / 2)) = (fun u => exp (-(1/2 : ℝ) * u ^ 2)) := by
        ext u; ring_nf
      rw [this]
      exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    have h_int1 : IntegrableOn (fun u => exp (-u ^ 2 / 2)) (Ioc (-1 : ℝ) 0) :=
      h_int'.integrableOn
    have h_int2 : IntegrableOn (fun u => exp (-u ^ 2 / 2)) (Ioi (0 : ℝ)) :=
      h_int'.integrableOn
    rw [h_split', setIntegral_union h_disjoint h_meas2 h_int1 h_int2]
    have h_Ioi : ∫ u in Ioi (0 : ℝ), exp (-u ^ 2 / 2) = √(2 * π) / 2 := by
      have h_eq : ∀ᵐ u ∂volume, u ∈ Ioi (0 : ℝ) → exp (-u ^ 2 / 2) = exp (-(1/2 : ℝ) * u ^ 2) := by
        filter_upwards with u hu
        ring_nf
      calc
        ∫ u in Ioi (0 : ℝ), exp (-u ^ 2 / 2) = ∫ u in Ioi (0 : ℝ), exp (-(1/2 : ℝ) * u ^ 2) := by
          rw [setIntegral_congr_ae measurableSet_Ioi h_eq]
        _ = √(π / (1/2 : ℝ)) / 2 := by rw [integral_gaussian_Ioi (1/2 : ℝ)]
        _ = √(2 * π) / 2 := by ring_nf
    have h_Ioc : ∫ u in Ioc (-1 : ℝ) 0, exp (-u ^ 2 / 2) = ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) := by
      calc
        ∫ u in Ioc (-1 : ℝ) 0, exp (-u ^ 2 / 2) = ∫ u in (-1 : ℝ)..(0 : ℝ), exp (-u ^ 2 / 2) := by
          rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
        _ = ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) := by
          calc
            ∫ u in (-1 : ℝ)..(0 : ℝ), exp (-u ^ 2 / 2) = ∫ u in (-1 : ℝ)..(0 : ℝ), exp (-( -u) ^ 2 / 2) := by
              refine intervalIntegral.integral_congr (fun u hu => ?_)
              simp
            _ = ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) := by
              rw [intervalIntegral.integral_comp_neg (fun x => exp (-x ^ 2 / 2))]
              ring_nf
    rw [h_Ioi, h_Ioc]
    ring
  calc
    √(2 * π) / 2 + ∫ u in (0 : ℝ)..1, exp (-u ^ 2 / 2) = ∫ u in Ioi (-1 : ℝ), exp (-u ^ 2 / 2) := by rw [h_split]
    _ ≤ ∫ u in Ioi (1 - ρ), exp (-u ^ 2 / 2) := h_mono

/-! ### The integrals of the terminal condition -/

/-- `e^{ρ²/2} ∫_1^∞ γ/θ ≤ Γ(ρ)`: the paper, proof of Lemma 3.4, first display. -/
theorem Gam_ge_int (ρ : ℝ) :
    exp (ρ ^ 2 / 2) * ∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2) / θ ≤ Gam ρ := by
  -- pull the constant factor inside the integral
  rw [← integral_const_mul (exp (ρ ^ 2 / 2))]
  -- define the two integrands
  set f := fun (θ : ℝ) => exp (ρ ^ 2 / 2) * (exp (-(θ - ρ) ^ 2 / 2) / θ) with hf
  set g := fun (θ : ℝ) => 2 * cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3)) with hg
  -- pointwise inequality for θ > 1
  have h_pointwise : ∀ θ ∈ Ioi (1 : ℝ), f θ ≤ g θ := by
    intro θ hθ
    have hθ_one : 1 < θ := hθ
    unfold f g
    -- algebraic identity: exp(ρ²/2) * exp(-(θ-ρ)²/2) = exp(θρ) * exp(-θ²/2)
    have h_exp_eq : exp (ρ ^ 2 / 2) * exp (-(θ - ρ) ^ 2 / 2) = exp (θ * ρ) * exp (-θ ^ 2 / 2) := by
      calc
        exp (ρ ^ 2 / 2) * exp (-(θ - ρ) ^ 2 / 2) = exp (ρ ^ 2 / 2 + (-(θ - ρ) ^ 2 / 2)) := by
          rw [Real.exp_add]
        _ = exp ((ρ ^ 2 - (θ - ρ) ^ 2) / 2) := by ring_nf
        _ = exp ((ρ ^ 2 - (θ ^ 2 - 2 * θ * ρ + ρ ^ 2)) / 2) := by ring_nf
        _ = exp ((2 * θ * ρ - θ ^ 2) / 2) := by ring_nf
        _ = exp (θ * ρ - θ ^ 2 / 2) := by ring_nf
        _ = exp (θ * ρ + (-θ ^ 2 / 2)) := by ring_nf
        _ = exp (θ * ρ) * exp (-θ ^ 2 / 2) := by rw [Real.exp_add]
    -- using Real.cosh_eq: 2 cosh x = exp x + exp (-x) ≥ exp x
    have h_cosh_ge : exp (θ * ρ) ≤ 2 * cosh (θ * ρ) := by
      have h := Real.cosh_eq (θ * ρ)
      have h2 : 2 * cosh (θ * ρ) = exp (θ * ρ) + exp (-(θ * ρ)) := by linarith
      rw [h2]
      have h_exp_nonneg : 0 ≤ exp (-(θ * ρ)) := by positivity
      linarith
    have h_bound : exp (θ * ρ) * exp (-θ ^ 2 / 2) / θ ≤
        2 * cosh (θ * ρ) * exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := by
      have hθ_pos : 0 < θ := by linarith
      have h_nonneg_factor : 0 ≤ exp (θ * ρ) * exp (-θ ^ 2 / 2) := by positivity
      have h_nonneg_cosh : 0 ≤ 2 * cosh (θ * ρ) * exp (-θ ^ 2 / 2) := by positivity
      have h_add_nonneg : 0 ≤ 2 / θ ^ 3 := by
        have hθ3_pos : 0 < θ ^ 3 := pow_pos hθ_pos 3
        positivity
      have h1 : (exp (θ * ρ) * exp (-θ ^ 2 / 2)) * (1 / θ) ≤
          (exp (θ * ρ) * exp (-θ ^ 2 / 2)) * (1 / θ + 2 / θ ^ 3) := by
        nlinarith
      have h2 : (exp (θ * ρ) * exp (-θ ^ 2 / 2)) * (1 / θ + 2 / θ ^ 3) ≤
          (2 * cosh (θ * ρ)) * exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := by
        have h_factor_nonneg : 0 ≤ exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := by positivity
        nlinarith
      calc
        exp (θ * ρ) * exp (-θ ^ 2 / 2) / θ = (exp (θ * ρ) * exp (-θ ^ 2 / 2)) * (1 / θ) := by ring
        _ ≤ (exp (θ * ρ) * exp (-θ ^ 2 / 2)) * (1 / θ + 2 / θ ^ 3) := h1
        _ ≤ (2 * cosh (θ * ρ)) * exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := h2
        _ = 2 * cosh (θ * ρ) * exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := by ring
    calc
      exp (ρ ^ 2 / 2) * (exp (-(θ - ρ) ^ 2 / 2) / θ) =
          (exp (ρ ^ 2 / 2) * exp (-(θ - ρ) ^ 2 / 2)) / θ := by ring
      _ = (exp (θ * ρ) * exp (-θ ^ 2 / 2)) / θ := by rw [h_exp_eq]
      _ ≤ 2 * cosh (θ * ρ) * exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3) := h_bound
      _ = 2 * cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3)) := by ring
  -- integrability of f on Ioi 1
  have h_int_f : IntegrableOn f (Ioi (1 : ℝ)) := by
    -- define the dominating function h(θ) = exp(ρ²/2) * exp(-(θ-ρ)²/2)
    set h := fun (θ : ℝ) => exp (ρ ^ 2 / 2) * exp (-(θ - ρ) ^ 2 / 2) with hh
    have h_int_h : IntegrableOn h (Ioi (1 : ℝ)) := by
      -- exp(-(θ-ρ)²/2) is integrable on ℝ (it's a Gaussian)
      have h_int_gauss_all : Integrable (fun x : ℝ => exp (-(1/2 : ℝ) * x ^ 2)) volume := by
        rw [integrable_exp_neg_mul_sq_iff]
        norm_num
      -- shift by ρ
      have h_int_shifted : Integrable (fun x : ℝ => exp (-(1/2 : ℝ) * (x - ρ) ^ 2)) volume := by
        have := h_int_gauss_all.comp_add_right (-ρ)
        simpa [sub_eq_add_neg] using this
      -- note: -(1/2)*(x-ρ)² = -(x-ρ)²/2
      have h_int_shifted' : Integrable (fun x : ℝ => exp (-(x - ρ) ^ 2 / 2)) volume := by
        convert h_int_shifted using 1
        ext x; ring_nf
      -- multiply by constant and restrict
      have h_int_const : Integrable (fun x : ℝ => exp (ρ ^ 2 / 2) * exp (-(x - ρ) ^ 2 / 2)) volume :=
        h_int_shifted'.const_mul (exp (ρ ^ 2 / 2))
      exact h_int_const.integrableOn
    have h_bound_on_Ioi : ∀ θ ∈ Ioi (1 : ℝ), f θ ≤ h θ := by
      intro θ hθ
      have hθ_one : 1 < θ := hθ
      unfold f h
      have hθ_one' : 1 ≤ θ := by linarith
      have h_nonneg_a : 0 ≤ exp (-(θ - ρ) ^ 2 / 2) := by positivity
      have h_nonneg_exp : 0 ≤ exp (ρ ^ 2 / 2) := by positivity
      have h_div_le : exp (-(θ - ρ) ^ 2 / 2) / θ ≤ exp (-(θ - ρ) ^ 2 / 2) :=
        div_le_self h_nonneg_a hθ_one'
      nlinarith
    -- use Integrable.mono' on the restricted measure
    have h_int_h' : Integrable h (volume.restrict (Ioi (1 : ℝ))) := h_int_h
    have h_meas_f : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
      -- f is continuous on Ioi 1, hence AEStronglyMeasurable
      have h_cont : ContinuousOn f (Ioi (1 : ℝ)) := by
        unfold f
        have h_cont_num : ContinuousOn (fun θ : ℝ => exp (-(θ - ρ) ^ 2 / 2)) (Ioi (1 : ℝ)) := by
          refine (Real.continuous_exp.comp (by continuity)).continuousOn
        have h_cont_denom : ContinuousOn (fun θ : ℝ => θ) (Ioi (1 : ℝ)) :=
          continuous_id.continuousOn
        have h_denom_ne_zero : ∀ θ ∈ Ioi (1 : ℝ), θ ≠ 0 := by
          intro θ hθ
          have : 1 < θ := hθ
          linarith
        refine ContinuousOn.mul continuous_const.continuousOn ?_
        exact ContinuousOn.div h_cont_num h_cont_denom h_denom_ne_zero
      exact h_cont.aestronglyMeasurable measurableSet_Ioi
    have h_bound_ae : ∀ᵐ θ ∂(volume.restrict (Ioi (1 : ℝ))), ‖f θ‖ ≤ h θ := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
      have h_nonneg_f : 0 ≤ f θ := by
        unfold f
        have h_nonneg_exp : 0 ≤ exp (ρ ^ 2 / 2) := by positivity
        have h_nonneg_div : 0 ≤ exp (-(θ - ρ) ^ 2 / 2) / θ := by
          refine div_nonneg (by positivity) ?_
          have : 1 < θ := hθ
          linarith
        nlinarith
      have h_le : f θ ≤ h θ := h_bound_on_Ioi θ hθ
      -- ‖f θ‖ = |f θ| = f θ (since f θ ≥ 0)
      simpa [abs_of_nonneg h_nonneg_f] using h_le
    have h_int_f' : Integrable f (volume.restrict (Ioi (1 : ℝ))) :=
      Integrable.mono' h_int_h' h_meas_f h_bound_ae
    exact h_int_f'
  -- integrability of g on Ioi 1 (from Work.Deps)
  have h_int_g : IntegrableOn g (Ioi (1 : ℝ)) := by
    have h := Upper.integrableOn_G ρ
    have h_g_eq : (fun θ => 2 * cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))) =
        fun θ => 2 * (cosh (θ * ρ) * Upper.wt θ) := by
      ext θ
      unfold Upper.wt
      ring
    dsimp [g]
    rw [h_g_eq]
    exact h.const_mul 2
  -- measurableSet (Ioi 1)
  have h_meas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
  -- apply setIntegral_mono_on
  calc
    ∫ θ in Ioi (1 : ℝ), f θ ≤ ∫ θ in Ioi (1 : ℝ), g θ :=
      setIntegral_mono_on h_int_f h_int_g h_meas h_pointwise
    _ = ∫ θ in Ioi (1 : ℝ), (2 * cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))) := rfl
    _ = ∫ θ in Ioi (1 : ℝ), (2 * (cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3)))) := by
      refine setIntegral_congr_fun h_meas ?_
      intro θ hθ
      ring
    _ = 2 * ∫ θ in Ioi (1 : ℝ), (cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))) := by
      rw [integral_const_mul (2 : ℝ) (fun θ => cosh (θ * ρ) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))) (μ := volume.restrict (Ioi (1 : ℝ)))]
    _ = Gam ρ := rfl

/-- The tangent bound `2aZ - a²M ≤ I`, from `1/θ ≥ 2a - a²θ` for `θ > 0`. -/
theorem tangent_int (ρ a : ℝ) :
    2 * a * (∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2)) - a ^ 2 * ∫ θ in Ioi 1, θ * exp (-(θ - ρ) ^ 2 / 2) ≤
      ∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2) / θ := by
  set γ := fun (θ : ℝ) => exp (-(θ - ρ) ^ 2 / 2) with hγ
  have hγ_pos : ∀ θ, 0 < γ θ := by
    intro θ; unfold γ; exact Real.exp_pos _
  have h_meas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
  -- integrability of γ
  have h_int_γ : IntegrableOn γ (Ioi 1) := by
    have h_int : Integrable (fun x : ℝ => exp (-((1/2 : ℝ)) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    have h_int_shift : Integrable (fun θ : ℝ => exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) :=
      h_int.comp_sub_right ρ
    have h_eq : γ = fun θ : ℝ => exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2) := by
      ext θ; unfold γ; ring_nf
    rw [h_eq]
    exact h_int_shift.integrableOn
  -- integrability of θ * γ(θ)
  have h_int_θγ : IntegrableOn (fun θ => θ * γ θ) (Ioi 1) := by
    have h_int : Integrable (fun x : ℝ => x * exp (-((1/2 : ℝ)) * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    have h_int_shift : Integrable (fun θ : ℝ => (θ - ρ) * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) :=
      h_int.comp_sub_right ρ
    have h_int' : IntegrableOn (fun θ : ℝ => (θ - ρ) * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) (Ioi 1) :=
      h_int_shift.integrableOn
    have h_int_ρ : IntegrableOn (fun θ : ℝ => ρ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) (Ioi 1) := by
      have : (fun θ : ℝ => ρ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) =
          (fun θ : ℝ => ρ * γ θ) := by
        ext θ; unfold γ; ring_nf
      rw [this]
      exact h_int_γ.const_mul ρ
    have h_sum : IntegrableOn
      ((fun θ : ℝ => (θ - ρ) * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) +
       (fun θ : ℝ => ρ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2))) (Ioi 1) :=
      h_int'.add h_int_ρ
    have h_eq : ((fun θ : ℝ => (θ - ρ) * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) +
                 (fun θ : ℝ => ρ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2))) =
                (fun θ : ℝ => θ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) := by
      ext θ
      calc
        ((θ - ρ) * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2) + ρ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2))
            = ((θ - ρ) + ρ) * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2) := by ring
        _ = θ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2) := by ring
    rw [h_eq] at h_sum
    have h_eq2 : (fun θ : ℝ => θ * exp (-((1/2 : ℝ)) * (θ - ρ) ^ 2)) =
                (fun θ : ℝ => θ * γ θ) := by
      ext θ; unfold γ; ring_nf
    rw [h_eq2] at h_sum
    exact h_sum
  -- integrability of γ/θ
  have h_int_γ_div_θ : IntegrableOn (fun θ => γ θ / θ) (Ioi 1) := by
    have h_bound : ∀ᵐ θ ∂(volume.restrict (Ioi 1)), ‖γ θ / θ‖ ≤ γ θ := by
      have h_mem : (Ioi (1 : ℝ)) ∈ ae (volume.restrict (Ioi 1)) := ae_restrict_mem h_meas
      filter_upwards [h_mem] with θ hθ
      have h1 : (1 : ℝ) < θ := hθ
      have hθ_pos : 0 < θ := by linarith
      have h_one_div_le_one : 1 / θ ≤ 1 := by
        rw [div_le_one hθ_pos]
        linarith
      calc
        ‖γ θ / θ‖ = |γ θ / θ| := Real.norm_eq_abs _
        _ = |γ θ| / |θ| := abs_div _ _
        _ = γ θ / θ := by rw [abs_of_pos (hγ_pos θ), abs_of_pos hθ_pos]
        _ = γ θ * (1 / θ) := by ring
        _ ≤ γ θ * 1 := by gcongr
        _ = γ θ := by ring
    have h_meas_γ_div_θ : AEStronglyMeasurable (fun θ => γ θ / θ) (volume.restrict (Ioi 1)) := by
      have h_cont : ContinuousOn (fun θ : ℝ => γ θ / θ) (Ioi 1) := by
        unfold γ
        have h_cont_num : ContinuousOn (fun θ : ℝ => exp (-(θ - ρ) ^ 2 / 2)) (Ioi 1) := by
          refine (Real.continuous_exp.comp ?_).continuousOn
          continuity
        have h_cont_denom : ContinuousOn (fun θ : ℝ => θ) (Ioi 1) := continuous_id.continuousOn
        refine h_cont_num.div h_cont_denom ?_
        intro θ hθ
        have : 1 < θ := hθ
        linarith
      exact h_cont.aestronglyMeasurable h_meas
    have h_int_γ_restrict : Integrable γ (volume.restrict (Ioi 1)) := h_int_γ
    exact Integrable.mono' h_int_γ_restrict h_meas_γ_div_θ h_bound
  -- pointwise inequality
  have h_pointwise : ∀ θ ∈ Ioi (1 : ℝ), (2 * a - a ^ 2 * θ) * γ θ ≤ γ θ / θ := by
    intro θ hθ
    have h1 : (1 : ℝ) < θ := hθ
    have hθ_pos : 0 < θ := by linarith
    have h_ineq : 2 * a - a ^ 2 * θ ≤ 1 / θ := by
      have h_sq_nonneg : 0 ≤ (1 - a * θ) ^ 2 := by positivity
      have h_eq : θ * (1 / θ - (2 * a - a ^ 2 * θ)) = (1 - a * θ) ^ 2 := by
        field_simp [hθ_pos.ne']
        ring
      have h_nonneg_prod : 0 ≤ θ * (1 / θ - (2 * a - a ^ 2 * θ)) := by rw [h_eq]; exact h_sq_nonneg
      have h_nonneg_diff : 0 ≤ 1 / θ - (2 * a - a ^ 2 * θ) :=
        nonneg_of_mul_nonneg_right h_nonneg_prod hθ_pos
      linarith
    calc
      (2 * a - a ^ 2 * θ) * γ θ ≤ (1 / θ) * γ θ := by gcongr
      _ = γ θ / θ := by ring
  -- apply setIntegral_mono_on
  have h_int_left : IntegrableOn (fun θ => (2 * a - a ^ 2 * θ) * γ θ) (Ioi 1) := by
    have h_eq : (fun θ => (2 * a - a ^ 2 * θ) * γ θ) =
               (fun θ => 2 * a * γ θ) - (fun θ => a ^ 2 * (θ * γ θ)) := by
      ext θ
      calc
        (2 * a - a ^ 2 * θ) * γ θ = 2 * a * γ θ - a ^ 2 * θ * γ θ := by ring
        _ = (2 * a * γ θ) - (a ^ 2 * (θ * γ θ)) := by ring
    rw [h_eq]
    exact (h_int_γ.const_mul (2 * a)).sub (h_int_θγ.const_mul (a ^ 2))
  have h_int_ineq := setIntegral_mono_on h_int_left h_int_γ_div_θ h_meas h_pointwise
  -- split the left integral
  have h_split : (∫ θ in Ioi 1, (2 * a - a ^ 2 * θ) * γ θ) =
      2 * a * (∫ θ in Ioi 1, γ θ) - a ^ 2 * (∫ θ in Ioi 1, θ * γ θ) := by
    calc
      (∫ θ in Ioi 1, (2 * a - a ^ 2 * θ) * γ θ) =
          (∫ θ in Ioi 1, (2 * a * γ θ - a ^ 2 * (θ * γ θ))) := by
        refine setIntegral_congr_fun h_meas ?_
        intro θ hθ
        ring
      _ = (∫ θ in Ioi 1, 2 * a * γ θ) - (∫ θ in Ioi 1, a ^ 2 * (θ * γ θ)) := by
        rw [integral_sub]
        · exact (h_int_γ.const_mul (2 * a))
        · exact (h_int_θγ.const_mul (a ^ 2))
      _ = (2 * a * (∫ θ in Ioi 1, γ θ)) - (a ^ 2 * (∫ θ in Ioi 1, θ * γ θ)) := by
        simp [integral_const_mul]
  rw [h_split] at h_int_ineq
  exact h_int_ineq

/-- `γ(θ) = e^{-(θ-ρ)²/2}` is integrable on `ℝ`. -/
theorem integrable_gauss_shift (ρ : ℝ) : Integrable (fun θ : ℝ => exp (-(θ - ρ) ^ 2 / 2)) := by
  have h : Integrable (fun x : ℝ => exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have e : (fun θ : ℝ => exp (-(θ - ρ) ^ 2 / 2)) =
      fun θ => (fun x : ℝ => exp (-(1 / 2 : ℝ) * x ^ 2)) (θ - ρ) := by
    funext θ; ring_nf
  rw [e]
  exact h.comp_sub_right ρ

/-- `(θ - ρ) γ(θ)` is integrable on `ℝ`. -/
theorem integrable_gauss_shift_mul (ρ : ℝ) :
    Integrable (fun θ : ℝ => (θ - ρ) * exp (-(θ - ρ) ^ 2 / 2)) := by
  have h : Integrable (fun x : ℝ => x * exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    integrable_mul_exp_neg_mul_sq (by norm_num)
  have e : (fun θ : ℝ => (θ - ρ) * exp (-(θ - ρ) ^ 2 / 2)) =
      fun θ => (fun x : ℝ => x * exp (-(1 / 2 : ℝ) * x ^ 2)) (θ - ρ) := by
    funext θ; ring_nf
  rw [e]
  exact h.comp_sub_right ρ

/-- `∫_1^∞ (θ - ρ) γ = e^{-(1-ρ)²/2}`. -/
theorem integral_shift_mul_gauss (ρ : ℝ) :
    ∫ θ in Ioi 1, (θ - ρ) * exp (-(θ - ρ) ^ 2 / 2) = exp (-(1 - ρ) ^ 2 / 2) := by
  have hderiv : ∀ θ ∈ Ici (1 : ℝ), HasDerivAt (fun θ : ℝ => -exp (-(θ - ρ) ^ 2 / 2))
      ((θ - ρ) * exp (-(θ - ρ) ^ 2 / 2)) θ := by
    intro θ _
    have h := ((((hasDerivAt_id' θ).sub_const ρ).pow 2).neg.div_const 2).exp.neg
    convert h using 1
    simp only [Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat]
    ring_nf
  have h0 : Tendsto (fun θ : ℝ => θ - ρ) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-ρ) tendsto_id
  have h1 : Tendsto (fun θ : ℝ => (θ - ρ) ^ 2 / 2) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp h0).atTop_div_const (by norm_num)
  have h2 : Tendsto (fun θ : ℝ => exp (-(θ - ρ) ^ 2 / 2)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    refine this.congr fun θ => ?_
    simp only [Function.comp, neg_div]
  have h3 : Tendsto (fun θ : ℝ => -exp (-(θ - ρ) ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using h2.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrable_gauss_shift_mul ρ).integrableOn h3]
  simp

/-- `M = ∫_1^∞ θγ = ρ Z + e^{-(1-ρ)²/2}`. -/
theorem M_eq (ρ : ℝ) :
    ∫ θ in Ioi 1, θ * exp (-(θ - ρ) ^ 2 / 2) =
      ρ * (∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2)) + exp (-(1 - ρ) ^ 2 / 2) := by
  have hg : IntegrableOn (fun θ : ℝ => ρ * exp (-(θ - ρ) ^ 2 / 2)) (Ioi 1) :=
    ((integrable_gauss_shift ρ).const_mul ρ).integrableOn
  have hd : IntegrableOn (fun θ : ℝ => (θ - ρ) * exp (-(θ - ρ) ^ 2 / 2)) (Ioi 1) :=
    (integrable_gauss_shift_mul ρ).integrableOn
  have e : (fun θ : ℝ => θ * exp (-(θ - ρ) ^ 2 / 2)) =
      fun θ => ρ * exp (-(θ - ρ) ^ 2 / 2) + (θ - ρ) * exp (-(θ - ρ) ^ 2 / 2) := by
    funext θ; ring
  rw [e, integral_add hg hd, integral_const_mul, integral_shift_mul_gauss]

/-! ### Lemma 3.4 -/

/-- The real part of Lemma 3.4: from the identities and bounds of `Z`, `M`, the lower tail `t`
and the tangent bound of `I`, `√(2π) ≤ (ρ + 1) I`. -/
theorem terminal_alg {ρ Z M I t e : ℝ} (hρ : 2 ≤ ρ) (hMe : M = ρ * Z + e)
    (hsum : t + Z = √(2 * π)) (htle : t ≤ e / (ρ - 1)) (ht0 : 0 ≤ t)
    (hA : √(2 * π) / 2 + 0.8556 ≤ Z) (he0 : 0 ≤ e) (heE : e ≤ 0.6065306598)
    (htan : ∀ a, 2 * a * Z - a ^ 2 * M ≤ I) : √(2 * π) ≤ (ρ + 1) * I := by
  have hs := sqrt_two_pi_bounds
  have hZpos : 0 < Z := by linarith
  have hmills := mills_num he0 heE hA
  have hm2 : 2 * e * Z + √(2 * π) * e < Z ^ 2 := by
    have h := mul_lt_mul_of_pos_right hmills (by positivity : 0 < Z ^ 2)
    have e1 : (2 * e / Z + √(2 * π) * e / Z ^ 2) * Z ^ 2 = 2 * e * Z + √(2 * π) * e := by
      field_simp
    linarith
  have hρt : ρ * t ≤ 2 * e := by
    have hρ1 : 0 < ρ - 1 := by linarith
    have h1 : t * (ρ - 1) ≤ e := (le_div_iff₀ hρ1).1 htle
    nlinarith
  have hkey : √(2 * π) * M ≤ (ρ + 1) * Z ^ 2 := by
    rw [hMe, ← hsum]
    nlinarith [mul_le_mul_of_nonneg_right hρt hZpos.le]
  have hMpos : 0 < M := by rw [hMe]; nlinarith
  have hI : Z ^ 2 / M ≤ I := by
    have h := htan (Z / M)
    have e1 : 2 * (Z / M) * Z - (Z / M) ^ 2 * M = Z ^ 2 / M := by
      field_simp
      ring
    linarith
  have h1 : √(2 * π) ≤ (ρ + 1) * (Z ^ 2 / M) := by
    rw [← mul_div_assoc, le_div_iff₀ hMpos]
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left hI (by linarith))

/-- **Lemma 3.4**, the inequality: for `ρ ≥ 2`, `√(2π) e^{ρ²/2} ≤ (ρ + 1) Γ(ρ)`. -/
theorem terminal_ineq {ρ : ℝ} (hρ : 2 ≤ ρ) : √(2 * π) * exp (ρ ^ 2 / 2) ≤ (ρ + 1) * Gam ρ := by
  have hMe := M_eq ρ
  rw [show (1 - ρ) ^ 2 = (ρ - 1) ^ 2 by ring] at hMe
  have heE : exp (-(ρ - 1) ^ 2 / 2) ≤ 0.6065306598 := by
    have : exp (-(ρ - 1) ^ 2 / 2) ≤ exp (-1 / 2) := exp_le_exp.2 (by nlinarith)
    linarith [exp_neg_half_bounds.2]
  have ht0 : 0 ≤ ∫ θ in Iic 1, exp (-(θ - ρ) ^ 2 / 2) :=
    setIntegral_nonneg measurableSet_Iic fun θ _ => (exp_pos _).le
  have h := terminal_alg hρ hMe (Z_add_lower ρ) (lower_tail_le (by linarith)) ht0
    (by linarith [Z_ge hρ, int01_ge]) (exp_pos _).le heE (tangent_int ρ)
  have hG := Gam_ge_int ρ
  calc √(2 * π) * exp (ρ ^ 2 / 2)
      ≤ (ρ + 1) * (∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2) / θ) * exp (ρ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h (exp_pos _).le
    _ = (ρ + 1) * (exp (ρ ^ 2 / 2) * ∫ θ in Ioi 1, exp (-(θ - ρ) ^ 2 / 2) / θ) := by ring
    _ ≤ (ρ + 1) * Gam ρ := mul_le_mul_of_nonneg_left hG (by linarith)

/-- `Γ ≥ 0`. -/
theorem Gam_nonneg (ρ : ℝ) : 0 ≤ Gam ρ := by
  refine le_trans ?_ (Gam_ge_int ρ)
  refine mul_nonneg (exp_pos _).le (setIntegral_nonneg measurableSet_Ioi fun θ hθ => ?_)
  exact div_nonneg (exp_pos _).le (le_trans zero_le_one (le_of_lt hθ))

/-- `Γ` is even. -/
theorem Gam_neg (ρ : ℝ) : Gam (-ρ) = Gam ρ := by
  simp only [Gam, mul_neg, cosh_neg]

theorem Cst_pos (T : ℕ) : 0 < Cst T := by
  unfold Cst
  positivity

/-- **Lemma 3.4**, the consequence: for `ρ² ≤ T`, `Φ₀(ρ) = 2 log(C (λ₀ + Γ(ρ))) ≥ ρ²`. -/
theorem terminal_sharp {T : ℕ} {ρ : ℝ} (hρ : ρ ^ 2 ≤ T) :
    ρ ^ 2 ≤ 2 * log (Cst T * (lam0 T + Gam ρ)) := by
  have hC := Cst_pos T
  have hG := Gam_nonneg ρ
  have heq : Cst T * (lam0 T + Gam ρ) = exp 2 + Cst T * Gam ρ := by
    unfold lam0; field_simp
  have hpos : 0 < Cst T * (lam0 T + Gam ρ) := by rw [heq]; positivity
  suffices h : exp (ρ ^ 2 / 2) ≤ Cst T * (lam0 T + Gam ρ) by
    have := (Real.le_log_iff_exp_le hpos).2 h
    linarith
  rw [heq]
  rcases le_or_gt |ρ| 2 with hr | hr
  · have h1 : ρ ^ 2 / 2 ≤ 2 := by
      have : ρ ^ 2 ≤ 4 := by
        have := sq_abs ρ ▸ pow_le_pow_left₀ (abs_nonneg ρ) hr 2
        linarith
      linarith
    have := exp_le_exp.2 h1
    have : 0 ≤ Cst T * Gam ρ := by positivity
    linarith
  · have hGa : Gam |ρ| = Gam ρ := by
      rcases abs_choice ρ with h | h <;> rw [h]
      exact Gam_neg ρ
    have hti := terminal_ineq hr.le
    rw [hGa, sq_abs] at hti
    have hrT : |ρ| ≤ √(T : ℝ) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hρ
    have hs : 0 < √(2 * π) := by positivity
    have h2 : √(2 * π) * exp (ρ ^ 2 / 2) ≤ (√(T : ℝ) + 1) * Gam ρ :=
      hti.trans (mul_le_mul_of_nonneg_right (by linarith) hG)
    have h3 : exp (ρ ^ 2 / 2) ≤ Cst T * Gam ρ := by
      unfold Cst
      rw [div_mul_eq_mul_div, le_div_iff₀ hs]
      linarith
    linarith [exp_pos 2]

end RegretKappa.UpperSharp
