import RegretKappa.LowerSharp.VanTrees
import RegretKappa.LowerSharp.Statement

/-!
# Sharp lower bound: the prior

The paper, Lemma B.6 (the prior): the density `f_Z(z) = (1/2) cos²(π z/4)` on `[-2, 2]` is
`g²` with `g(z) = cos(π z/4)/√2` (`gP`), `g' = -(π/4) sin(π z/4)/√2` (`gP'`), `g(±2) = 0`; its
mass is `1` (`integral_gP_sq`), its Fisher information `∫ 4 g'² = π²/4 = J` (`integral_gP_deriv_sq`)
and its second moment `∫ z² g² = 4/3 - 8/π²` (`integral_sq_gP_sq`). `vanTreesP` is the van Trees
inequality of `LowerSharp/VanTrees.lean` for this prior.
-/

namespace RegretKappa.LowerSharp

open Real MeasureTheory Set RegretKappa.Lower

/-- `g(z) = cos(π z/4)/√2`; the prior density is `g²`. -/
noncomputable def gP (z : ℝ) : ℝ := cos (π * z / 4) / √2

/-- The derivative of `gP`. -/
noncomputable def gP' (z : ℝ) : ℝ := -(π / 4) * sin (π * z / 4) / √2

@[fun_prop]
theorem continuous_gP : Continuous gP := by unfold gP; fun_prop

@[fun_prop]
theorem continuous_gP' : Continuous gP' := by unfold gP'; fun_prop

theorem hasDerivAt_gP (z : ℝ) : HasDerivAt gP (gP' z) z := by
  have h := ((hasDerivAt_id z).const_mul π).div_const 4
  have h2 := (h.cos).div_const (√2)
  convert h2 using 1
  · funext x; simp [gP]
  · simp [gP']; ring

theorem gP_two : gP 2 = 0 := by
  rw [gP, show π * 2 / 4 = π / 2 by ring, Real.cos_pi_div_two, zero_div]

theorem gP_neg_two : gP (-2) = 0 := by
  rw [gP, show π * -2 / 4 = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, zero_div]

theorem gP_sq (z : ℝ) : gP z ^ 2 = cos (π * z / 4) ^ 2 / 2 := by
  rw [gP, div_pow, Real.sq_sqrt (by norm_num)]

/-- The prior has mass `1`. -/
theorem integral_gP_sq : ∫ z in (-2 : ℝ)..2, gP z ^ 2 = 1 := by
  have hgP_sq (z : ℝ) : gP z ^ 2 = (1 + cos (π * z / 2)) / 4 := by
    dsimp [gP]
    have hcos_sq := Real.cos_sq (π * z / 4)
    calc
      (cos (π * z / 4) / √2) ^ 2 = cos (π * z / 4) ^ 2 / (√2) ^ 2 := by ring
      _ = cos (π * z / 4) ^ 2 / 2 := by norm_num
      _ = ((1 / 2 + cos (2 * (π * z / 4)) / 2)) / 2 := by rw [hcos_sq]
      _ = (1 + cos (π * z / 2)) / 4 := by ring_nf
  have h_int_cos : ∫ z in (-2 : ℝ)..2, cos (π * z / 2) = 0 := by
    have hπ_ne_zero : π / 2 ≠ 0 := by
      exact div_ne_zero (by positivity) (by norm_num)
    calc
      ∫ z in (-2 : ℝ)..2, cos (π * z / 2) = ∫ z in (-2 : ℝ)..2, cos ((π / 2) * z) := by
        ring_nf
      _ = ((π / 2)⁻¹ : ℝ) • ∫ z in ((π / 2) * (-2 : ℝ))..((π / 2) * (2 : ℝ)), cos z := by
        rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) (by
          exact div_ne_zero (by positivity) (by norm_num))]
      _ = (2 / π) • ∫ z in (-(π))..(π), cos z := by
        ring_nf
      _ = (2 / π) • (sin π - sin (-(π))) := by rw [integral_cos]
      _ = (2 / π) • (0 - 0) := by simp [Real.sin_pi]
      _ = 0 := by simp
  have h_int_const : IntervalIntegrable (fun (_ : ℝ) => (1 : ℝ)) MeasureTheory.volume (-2) 2 :=
    intervalIntegrable_const
  have h_int_cos_int : IntervalIntegrable (fun (z : ℝ) => cos (π * z / 2)) MeasureTheory.volume (-2) 2 := by
    have h_cont : Continuous (fun (z : ℝ) => cos (π * z / 2)) := by continuity
    exact h_cont.intervalIntegrable _ _
  calc
    ∫ z in (-2 : ℝ)..2, gP z ^ 2 = ∫ z in (-2 : ℝ)..2, (1 + cos (π * z / 2)) / 4 := by
      refine intervalIntegral.integral_congr (fun z _ => ?_)
      rw [hgP_sq z]
    _ = (∫ z in (-2 : ℝ)..2, (1 + cos (π * z / 2))) / 4 := by
      rw [intervalIntegral.integral_div]
    _ = ((∫ z in (-2 : ℝ)..2, (1 : ℝ)) + (∫ z in (-2 : ℝ)..2, cos (π * z / 2))) / 4 := by
      rw [intervalIntegral.integral_add h_int_const h_int_cos_int]
    _ = (∫ z in (-2 : ℝ)..2, (1 : ℝ)) / 4 + (∫ z in (-2 : ℝ)..2, cos (π * z / 2)) / 4 := by ring
    _ = ((2 - (-2 : ℝ)) : ℝ) / 4 + (∫ z in (-2 : ℝ)..2, cos (π * z / 2)) / 4 := by
      simp [intervalIntegral.integral_const]
    _ = (4 : ℝ) / 4 + (∫ z in (-2 : ℝ)..2, cos (π * z / 2)) / 4 := by ring
    _ = 1 + (∫ z in (-2 : ℝ)..2, cos (π * z / 2)) / 4 := by norm_num
    _ = 1 + 0 / 4 := by rw [h_int_cos]
    _ = 1 := by norm_num

/-- The Fisher information of the prior: `∫ 4 g'² = π²/4`. -/
theorem integral_gP_deriv_sq : ∫ z in (-2 : ℝ)..2, 4 * gP' z ^ 2 = Jc := by
  have hJc : Jc = π ^ 2 / 4 := rfl
  rw [hJc]
  have h_integrand (z : ℝ) : 4 * gP' z ^ 2 = (π ^ 2 / 16) * (1 - Real.cos (π * z / 2)) := by
    dsimp [gP']
    have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    calc
      4 * ((-(π / 4) * Real.sin (π * z / 4) / Real.sqrt 2) ^ 2)
          = 4 * ((-(π / 4) * Real.sin (π * z / 4)) ^ 2 / (Real.sqrt 2) ^ 2) := by ring
      _ = 4 * ((-(π / 4) * Real.sin (π * z / 4)) ^ 2 / 2) := by rw [hsq2]
      _ = 4 * (((π / 4) ^ 2) * (Real.sin (π * z / 4)) ^ 2 / 2) := by ring
      _ = 4 * ((π ^ 2 / 16) * (Real.sin (π * z / 4)) ^ 2 / 2) := by ring
      _ = (π ^ 2 / 8) * (Real.sin (π * z / 4)) ^ 2 := by ring
      _ = (π ^ 2 / 8) * (1 / 2 - Real.cos (2 * (π * z / 4)) / 2) := by rw [Real.sin_sq_eq_half_sub]
      _ = (π ^ 2 / 8) * (1 / 2 - Real.cos (π * z / 2) / 2) := by ring_nf
      _ = (π ^ 2 / 16) * (1 - Real.cos (π * z / 2)) := by ring
  rw [intervalIntegral.integral_congr (fun z hz => h_integrand z)]
  set F : ℝ → ℝ := fun z => (π ^ 2 / 16) * z - (π / 8) * Real.sin (π * z / 2) with hF
  have hFderiv (z : ℝ) : HasDerivAt F ((π ^ 2 / 16) * (1 - Real.cos (π * z / 2))) z := by
    dsimp [F]
    have hf : HasDerivAt (fun z => (π ^ 2 / 16) * z) (π ^ 2 / 16) z :=
      hasDerivAt_const_mul (π ^ 2 / 16)
    have hg : HasDerivAt (fun z => (π / 8) * Real.sin (π * z / 2)) ((π ^ 2 / 16) * Real.cos (π * z / 2)) z := by
      have h_inner : HasDerivAt (fun z => π * z / 2) (π / 2) z := by
        have h_mul : HasDerivAt (fun z => π * z) π z := hasDerivAt_const_mul π
        simpa [div_eq_mul_inv] using h_mul.mul_const (1/2 : ℝ)
      have h_sin_inner : HasDerivAt (fun z => Real.sin (π * z / 2)) (Real.cos (π * z / 2) * (π / 2)) z :=
        (Real.hasDerivAt_sin _).comp z h_inner
      have hg' : HasDerivAt (fun z => (π / 8) * Real.sin (π * z / 2)) ((π / 8) * (Real.cos (π * z / 2) * (π / 2))) z :=
        HasDerivAt.const_mul (π / 8) h_sin_inner
      have hsimp : (π / 8) * (Real.cos (π * z / 2) * (π / 2)) = (π ^ 2 / 16) * Real.cos (π * z / 2) := by ring
      simpa [hsimp] using hg'
    have hF' : HasDerivAt (fun z => (π ^ 2 / 16) * z - (π / 8) * Real.sin (π * z / 2))
        ((π ^ 2 / 16) - ((π ^ 2 / 16) * Real.cos (π * z / 2))) z :=
      HasDerivAt.sub hf hg
    simpa [mul_sub] using hF'
  have hFderiv_on : ∀ z ∈ Set.uIcc (-2 : ℝ) 2, HasDerivAt F ((π ^ 2 / 16) * (1 - Real.cos (π * z / 2))) z :=
    fun z _ => hFderiv z
  have h_cont : Continuous (fun z => (π ^ 2 / 16) * (1 - Real.cos (π * z / 2))) := by
    have h_sub : Continuous (fun z : ℝ => 1 - Real.cos (π * z / 2)) :=
      Continuous.sub continuous_const (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2))
    exact continuous_const.mul h_sub
  have h_int : IntervalIntegrable (fun z => (π ^ 2 / 16) * (1 - Real.cos (π * z / 2))) MeasureTheory.volume (-2 : ℝ) 2 :=
    h_cont.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv_on h_int]
  dsimp [F]
  have hsin2 : Real.sin (π * (2 : ℝ) / 2) = 0 := by
    calc
      Real.sin (π * (2 : ℝ) / 2) = Real.sin π := by ring_nf
      _ = 0 := Real.sin_pi
  have hsinneg2 : Real.sin (π * (-2 : ℝ) / 2) = 0 := by
    calc
      Real.sin (π * (-2 : ℝ) / 2) = Real.sin (-π) := by ring_nf
      _ = 0 := by simp
  calc
    ((π ^ 2 / 16) * (2 : ℝ) - (π / 8) * Real.sin (π * (2 : ℝ) / 2)) -
      ((π ^ 2 / 16) * (-2 : ℝ) - (π / 8) * Real.sin (π * (-2 : ℝ) / 2))
        = ((π ^ 2 / 16) * 2 - (π / 8) * 0) - ((π ^ 2 / 16) * (-2) - (π / 8) * 0) := by
      rw [hsin2, hsinneg2]
    _ = ((π ^ 2 / 8) - 0) - (-(π ^ 2 / 8) - 0) := by ring
    _ = π ^ 2 / 4 := by ring

/-- The second moment of the prior: `∫ z² g² = 4/3 - 8/π²`. -/
theorem integral_sq_gP_sq : ∫ z in (-2 : ℝ)..2, z ^ 2 * gP z ^ 2 = 4 / 3 - 8 / π ^ 2 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  -- Rewrite gP(z)^2 using the cosine double-angle formula
  have hgP_sq (z : ℝ) : gP z ^ 2 = 1/4 + Real.cos (π * z / 2) / 4 := by
    dsimp [gP]
    rw [div_pow]
    have hsq2 : (√2 : ℝ) ^ 2 = 2 := by norm_num
    rw [hsq2]
    rw [Real.cos_sq (π * z / 4)]
    ring_nf
  -- Compute ∫ z^2 from -2 to 2
  have h_int_z2 : ∫ z in (-2 : ℝ)..2, z ^ 2 = (16 : ℝ) / 3 := by
    rw [integral_pow]
    ring
  -- Define the antiderivative F for z^2 * cos(πz/2)
  set F : ℝ → ℝ := λ z =>
    (2 / π) * z ^ 2 * Real.sin (π * z / 2) + (8 / π ^ 2) * z * Real.cos (π * z / 2) + (-(16 / π ^ 3) * Real.sin (π * z / 2))
  have hFderiv (z : ℝ) : HasDerivAt F (z ^ 2 * Real.cos (π * z / 2)) z := by
    dsimp [F]
    -- Derivative of z ↦ z^2
    have hz2 : HasDerivAt (λ x : ℝ => x ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    -- Derivative of z ↦ sin(πz/2)
    have hsin_inner : HasDerivAt (λ x : ℝ => π * x / 2) (π / 2) z := by
      have : (λ x : ℝ => π * x / 2) = (λ x => (π/2) * x) := by ext x; ring
      rw [this]
      simpa using hasDerivAt_const_mul (π/2) (x := z)
    have hsin : HasDerivAt (λ x : ℝ => Real.sin (π * x / 2)) (Real.cos (π * z / 2) * (π / 2)) z :=
      HasDerivAt.comp z (hasDerivAt_sin _) hsin_inner
    -- Derivative of z ↦ cos(πz/2)
    have hcos : HasDerivAt (λ x : ℝ => Real.cos (π * x / 2)) (-Real.sin (π * z / 2) * (π / 2)) z :=
      HasDerivAt.comp z (hasDerivAt_cos _) hsin_inner
    -- Derivative of z ↦ z
    have hz' : HasDerivAt (λ x : ℝ => x) 1 z := hasDerivAt_id z
    -- Term 1: (2/π) * z^2 * sin(πz/2)
    have ht1 : HasDerivAt (λ x : ℝ => (2 / π) * x ^ 2 * Real.sin (π * x / 2))
      ((2 / π) * (2 * z * Real.sin (π * z / 2) + z ^ 2 * (Real.cos (π * z / 2) * (π / 2)))) z := by
      have h_mul : HasDerivAt (λ x : ℝ => x ^ 2 * Real.sin (π * x / 2))
        (2 * z * Real.sin (π * z / 2) + z ^ 2 * (Real.cos (π * z / 2) * (π / 2))) z :=
        HasDerivAt.mul hz2 hsin
      have : (λ x : ℝ => (2 / π) * x ^ 2 * Real.sin (π * x / 2)) = (λ x => (2 / π) * (x ^ 2 * Real.sin (π * x / 2))) := by
        ext x; ring
      rw [this]
      exact HasDerivAt.const_mul (2 / π) h_mul
    -- Term 2: (8/π^2) * z * cos(πz/2)
    have ht2 : HasDerivAt (λ x : ℝ => (8 / π ^ 2) * x * Real.cos (π * x / 2))
      ((8 / π ^ 2) * (1 * Real.cos (π * z / 2) + z * (-Real.sin (π * z / 2) * (π / 2)))) z := by
      have h_mul : HasDerivAt (λ x : ℝ => x * Real.cos (π * x / 2))
        (1 * Real.cos (π * z / 2) + z * (-Real.sin (π * z / 2) * (π / 2))) z :=
        HasDerivAt.mul hz' hcos
      have : (λ x : ℝ => (8 / π ^ 2) * x * Real.cos (π * x / 2)) = (λ x => (8 / π ^ 2) * (x * Real.cos (π * x / 2))) := by
        ext x; ring
      rw [this]
      exact HasDerivAt.const_mul (8 / π ^ 2) h_mul
    -- Term 3: -(16/π^3) * sin(πz/2)
    have ht3 : HasDerivAt (λ x : ℝ => -(16 / π ^ 3) * Real.sin (π * x / 2))
      (-(16 / π ^ 3) * (Real.cos (π * z / 2) * (π / 2))) z := by
      have : (λ x : ℝ => -(16 / π ^ 3) * Real.sin (π * x / 2)) = (λ x => (-(16 / π ^ 3)) * Real.sin (π * x / 2)) := by
        ext x; ring
      rw [this]
      exact HasDerivAt.const_mul (-(16 / π ^ 3)) hsin
    -- Combine: F = term1 + term2 + term3
    have hsum12 : HasDerivAt (λ x : ℝ => (2 / π) * x ^ 2 * Real.sin (π * x / 2) + (8 / π ^ 2) * x * Real.cos (π * x / 2))
      (((2 / π) * (2 * z * Real.sin (π * z / 2) + z ^ 2 * (Real.cos (π * z / 2) * (π / 2)))) +
       ((8 / π ^ 2) * (1 * Real.cos (π * z / 2) + z * (-Real.sin (π * z / 2) * (π / 2))))) z :=
      HasDerivAt.add ht1 ht2
    have htotal_raw : HasDerivAt (λ x : ℝ => ((2 / π) * x ^ 2 * Real.sin (π * x / 2) + (8 / π ^ 2) * x * Real.cos (π * x / 2)) +
      (-(16 / π ^ 3) * Real.sin (π * x / 2)))
      (((2 / π) * (2 * z * Real.sin (π * z / 2) + z ^ 2 * (Real.cos (π * z / 2) * (π / 2)))) +
       ((8 / π ^ 2) * (1 * Real.cos (π * z / 2) + z * (-Real.sin (π * z / 2) * (π / 2)))) +
       (-(16 / π ^ 3) * (Real.cos (π * z / 2) * (π / 2)))) z :=
      HasDerivAt.add hsum12 ht3
    -- Simplify the derivative expression to z^2 * cos(πz/2)
    have h_eq : ((2 / π) * (2 * z * Real.sin (π * z / 2) + z ^ 2 * (Real.cos (π * z / 2) * (π / 2)))) +
      ((8 / π ^ 2) * (1 * Real.cos (π * z / 2) + z * (-Real.sin (π * z / 2) * (π / 2)))) +
      (-(16 / π ^ 3) * (Real.cos (π * z / 2) * (π / 2))) = z ^ 2 * Real.cos (π * z / 2) := by
      field_simp [hπ]
      ring
    rw [h_eq] at htotal_raw
    exact htotal_raw
  have h_int_z2_cos : ∫ z in (-2 : ℝ)..2, z ^ 2 * Real.cos (π * z / 2) = -(32 : ℝ) / π ^ 2 := by
    have hint : IntervalIntegrable (λ z => z ^ 2 * Real.cos (π * z / 2)) MeasureTheory.volume (-2 : ℝ) 2 := by
      refine Continuous.intervalIntegrable ?_ _ _
      continuity
    have hF_at_2 : F 2 = -(16 : ℝ) / π ^ 2 := by
      dsimp [F]
      have hsin2 : Real.sin (π * 2 / 2) = Real.sin π := by ring_nf
      have hcos2 : Real.cos (π * 2 / 2) = Real.cos π := by ring_nf
      rw [hsin2, hcos2, Real.sin_pi, Real.cos_pi]
      ring
    have hF_at_neg2 : F (-2) = (16 : ℝ) / π ^ 2 := by
      dsimp [F]
      have hsin_neg2 : Real.sin (π * (-2) / 2) = Real.sin (-π) := by ring_nf
      have hcos_neg2 : Real.cos (π * (-2) / 2) = Real.cos (-π) := by ring_nf
      rw [hsin_neg2, hcos_neg2, Real.sin_neg, Real.sin_pi, Real.cos_neg, Real.cos_pi]
      ring
    have hFderiv_on : ∀ x, x ∈ Set.uIcc (-2 : ℝ) 2 → HasDerivAt F (x ^ 2 * Real.cos (π * x / 2)) x := by
      intro x hx
      exact hFderiv x
    calc
      ∫ z in (-2 : ℝ)..2, z ^ 2 * Real.cos (π * z / 2) = F 2 - F (-2) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv_on hint]
      _ = (-(16 : ℝ) / π ^ 2) - ((16 : ℝ) / π ^ 2) := by rw [hF_at_2, hF_at_neg2]
      _ = -(32 : ℝ) / π ^ 2 := by ring
  calc
    ∫ z in (-2 : ℝ)..2, z ^ 2 * gP z ^ 2 = ∫ z in (-2 : ℝ)..2, z ^ 2 * (1/4 + Real.cos (π * z / 2) / 4) := by
      refine intervalIntegral.integral_congr (fun z hz => ?_)
      rw [hgP_sq z]
    _ = ∫ z in (-2 : ℝ)..2, (z ^ 2 / 4 + z ^ 2 * Real.cos (π * z / 2) / 4) := by
      refine intervalIntegral.integral_congr (fun z hz => ?_)
      ring
    _ = (∫ z in (-2 : ℝ)..2, z ^ 2 / 4) + (∫ z in (-2 : ℝ)..2, z ^ 2 * Real.cos (π * z / 2) / 4) := by
      rw [intervalIntegral.integral_add]
      · refine Continuous.intervalIntegrable ?_ _ _
        continuity
      · refine Continuous.intervalIntegrable ?_ _ _
        continuity
    _ = (∫ z in (-2 : ℝ)..2, z ^ 2 * (1/4 : ℝ)) + (∫ z in (-2 : ℝ)..2, z ^ 2 * Real.cos (π * z / 2) * (1/4 : ℝ)) := by
      refine by
        congr 1
        · refine intervalIntegral.integral_congr (fun z hz => ?_)
          ring
        · refine intervalIntegral.integral_congr (fun z hz => ?_)
          ring
    _ = ((∫ z in (-2 : ℝ)..2, z ^ 2) * (1/4 : ℝ)) + ((∫ z in (-2 : ℝ)..2, z ^ 2 * Real.cos (π * z / 2)) * (1/4 : ℝ)) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
    _ = (1/4) * (∫ z in (-2 : ℝ)..2, z ^ 2) + (1/4) * (∫ z in (-2 : ℝ)..2, z ^ 2 * Real.cos (π * z / 2)) := by
      ring
    _ = (1/4) * ((16 : ℝ) / 3) + (1/4) * (-(32 : ℝ) / π ^ 2) := by rw [h_int_z2, h_int_z2_cos]
    _ = 4 / 3 - 8 / π ^ 2 := by
      ring

theorem Jc_pos : 0 < Jc := by unfold Jc; positivity

/-- **The van Trees inequality** (Lemma B.5) for the prior of the paper. -/
theorem vanTreesP {n : ℕ} (α β c : Fin n → ℝ) (hc : ∀ l, c l < 1)
    (h : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| ≤ c l) (ψ : (Fin n → Bool) → ℝ) :
    1 / (Jc + ∑ l, β l ^ 2 / (1 - c l ^ 2)) ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 * lik α β η z * (ψ η - z) ^ 2 :=
  vanTreesG hasDerivAt_gP continuous_gP' gP_two gP_neg_two integral_gP_sq integral_gP_deriv_sq Jc_pos
    α β c hc h ψ

end RegretKappa.LowerSharp
