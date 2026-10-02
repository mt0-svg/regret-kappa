import RegretKappa.Lower.Model

/-!
# Lower bound: the van Trees inequality for the phase-2 model

The paper, Lemma 4.9 (van Trees, finite sample space), for the model of
`Lower/Model.lean` and one fixed prior on `[-2, 2]`.

Departure from the paper (simpler, constants only): the prior is the polynomial density
`f(z) = (15/512) (4 - z²)²` on `[-2, 2]` (the paper's is `(1/2) cos²(π z / 4)`). It is `c h²` with
`h(z) = 4 - z²`, `c = 15/512`, vanishes at `±2`, and its Fisher information is
`4 c ∫ h'² = 5/2` (the paper's `π²/4 = 2.47`). Every integrand below is a polynomial in `z`.

Proof (no division by the prior, no Cauchy-Schwarz for integrals). For `λ ∈ ℝ`, pointwise on
`[-2, 2]`,
`0 ≤ ∑_η c lik [(ψ - z) h - λ (score h + 2 h')]²
   = A(z) - 2 λ M(z) + λ² c (h² ∑ lik score² + 4 h h' ∑ lik score + 4 h'² ∑ lik)`,
with `A = ∑_η c lik (ψ - z)² h²` and `M = ∑_η c (ψ - z) (lik h²)'`. The last bracket is at most
`c (Ī h² + 4 h'²)` (`Model`: mass `1`, mean score `0`, information at most `Ī`). Integrating,
`∫ M = 1` by parts (the boundary terms vanish with `h`), so `0 ≤ ∫ A - 2 λ + λ² (Ī + 5/2)`, and
`λ = 1 / (Ī + 5/2)` gives `∫ A ≥ 1 / (Ī + 5/2)`.
-/

namespace RegretKappa.Lower

open Finset Set MeasureTheory

/-- The prior density `(15/512) (4 - z²)²` on `[-2, 2]`. -/
noncomputable def prior (z : ℝ) : ℝ := 15 / 512 * (4 - z ^ 2) ^ 2

theorem prior_nonneg (z : ℝ) : 0 ≤ prior z := by
  unfold prior
  positivity

@[fun_prop]
theorem continuous_prior : Continuous prior := by
  unfold prior
  fun_prop

-- TARGET

/-- The prior has mass `1`. -/
theorem integral_prior : ∫ z in (-2 : ℝ)..2, prior z = 1 := by
  unfold prior
  have h_expand : (fun (z : ℝ) => (15/512 : ℝ) * ((4 - z ^ 2) ^ 2)) = (fun (z : ℝ) => (15/512 : ℝ) * (16 - 8 * z ^ 2 + z ^ 4)) := by
    ext z; ring
  rw [h_expand]
  rw [intervalIntegral.integral_const_mul]
  have h_int : ∫ z in (-2 : ℝ)..2, (16 - 8 * z ^ 2 + z ^ 4) = (512/15 : ℝ) := by
    have h_cont_sub : Continuous (fun z : ℝ => 16 - 8 * z ^ 2) := by
      continuity
    have h_cont_z4 : Continuous (fun z : ℝ => z ^ 4) := by
      continuity
    have h_cont_16 : Continuous (fun z : ℝ => (16 : ℝ)) := continuous_const
    have h_cont_8z2 : Continuous (fun z : ℝ => 8 * z ^ 2) := by continuity
    have h_int_sub : IntervalIntegrable (fun z : ℝ => 16 - 8 * z ^ 2) MeasureTheory.volume (-2 : ℝ) 2 :=
      h_cont_sub.intervalIntegrable _ _
    have h_int_z4 : IntervalIntegrable (fun z : ℝ => z ^ 4) MeasureTheory.volume (-2 : ℝ) 2 :=
      h_cont_z4.intervalIntegrable _ _
    have h_int_16 : IntervalIntegrable (fun z : ℝ => (16 : ℝ)) MeasureTheory.volume (-2 : ℝ) 2 :=
      h_cont_16.intervalIntegrable _ _
    have h_int_8z2 : IntervalIntegrable (fun z : ℝ => 8 * z ^ 2) MeasureTheory.volume (-2 : ℝ) 2 :=
      h_cont_8z2.intervalIntegrable _ _
    have h_sub : ∫ z in (-2 : ℝ)..2, (16 - 8 * z ^ 2) = (∫ z in (-2 : ℝ)..2, (16 : ℝ)) - (∫ z in (-2 : ℝ)..2, (8 * z ^ 2)) := by
      rw [intervalIntegral.integral_sub h_int_16 h_int_8z2]
    calc
      ∫ z in (-2 : ℝ)..2, (16 - 8 * z ^ 2 + z ^ 4)
          = (∫ z in (-2 : ℝ)..2, (16 - 8 * z ^ 2)) + (∫ z in (-2 : ℝ)..2, z ^ 4) := by
        apply intervalIntegral.integral_add h_int_sub h_int_z4
      _ = ((∫ z in (-2 : ℝ)..2, (16 : ℝ)) - (∫ z in (-2 : ℝ)..2, (8 * z ^ 2))) + (∫ z in (-2 : ℝ)..2, z ^ 4) := by
        rw [h_sub]
      _ = ((∫ z in (-2 : ℝ)..2, (16 : ℝ)) - ((8 : ℝ) * ∫ z in (-2 : ℝ)..2, z ^ 2)) + (∫ z in (-2 : ℝ)..2, z ^ 4) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (((2 : ℝ) - (-2 : ℝ)) • (16 : ℝ) - ((8 : ℝ) * ∫ z in (-2 : ℝ)..2, z ^ 2)) + (∫ z in (-2 : ℝ)..2, z ^ 4) := by
        rw [intervalIntegral.integral_const]
      _ = (((2 : ℝ) - (-2 : ℝ)) * (16 : ℝ) - ((8 : ℝ) * ((((2 : ℝ)^(2+1) - (-2 : ℝ)^(2+1)) / ((2 : ℕ) + 1 : ℝ))))) + ((((2 : ℝ)^(4+1) - (-2 : ℝ)^(4+1)) / ((4 : ℕ) + 1 : ℝ))) := by
        rw [integral_pow 2, integral_pow 4]
        simp [smul_eq_mul]
      _ = (512/15 : ℝ) := by norm_num
  rw [h_int]
  norm_num

/-- The Fisher information of the prior: `4 c ∫ h'² = ∫ (15/32) z² = 5/2`. -/
theorem integral_prior_info : ∫ z in (-2 : ℝ)..2, 15 / 32 * z ^ 2 = 5 / 2 := by
  calc
    ∫ z in (-2 : ℝ)..2, 15 / 32 * z ^ 2 = (15 / 32 : ℝ) * ∫ z in (-2 : ℝ)..2, z ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = (15 / 32 : ℝ) * (((2 : ℝ) ^ (2 + 1) - (-2 : ℝ) ^ (2 + 1)) / ((2 : ℕ) + 1 : ℝ)) := by
      rw [integral_pow]
    _ = 5 / 2 := by
      norm_num

-- TARGET

/-- Integration by parts: `∫ (ψ - z) (lik h²)' = ∫ lik h²`, for one sign vector. -/
theorem integral_by_parts_lik {n : ℕ} (α β : Fin n → ℝ) (η : Fin n → Bool) (ψ : ℝ)
    (h : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| < 1) :
    ∫ z in (-2 : ℝ)..2, (ψ - z) * (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z))) =
      ∫ z in (-2 : ℝ)..2, lik α β η z * (4 - z ^ 2) ^ 2 := by
  set u := fun z : ℝ => ψ - z with hu_def
  set u' := fun _ : ℝ => (-1 : ℝ) with hu'_def
  set v := fun z : ℝ => lik α β η z * (4 - z ^ 2) ^ 2 with hv_def
  set v' := fun z : ℝ => lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
    lik α β η z * (2 * (4 - z ^ 2) * (-2 * z)) with hv'_def
  have h_neg_two_le_two : (-2 : ℝ) ≤ 2 := by norm_num
  have hz_mem : ∀ z, z ∈ Set.uIcc (-2 : ℝ) 2 → z ∈ Icc (-2 : ℝ) 2 := by
    intro z hz
    rw [Set.uIcc_of_le h_neg_two_le_two] at hz
    exact hz
  have hu_deriv : ∀ z ∈ Set.uIcc (-2 : ℝ) 2, HasDerivAt u (u' z) z := by
    intro z hz
    dsimp [u, u']
    convert ((hasDerivAt_const (c := ψ) (x := z)).sub (hasDerivAt_id (x := z))) using 1
    · rfl
    · ring
  have h_inner_deriv : ∀ z ∈ Set.uIcc (-2 : ℝ) 2, HasDerivAt (fun z => 4 - z ^ 2) (-2 * z) z := by
    intro z hz
    have h4 : HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 z := hasDerivAt_const (c := 4) (x := z)
    have hz2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have hsub := h4.sub hz2
    -- hsub : HasDerivAt ((fun _ => 4) - (fun z => z ^ 2)) (0 - 2 * z) z
    -- Need to convert to HasDerivAt (fun z => 4 - z ^ 2) (-2 * z) z
    convert hsub using 1
    · ring
  have hv_deriv : ∀ z ∈ Set.uIcc (-2 : ℝ) 2, HasDerivAt v (v' z) z := by
    intro z hz
    dsimp [v, v']
    have hzIcc : z ∈ Icc (-2 : ℝ) 2 := hz_mem z hz
    have h_cond : ∀ l, |α l + β l * z| < 1 := fun l => h l z hzIcc
    have h_lik : HasDerivAt (lik α β η) (lik α β η z * score α β η z) z :=
      hasDerivAt_lik α β η h_cond
    have h_poly : HasDerivAt (fun z => (4 - z ^ 2) ^ 2) (2 * (4 - z ^ 2) * (-2 * z)) z := by
      have h_inner := h_inner_deriv z hz
      have h_pow := h_inner.pow 2
      -- h_pow : HasDerivAt ((fun z => 4 - z ^ 2) ^ 2) (2 * (4 - z ^ 2) ^ (2 - 1) * (-2 * z)) z
      convert h_pow using 1
      · ring
    exact HasDerivAt.mul h_lik h_poly
  have hu'_int : IntervalIntegrable u' MeasureTheory.volume (-2 : ℝ) 2 := by
    dsimp [u']
    exact Continuous.intervalIntegrable continuous_const _ _
  have hv'_int : IntervalIntegrable v' MeasureTheory.volume (-2 : ℝ) 2 := by
    have h_cont : ContinuousOn v' (Set.uIcc (-2 : ℝ) 2) := by
      dsimp [v']
      refine ContinuousOn.add ?_ ?_
      · -- lik * score * (4 - z^2)^2
        refine ContinuousOn.mul ?_ ?_
        · -- lik * score
          refine ContinuousOn.mul ?_ ?_
          · -- lik is continuous everywhere
            exact (continuous_lik α β η).continuousOn
          · -- score is continuous on uIcc
            unfold score
            refine continuousOn_finsetSum Finset.univ ?_
            intro l hl
            have h_denom_pos : ∀ z ∈ Set.uIcc (-2 : ℝ) 2, 1 + sgn (η l) * (α l + β l * z) ≠ 0 := by
              intro z' hz'
              have hz'Icc : z' ∈ Icc (-2 : ℝ) 2 := by
                rw [Set.uIcc_of_le h_neg_two_le_two] at hz'
                exact hz'
              have h_abs : |α l + β l * z'| < 1 := h l z' hz'Icc
              have h_sgn : sgn (η l) = 1 ∨ sgn (η l) = -1 := by
                cases η l <;> simp [sgn]
              rcases h_sgn with (hs | hs)
              · rw [hs]
                have := abs_lt.mp h_abs
                linarith
              · rw [hs]
                have := abs_lt.mp h_abs
                linarith
            refine ContinuousOn.div continuousOn_const ?_ (fun z hz => h_denom_pos z hz)
            -- denominator: 1 + sgn (η l) * (α l + β l * z)
            -- This is a sum of products of constants and identity, hence continuous
            have h_denom_cont : ContinuousOn (fun z => 1 + sgn (η l) * (α l + β l * z)) (Set.uIcc (-2 : ℝ) 2) := by
              refine ContinuousOn.add continuousOn_const ?_
              refine ContinuousOn.mul continuousOn_const ?_
              refine ContinuousOn.add continuousOn_const ?_
              refine ContinuousOn.mul continuousOn_const continuousOn_id
            exact h_denom_cont
        · -- (4 - z^2)^2
          refine (ContinuousOn.pow ?_ 2)
          refine ContinuousOn.sub continuousOn_const (ContinuousOn.pow continuousOn_id 2)
      · -- lik * (2 * (4 - z^2) * (-2*z))
        refine ContinuousOn.mul ?_ ?_
        · exact (continuous_lik α β η).continuousOn
        · -- polynomial part: 2 * (4 - z^2) * (-2*z)
          -- Note: 2 * (4 - z^2) * (-2*z) is parsed as (2 * (4 - z^2)) * (-2*z)
          refine ContinuousOn.mul ?_ ?_
          · -- 2 * (4 - z^2)
            refine ContinuousOn.mul continuousOn_const ?_
            refine ContinuousOn.sub continuousOn_const (ContinuousOn.pow continuousOn_id 2)
          · -- -2 * z
            refine ContinuousOn.mul continuousOn_const continuousOn_id
    exact h_cont.intervalIntegrable
  have h_parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv hv_deriv hu'_int hv'_int
  have hv2 : v (2 : ℝ) = 0 := by
    dsimp [v]
    ring
  have hvneg2 : v (-2 : ℝ) = 0 := by
    dsimp [v]
    ring
  rw [hv2, hvneg2] at h_parts
  have hu2 : u (2 : ℝ) = ψ - 2 := rfl
  have huneg2 : u (-2 : ℝ) = ψ + 2 := by
    dsimp [u]
    ring
  simp [hu2, huneg2] at h_parts
  -- h_parts: ∫ u * v' = -∫ u' * v
  have hu'_val : u' = fun _ => (-1 : ℝ) := rfl
  rw [hu'_val] at h_parts
  -- h_parts: ∫ u * v' = -∫ (-1) * v
  have h_simp : (fun z : ℝ => (-1 : ℝ) * v z) = fun z => -v z := by
    ext z; simp
  rw [h_simp] at h_parts
  -- h_parts: ∫ u * v' = -∫ (-v) = ∫ v
  have h_neg : (∫ z in (-2 : ℝ)..2, -v z) = - (∫ z in (-2 : ℝ)..2, v z) := by
    rw [intervalIntegral.integral_neg]
  rw [h_neg] at h_parts
  -- h_parts: ∫ u * v' = -( -∫ v) = ∫ v
  simp at h_parts
  -- h_parts: ∫ u * v' = ∫ v
  -- Now expand definitions
  dsimp [u, v, v'] at h_parts ⊢
  exact h_parts

/-- The pointwise quadratic inequality of the proof. -/
theorem vanTrees_pointwise {n : ℕ} (α β c : Fin n → ℝ) (ψ : (Fin n → Bool) → ℝ) (lam : ℝ) {z : ℝ}
    (h : ∀ l, |α l + β l * z| ≤ c l) (hc : ∀ l, c l < 1) :
    0 ≤ ∑ η, prior z * lik α β η z * (ψ η - z) ^ 2 -
      2 * lam * ∑ η, 15 / 512 * ((ψ η - z) * (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z)))) +
      lam ^ 2 * ((∑ l, β l ^ 2 / (1 - c l ^ 2)) * prior z + 15 / 32 * z ^ 2) := by
  have hlt : ∀ l, |α l + β l * z| < 1 := fun l => (h l).trans_lt (hc l)
  have hle : ∀ l, |α l + β l * z| ≤ 1 := fun l => (hlt l).le
  have hI : ∑ η, lik α β η z * score α β η z ^ 2 ≤ ∑ l, β l ^ 2 / (1 - c l ^ 2) := by
    rw [sum_lik_score_sq α β hlt]
    refine Finset.sum_le_sum fun l _ => ?_
    have h0 : 0 ≤ c l := (abs_nonneg _).trans (h l)
    have h1 : (α l + β l * z) ^ 2 ≤ c l ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h l) 2
    have h2 : 0 < 1 - c l ^ 2 := by nlinarith [hc l]
    exact div_le_div_of_nonneg_left (sq_nonneg _) h2 (by linarith)
  have hQ : 0 ≤ ∑ η, 15 / 512 * lik α β η z * ((ψ η - z) * (4 - z ^ 2) -
      lam * (score α β η z * (4 - z ^ 2) + 2 * (-2 * z))) ^ 2 :=
    Finset.sum_nonneg fun η _ =>
      mul_nonneg (mul_nonneg (by norm_num) (lik_nonneg hle η)) (sq_nonneg _)
  have hexp : ∑ η, 15 / 512 * lik α β η z * ((ψ η - z) * (4 - z ^ 2) -
      lam * (score α β η z * (4 - z ^ 2) + 2 * (-2 * z))) ^ 2 =
      ∑ η, prior z * lik α β η z * (ψ η - z) ^ 2 -
      2 * lam * ∑ η, 15 / 512 * ((ψ η - z) * (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z)))) +
      lam ^ 2 * (15 / 512 * (4 - z ^ 2) ^ 2 * ∑ η, lik α β η z * score α β η z ^ 2 +
        15 / 512 * (4 * (4 - z ^ 2) * (-2 * z)) * ∑ η, lik α β η z * score α β η z +
        15 / 512 * (4 * (-2 * z) ^ 2) * ∑ η, lik α β η z) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun η _ => ?_
    unfold prior; ring
  rw [sum_lik_score α β hlt, sum_lik] at hexp
  have hP : lam ^ 2 * (15 / 512 * (4 - z ^ 2) ^ 2 * ∑ η, lik α β η z * score α β η z ^ 2) ≤
      lam ^ 2 * ((∑ l, β l ^ 2 / (1 - c l ^ 2)) * prior z) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg lam)
    rw [mul_comm _ (prior z)]
    unfold prior
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  nlinarith

/-- The score is continuous on `[-2, 2]`, where no factor of `lik` vanishes. -/
theorem continuousOn_score {n : ℕ} (α β : Fin n → ℝ) (η : Fin n → Bool)
    (h : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| < 1) :
    ContinuousOn (score α β η) (Icc (-2) 2) := by
  unfold score
  refine continuousOn_finsetSum _ fun l _ => ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
  have := abs_lt.mp (h l z hz)
  cases η l <;> simp only [sgn_true, sgn_false] <;> intro h0 <;> linarith


/-- **van Trees inequality** for the phase-2 model with the prior `prior`: every estimator `ψ`
of `z` from the signs has Bayes risk at least `1 / (5/2 + Ī)`, with `Ī = ∑ β_l² / (1 - c_l²)` a
bound of the Fisher information on `[-2, 2]`. -/
theorem vanTrees {n : ℕ} (α β c : Fin n → ℝ) (hc : ∀ l, c l < 1)
    (h : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| ≤ c l) (ψ : (Fin n → Bool) → ℝ) :
    1 / (5 / 2 + ∑ l, β l ^ 2 / (1 - c l ^ 2)) ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik α β η z * (ψ η - z) ^ 2 := by
  set I := ∑ l, β l ^ 2 / (1 - c l ^ 2) with hIdef
  have hc0 : ∀ l, 0 ≤ c l := fun l => (abs_nonneg _).trans (h l 0 ⟨by norm_num, by norm_num⟩)
  have hI0 : 0 ≤ I :=
    Finset.sum_nonneg fun l _ => div_nonneg (sq_nonneg _) (by nlinarith [hc l, hc0 l])
  have hD0 : 0 < 5 / 2 + I := by linarith
  set lam := 1 / (5 / 2 + I) with hlam
  have hlt : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| < 1 :=
    fun l z hz => (h l z hz).trans_lt (hc l)
  have hcl : ∀ η, Continuous (lik α β η) := continuous_lik α β
  have hA : IntervalIntegrable (fun z => ∑ η, prior z * lik α β η z * (ψ η - z) ^ 2)
      volume (-2) 2 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun η _ => by have := hcl η; fun_prop
  have hMη : ∀ η, IntervalIntegrable (fun z => 15 / 512 * ((ψ η - z) *
      (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z))))) volume (-2) 2 := by
    intro η
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    have h1 := (hcl η).continuousOn (s := Icc (-2 : ℝ) 2)
    have h2 := continuousOn_score α β η hlt
    fun_prop
  have hM : IntervalIntegrable (fun z => ∑ η, 15 / 512 * ((ψ η - z) *
      (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z))))) volume (-2) 2 :=
    by simpa only [Finset.sum_fn] using IntervalIntegrable.sum univ fun η _ => hMη η
  have hR : IntervalIntegrable (fun z : ℝ => I * prior z + 15 / 32 * z ^ 2) volume (-2) 2 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hMint : ∫ z in (-2 : ℝ)..2, ∑ η, 15 / 512 * ((ψ η - z) *
      (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z)))) = 1 := by
    rw [intervalIntegral.integral_finsetSum fun η _ => hMη η]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [Finset.sum_congr rfl fun η _ => by rw [integral_by_parts_lik α β η (ψ η) hlt]]
    rw [← integral_prior]
    have e : ∀ z, prior z = ∑ η, 15 / 512 * (lik α β η z * (4 - z ^ 2) ^ 2) := by
      intro z
      rw [← Finset.mul_sum, ← Finset.sum_mul, sum_lik]
      unfold prior; ring
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum fun η _ =>
      Continuous.intervalIntegrable (by have := hcl η; fun_prop) _ _]
    simp_rw [intervalIntegral.integral_const_mul]
  have hRint : ∫ z in (-2 : ℝ)..2, (I * prior z + 15 / 32 * z ^ 2) = I + 5 / 2 := by
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
      integral_prior, integral_prior_info, mul_one]
  have hpos : 0 ≤ ∫ z in (-2 : ℝ)..2, ((∑ η, prior z * lik α β η z * (ψ η - z) ^ 2 -
      2 * lam * ∑ η, 15 / 512 * ((ψ η - z) * (lik α β η z * score α β η z * (4 - z ^ 2) ^ 2 +
        lik α β η z * (2 * (4 - z ^ 2) * (-2 * z))))) +
      lam ^ 2 * (I * prior z + 15 / 32 * z ^ 2)) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun z hz => ?_
    exact vanTrees_pointwise α β c ψ lam (fun l => h l z hz) hc
  rw [intervalIntegral.integral_add (hA.sub (hM.const_mul _)) (hR.const_mul _),
    intervalIntegral.integral_sub hA (hM.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hMint, hRint] at hpos
  have e2 : lam ^ 2 * (I + 5 / 2) = lam := by
    rw [hlam]; field_simp; ring
  linarith

end RegretKappa.Lower
