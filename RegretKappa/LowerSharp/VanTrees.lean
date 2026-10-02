import RegretKappa.Lower.VanTrees

/-!
# Sharp lower bound: the van Trees inequality for a prior `g²`

The paper, Lemma 4.9 (van Trees, finite sample space), for the phase-2 model of
`Lower/Model.lean` and any prior density `g²` on `[-2, 2]` with `g` differentiable, `g'`
continuous and `g(±2) = 0`. The Fisher information of the prior is `J = ∫ 4 g'²`
(`π'²/π = 4 g'²` for `π = g²`).

Proof as in `Lower/VanTrees.lean` (no division by the prior, no Cauchy-Schwarz for integrals).
For `λ ∈ ℝ`, pointwise on `[-2, 2]`,
`0 ≤ ∑_η lik [(ψ - z) g - λ (score g + 2 g')]²
   = A(z) - 2 λ M(z) + λ² (g² ∑ lik score² + 4 g g' ∑ lik score + 4 g'² ∑ lik)`,
with `A = ∑_η lik (ψ - z)² g²` and `M = ∑_η (ψ - z) (lik g²)'`. The last bracket is at most
`Ī g² + 4 g'²`. Integrating, `∫ M = ∫ g² = 1` by parts (the boundary terms vanish with `g`), so
`0 ≤ ∫ A - 2 λ + λ² (Ī + J)`, and `λ = 1 / (Ī + J)` gives `∫ A ≥ 1 / (J + Ī)`.
-/

namespace RegretKappa.LowerSharp

open Finset Set MeasureTheory RegretKappa.Lower

/-- Integration by parts: `∫ (ψ - z) (lik g²)' = ∫ lik g²`, for one sign vector. -/
theorem integral_by_parts_likG {n : ℕ} {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z)
    (hg' : Continuous g') (h2 : g 2 = 0) (hm2 : g (-2) = 0)
    (α β : Fin n → ℝ) (η : Fin n → Bool) (ψ : ℝ)
    (h : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| < 1) :
    ∫ z in (-2 : ℝ)..2, (ψ - z) * (lik α β η z * score α β η z * g z ^ 2 +
        lik α β η z * (2 * g z * g' z)) =
      ∫ z in (-2 : ℝ)..2, lik α β η z * g z ^ 2 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z => (hg z).continuousAt
  have hv : ∀ z ∈ uIcc (-2 : ℝ) 2, HasDerivAt (fun z => lik α β η z * g z ^ 2)
      (lik α β η z * score α β η z * g z ^ 2 + lik α β η z * (2 * g z * g' z)) z := by
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    have h1 := hasDerivAt_lik α β η (fun l => h l z hz)
    have h3 := (hg z).pow 2
    convert h1.mul h3 using 1
    simp only [Pi.pow_apply]
    push_cast
    ring
  have hu : ∀ z ∈ uIcc (-2 : ℝ) 2, HasDerivAt (fun z => ψ - z) (-1) z := fun z _ => by
    simpa using (hasDerivAt_id z).const_sub ψ
  have hv' : IntervalIntegrable (fun z => lik α β η z * score α β η z * g z ^ 2 +
      lik α β η z * (2 * g z * g' z)) volume (-2) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    have c1 := continuousOn_score α β η h
    have c2 := (continuous_lik α β η).continuousOn (s := Icc (-2 : ℝ) 2)
    have c3 := hgc.continuousOn (s := Icc (-2 : ℝ) 2)
    have c4 := hg'.continuousOn (s := Icc (-2 : ℝ) 2)
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (intervalIntegrable_const (c := (-1 : ℝ))) hv'
  rw [hparts]
  simp only [h2, hm2]
  rw [show (fun x => -1 * (lik α β η x * g x ^ 2)) = fun x => -(lik α β η x * g x ^ 2) from
    funext fun x => by ring, intervalIntegral.integral_neg]
  ring

/-- The pointwise quadratic inequality of the proof. -/
theorem vanTreesG_pointwise {n : ℕ} (gz g'z : ℝ) (α β c : Fin n → ℝ) (ψ : (Fin n → Bool) → ℝ)
    (lam : ℝ) {z : ℝ} (h : ∀ l, |α l + β l * z| ≤ c l) (hc : ∀ l, c l < 1) :
    0 ≤ ∑ η, gz ^ 2 * lik α β η z * (ψ η - z) ^ 2 -
      2 * lam * ∑ η, (ψ η - z) * (lik α β η z * score α β η z * gz ^ 2 +
        lik α β η z * (2 * gz * g'z)) +
      lam ^ 2 * ((∑ l, β l ^ 2 / (1 - c l ^ 2)) * gz ^ 2 + 4 * g'z ^ 2) := by
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
  have hQ : 0 ≤ ∑ η, lik α β η z * ((ψ η - z) * gz -
      lam * (score α β η z * gz + 2 * g'z)) ^ 2 :=
    Finset.sum_nonneg fun η _ => mul_nonneg (lik_nonneg hle η) (sq_nonneg _)
  have hexp : ∑ η, lik α β η z * ((ψ η - z) * gz -
      lam * (score α β η z * gz + 2 * g'z)) ^ 2 =
      ∑ η, gz ^ 2 * lik α β η z * (ψ η - z) ^ 2 -
      2 * lam * ∑ η, (ψ η - z) * (lik α β η z * score α β η z * gz ^ 2 +
        lik α β η z * (2 * gz * g'z)) +
      lam ^ 2 * (gz ^ 2 * ∑ η, lik α β η z * score α β η z ^ 2 +
        4 * gz * g'z * ∑ η, lik α β η z * score α β η z +
        4 * g'z ^ 2 * ∑ η, lik α β η z) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  rw [sum_lik_score α β hlt, sum_lik] at hexp
  have hP : lam ^ 2 * (gz ^ 2 * ∑ η, lik α β η z * score α β η z ^ 2) ≤
      lam ^ 2 * ((∑ l, β l ^ 2 / (1 - c l ^ 2)) * gz ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg lam)
    rw [mul_comm _ (gz ^ 2)]
    exact mul_le_mul_of_nonneg_left hI (sq_nonneg _)
  nlinarith

/-- **van Trees inequality** for the phase-2 model with a prior `g²` of mass `1` and Fisher
information `J = ∫ 4 g'² > 0`: every estimator `ψ` of `z` from the signs has Bayes risk at least
`1 / (J + Ī)`, with `Ī = ∑ β_l² / (1 - c_l²)` a bound of the Fisher information of the model on
`[-2, 2]`. -/
theorem vanTreesG {n : ℕ} {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z)
    (hg' : Continuous g') (h2 : g 2 = 0) (hm2 : g (-2) = 0)
    (hmass : ∫ z in (-2 : ℝ)..2, g z ^ 2 = 1) {J : ℝ}
    (hJ : ∫ z in (-2 : ℝ)..2, 4 * g' z ^ 2 = J) (hJ0 : 0 < J)
    (α β c : Fin n → ℝ) (hc : ∀ l, c l < 1)
    (h : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| ≤ c l) (ψ : (Fin n → Bool) → ℝ) :
    1 / (J + ∑ l, β l ^ 2 / (1 - c l ^ 2)) ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, g z ^ 2 * lik α β η z * (ψ η - z) ^ 2 := by
  set I := ∑ l, β l ^ 2 / (1 - c l ^ 2) with hIdef
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z => (hg z).continuousAt
  have hc0 : ∀ l, 0 ≤ c l := fun l => (abs_nonneg _).trans (h l 0 ⟨by norm_num, by norm_num⟩)
  have hI0 : 0 ≤ I :=
    Finset.sum_nonneg fun l _ => div_nonneg (sq_nonneg _) (by nlinarith [hc l, hc0 l])
  have hD0 : 0 < J + I := by linarith
  set lam := 1 / (J + I) with hlam
  have hlt : ∀ l, ∀ z ∈ Icc (-2 : ℝ) 2, |α l + β l * z| < 1 :=
    fun l z hz => (h l z hz).trans_lt (hc l)
  have hcl : ∀ η, Continuous (lik α β η) := continuous_lik α β
  have hA : IntervalIntegrable (fun z => ∑ η, g z ^ 2 * lik α β η z * (ψ η - z) ^ 2)
      volume (-2) 2 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun η _ => by have := hcl η; fun_prop
  have hMη : ∀ η, IntervalIntegrable (fun z => (ψ η - z) *
      (lik α β η z * score α β η z * g z ^ 2 +
        lik α β η z * (2 * g z * g' z))) volume (-2) 2 := by
    intro η
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    have c1 := (hcl η).continuousOn (s := Icc (-2 : ℝ) 2)
    have c2 := continuousOn_score α β η hlt
    have c3 := hgc.continuousOn (s := Icc (-2 : ℝ) 2)
    have c4 := hg'.continuousOn (s := Icc (-2 : ℝ) 2)
    fun_prop
  have hM : IntervalIntegrable (fun z => ∑ η, (ψ η - z) *
      (lik α β η z * score α β η z * g z ^ 2 +
        lik α β η z * (2 * g z * g' z))) volume (-2) 2 :=
    by simpa only [Finset.sum_fn] using IntervalIntegrable.sum univ fun η _ => hMη η
  have hR : IntervalIntegrable (fun z : ℝ => I * g z ^ 2 + 4 * g' z ^ 2) volume (-2) 2 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hMint : ∫ z in (-2 : ℝ)..2, ∑ η, (ψ η - z) *
      (lik α β η z * score α β η z * g z ^ 2 +
        lik α β η z * (2 * g z * g' z)) = 1 := by
    rw [intervalIntegral.integral_finsetSum fun η _ => hMη η]
    rw [Finset.sum_congr rfl fun η _ => by
      rw [integral_by_parts_likG hg hg' h2 hm2 α β η (ψ η) hlt]]
    rw [← hmass]
    have e : ∀ z, g z ^ 2 = ∑ η, lik α β η z * g z ^ 2 := by
      intro z
      rw [← Finset.sum_mul, sum_lik, one_mul]
    rw [← intervalIntegral.integral_finsetSum fun η _ =>
      Continuous.intervalIntegrable (by have := hcl η; fun_prop) _ _]
    simp_rw [← e]
  have hRint : ∫ z in (-2 : ℝ)..2, (I * g z ^ 2 + 4 * g' z ^ 2) = I + J := by
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
      hmass, hJ, mul_one]
  have hpos : 0 ≤ ∫ z in (-2 : ℝ)..2, ((∑ η, g z ^ 2 * lik α β η z * (ψ η - z) ^ 2 -
      2 * lam * ∑ η, (ψ η - z) * (lik α β η z * score α β η z * g z ^ 2 +
        lik α β η z * (2 * g z * g' z))) +
      lam ^ 2 * (I * g z ^ 2 + 4 * g' z ^ 2)) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun z hz => ?_
    exact vanTreesG_pointwise (g z) (g' z) α β c ψ lam (fun l => h l z hz) hc
  rw [intervalIntegral.integral_add (hA.sub (hM.const_mul _)) (hR.const_mul _),
    intervalIntegral.integral_sub hA (hM.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hMint, hRint] at hpos
  have e2 : lam ^ 2 * (I + J) = lam := by
    rw [hlam]; field_simp; ring
  linarith

end RegretKappa.LowerSharp
