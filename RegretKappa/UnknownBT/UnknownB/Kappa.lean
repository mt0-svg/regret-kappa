import RegretKappa.UnknownBT.UnknownB.Gamma

/-!
# Unknown `B`: the scale lemma and its constant

In the units of `RegretKappa.Upper`. With `v = r²/2` and
`bco n = Mw n 2ⁿ n!/(2n)!` (half the `a_n` of the paper), `G r = ∑ bco n vⁿ/n!` (`G_hasSum_b`) and
`r G1 r / 2 = ∑ n bco n vⁿ/n!` (`rG1_hasSum_b`). The coefficients satisfy `bco n ≤ bco 1`
(`bco_le_one`) and `(n + 1)(bco n - bco (n + 1)) ≤ (16/15) bco (n + 1)` (`bco_beta`), so the Poisson
form bounds `G0(r) = 2 log(G r / G 0) - r G1 r / G r` by
`kappaB = 2 log((e^{-1/2} + 2 K0)/e^{-1/2}) + 32/15` (`G0_le`). The reduction in the level
(`lam_reduction`) turns this into the pointwise scale inequality `2P - wP' ≤ 2 kappaB` for
`P(w) = 2 log((l + G w)/A)`, `A ≥ l + G 0` (`scale_pointwise`), and its integrated form
`m² P(r/m) - P(r) ≤ kappaB (m² - 1)` for `m ≥ 1` (`scale_lemma`).
-/

namespace RegretKappa.UnknownBT.UB

open Real MeasureTheory Set Finset RegretKappa RegretKappa.UpperSharp

/-- `bco n = Mw n 2ⁿ n!/(2n)!`, so that `G r = ∑ bco n (r²/2)ⁿ/n!`. -/
noncomputable def bco (n : ℕ) : ℝ := Mw n * 2 ^ n * (n.factorial : ℝ) / ((2 * n).factorial : ℝ)

theorem G_hasSum (r : ℝ) :
    HasSum (fun n : ℕ => Mw n * r ^ (2 * n) / ((2 * n).factorial : ℝ)) (Upper.G r) := by
  set F : ℕ → ℝ → ℝ := fun n θ => θ ^ (2 * n) * r ^ (2 * n) / ((2 * n).factorial : ℝ) * Upper.wt θ
    with hF
  have hFi : ∀ n, IntegrableOn (F n) (Ioi 1) := fun n => by
    have h : IntegrableOn (fun θ => r ^ (2 * n) / ((2 * n).factorial : ℝ) *
        (θ ^ (2 * n) * Upper.wt θ)) (Ioi 1) := (integrableOn_pow_wt (2 * n)).const_mul _
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioi
    simp only [hF]
    ring
  have hlim : ∀ θ, HasSum (fun n => F n θ) (cosh (θ * r) * Upper.wt θ) := fun θ => by
    have h := (Real.hasSum_cosh (θ * r)).mul_right (Upper.wt θ)
    refine h.congr_fun fun n => ?_
    simp only [hF, mul_pow]
  have hFn : ∀ n, ∀ θ ∈ Ioi (1 : ℝ), 0 ≤ F n θ := fun n θ hθ => by
    have hθ0 : 0 ≤ θ := (lt_trans one_pos hθ).le
    have := (Upper.wt_pos (lt_trans one_pos hθ)).le
    have : 0 ≤ r ^ (2 * n) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg r) n
    simp only [hF]
    positivity
  have key := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := F) (f := fun θ => cosh (θ * r) * Upper.wt θ) F
    (fun n => (hFi n).aestronglyMeasurable)
    (fun n => (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (hFn n θ hθ)]))
    (Filter.Eventually.of_forall fun θ => (hlim θ).summable)
    ((Upper.integrableOn_G r).congr_fun (fun θ _ => (hlim θ).tsum_eq.symm) measurableSet_Ioi)
    (Filter.Eventually.of_forall hlim)
  refine key.congr_fun fun n => ?_
  simp only [hF, Mw]
  rw [mul_div_assoc, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  ring

theorem G1_eq_Dg {r : ℝ} (hr : 0 < r) : G1 r = 2 * r * Dg (r ^ 2) := by
  unfold G1 Dg
  rw [Real.sqrt_sq hr.le, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  field_simp

theorem hasSum_mul_sinh (x : ℝ) :
    HasSum (fun n : ℕ => 2 * (n : ℝ) * x ^ (2 * n) / ((2 * n).factorial : ℝ)) (x * sinh x) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_mul, zero_div,
    sub_zero]
  have h := (Real.hasSum_sinh x).mul_left x
  refine h.congr_fun fun n => ?_
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ]
  push_cast
  have : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem rG1_hasSum (r : ℝ) :
    HasSum (fun n : ℕ => 2 * (n : ℝ) * Mw n * r ^ (2 * n) / ((2 * n).factorial : ℝ)) (r * G1 r) := by
  set F : ℕ → ℝ → ℝ := fun n θ =>
    2 * (n : ℝ) * θ ^ (2 * n) * r ^ (2 * n) / ((2 * n).factorial : ℝ) * Upper.wt θ with hF
  have hFi : ∀ n, IntegrableOn (F n) (Ioi 1) := fun n => by
    have h : IntegrableOn (fun θ => 2 * (n : ℝ) * r ^ (2 * n) / ((2 * n).factorial : ℝ) *
        (θ ^ (2 * n) * Upper.wt θ)) (Ioi 1) := (integrableOn_pow_wt (2 * n)).const_mul _
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioi
    simp only [hF]
    ring
  have hlim : ∀ θ, HasSum (fun n => F n θ) (r * (θ * sinh (θ * r) * Upper.wt θ)) := fun θ => by
    have h := (hasSum_mul_sinh (θ * r)).mul_right (Upper.wt θ)
    have e : θ * r * sinh (θ * r) * Upper.wt θ = r * (θ * sinh (θ * r) * Upper.wt θ) := by ring
    rw [e] at h
    refine h.congr_fun fun n => ?_
    simp only [hF, mul_pow]
    ring
  have hFn : ∀ n, ∀ θ ∈ Ioi (1 : ℝ), 0 ≤ F n θ := fun n θ hθ => by
    have hθ0 : 0 ≤ θ := (lt_trans one_pos hθ).le
    have := (Upper.wt_pos (lt_trans one_pos hθ)).le
    have : 0 ≤ r ^ (2 * n) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg r) n
    simp only [hF]
    positivity
  have hI : IntegrableOn (fun θ => r * (θ * sinh (θ * r) * Upper.wt θ)) (Ioi 1) :=
    (integrableOn_G1 r).const_mul r
  have key := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := F) (f := fun θ => r * (θ * sinh (θ * r) * Upper.wt θ)) F
    (fun n => (hFi n).aestronglyMeasurable)
    (fun n => (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (hFn n θ hθ)]))
    (Filter.Eventually.of_forall fun θ => (hlim θ).summable)
    (hI.congr_fun (fun θ _ => (hlim θ).tsum_eq.symm) measurableSet_Ioi)
    (Filter.Eventually.of_forall hlim)
  rw [integral_const_mul] at key
  refine key.congr_fun fun n => ?_
  simp only [hF, Mw]
  rw [show 2 * (n : ℝ) * (∫ θ in Ioi 1, θ ^ (2 * n) * Upper.wt θ) * r ^ (2 * n) /
      ((2 * n).factorial : ℝ) = (∫ θ in Ioi 1, θ ^ (2 * n) * Upper.wt θ) *
      (2 * (n : ℝ) * r ^ (2 * n) / ((2 * n).factorial : ℝ)) by ring, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  ring

theorem G_hasSum_b (r : ℝ) :
    HasSum (fun n : ℕ => bco n * (r ^ 2 / 2) ^ n / (n.factorial : ℝ)) (Upper.G r) := by
  refine (G_hasSum r).congr_fun fun n => ?_
  unfold bco
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, pow_mul]
  field_simp

theorem rG1_hasSum_b (r : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * bco n * (r ^ 2 / 2) ^ n / (n.factorial : ℝ)) (r * G1 r / 2) := by
  refine ((rG1_hasSum r).div_const 2).congr_fun fun n => ?_
  unfold bco
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, pow_mul]
  field_simp

theorem bco_nonneg (n : ℕ) : 0 ≤ bco n := by
  have := Mw_nonneg n
  unfold bco
  positivity

theorem bco_zero : bco 0 = exp (-1 / 2) := by
  calc
    bco 0 = Mw 0 := by
      simp [bco, Mw]
    _ = Upper.G 0 := by
      simp [Mw, Upper.G, cosh_zero]
    _ = exp (-1 / 2) := G_zero

theorem bco_one : bco 1 = exp (-1 / 2) + 2 * K0 := by
  have hMw : Mw 1 = exp (-1 / 2) + 2 * K0 := by
    have hGamC : GamC (exp (-1 / 2)) K0 1 = 2 * exp (-1 / 2) + 4 * K0 := by
      unfold GamC
      simp
    have hMw_eq := Mw_eq_GamC (show 1 ≤ 1 from by decide)
    rw [hMw_eq, hGamC]
    ring
  calc
    bco 1 = Mw 1 * 2 ^ 1 * ((1 : ℕ).factorial : ℝ) / (((2 : ℕ) * 1).factorial : ℝ) := rfl
    _ = Mw 1 := by norm_num
    _ = exp (-1 / 2) + 2 * K0 := hMw

/-- The common factor of `bco n` and `bco (n + 1)` for `n ≥ 2`. -/
noncomputable def bcf (n : ℕ) : ℝ := exp (-1 / 2) * 2 ^ n * (n.factorial : ℝ) / ((2 * n).factorial : ℝ)

theorem bcf_pos (n : ℕ) : 0 < bcf n := by
  unfold bcf; have := exp_pos (-1 / 2 : ℝ); positivity

theorem bco_eq_bcf {n : ℕ} (hn : 2 ≤ n) :
    bco n = bcf n * ((kk n : ℝ) + 2 * kk (n - 1)) := by
  unfold bco bcf
  rw [Mw_eq_GamC (by omega)]
  simp only [GamC, show n ≠ 1 by omega, ite_false]
  ring

theorem bco_succ_eq_bcf {n : ℕ} (hn : 2 ≤ n) :
    bco (n + 1) = bcf n * ((kk (n + 1) : ℝ) + 2 * kk n) / (2 * n + 1) := by
  unfold bco bcf
  rw [Mw_eq_GamC (by omega)]
  simp only [GamC, show n + 1 ≠ 1 by omega, ite_false, Nat.add_sub_cancel]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  have h1 : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem bco_succ_le {n : ℕ} (hn : 2 ≤ n) : bco (n + 1) ≤ bco n := by
  rw [bco_eq_bcf hn, bco_succ_eq_bcf hn]
  have h := kk_ratio_mono n hn
  have hR : ((kk (n + 1) : ℝ) + 2 * kk n) ≤ (2 * n + 1) * ((kk n : ℝ) + 2 * kk (n - 1)) := by
    exact_mod_cast h
  have hc := bcf_pos n
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem bco_le_one (n : ℕ) : bco n ≤ bco 1 := by
  have hE := exp_neg_half_bounds
  have hK := K0_ge
  have h21 : bco 2 ≤ bco 1 := by
    rw [bco_eq_bcf le_rfl, bco_one]
    simp [bcf, kk, Nat.factorial]
    norm_num
    linarith
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · rw [bco_zero, bco_one]; linarith
    · exact le_rfl
  · refine le_trans ?_ h21
    induction n, h using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (bco_succ_le hk).trans ih

theorem bco_beta (n : ℕ) : ((n : ℝ) + 1) * (bco n - bco (n + 1)) ≤ 16 / 15 * bco (n + 1) := by
  have hE := exp_neg_half_bounds
  have hK := K0_ge
  have hK' := K0_le
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · rw [bco_zero, show (0 : ℕ) + 1 = 1 from rfl, bco_one]; norm_num; linarith
    · rw [show (1 : ℕ) + 1 = 2 from rfl, bco_one, bco_eq_bcf le_rfl]
      simp [bcf, kk, Nat.factorial]
      norm_num
      linarith
  · rw [bco_eq_bcf h, bco_succ_eq_bcf h]
    have hb := kk_ratio_beta n h
    have hR : 15 * (((n : ℝ) + 1) * (2 * n + 1)) * ((kk n : ℝ) + 2 * kk (n - 1)) ≤
        (15 * ((n : ℝ) + 1) + 16) * ((kk (n + 1) : ℝ) + 2 * kk n) := by
      exact_mod_cast hb
    have hc := bcf_pos n
    have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
    have key : 15 * (((n : ℝ) + 1) * ((kk n : ℝ) + 2 * kk (n - 1))) ≤
        (15 * ((n : ℝ) + 1) + 16) * (((kk (n + 1) : ℝ) + 2 * kk n) / (2 * n + 1)) := by
      rw [mul_div_assoc', le_div_iff₀ h2n]
      linear_combination hR
    have e1 : bcf n * ((kk n : ℝ) + 2 * kk (n - 1)) - bcf n * ((kk (n + 1) : ℝ) + 2 * kk n) /
        (2 * n + 1) = bcf n * (((kk n : ℝ) + 2 * kk (n - 1)) - ((kk (n + 1) : ℝ) + 2 * kk n) /
        (2 * n + 1)) := by ring
    have e2 : 16 / 15 * (bcf n * ((kk (n + 1) : ℝ) + 2 * kk n) / (2 * n + 1)) =
        bcf n * (16 / 15 * (((kk (n + 1) : ℝ) + 2 * kk n) / (2 * n + 1))) := by ring
    rw [e1, e2, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    nlinarith [key]

/-- The constant `κ` of the slope inequality. -/
noncomputable def kappaB : ℝ := 2 * Real.log ((exp (-1 / 2) + 2 * K0) / exp (-1 / 2)) + 2 * (16 / 15)

theorem kappaB_nonneg : 0 ≤ kappaB := by
  unfold kappaB
  have hpos : 0 < exp (-1 / 2) := exp_pos _
  have hdiv : 1 ≤ (exp (-1 / 2) + 2 * K0) / exp (-1 / 2) := by
    rw [one_le_div hpos]
    nlinarith [K0_nonneg]
  have hlog : 0 ≤ Real.log ((exp (-1 / 2) + 2 * K0) / exp (-1 / 2)) :=
    Real.log_nonneg hdiv
  nlinarith

/-- **The slope inequality**: `G0(r) ≤ kappaB`. -/
theorem G0_le {r : ℝ} (_hr : 0 < r) :
    2 * Real.log (Upper.G r / Upper.G 0) - r * G1 r / Upper.G r ≤ kappaB := by
  set v := r ^ 2 / 2 with hv_def
  set S := Upper.G r with hS_def
  set T := r * G1 r / 2 with hT_def
  have hv : 0 ≤ v := by
    rw [hv_def]
    nlinarith
  have hSpos : 0 < S := by
    rw [hS_def]
    exact G_pos r
  have hb0 : 0 < bco 0 := by
    rw [bco_zero]
    exact Real.exp_pos _
  have hSb0 : S ≤ bco 1 * Real.exp v := by
    rw [hS_def, hv_def]
    exact hasSum_le_exp (bco ·) (bco 1) (r ^ 2 / 2) (Upper.G r)
      (fun n => bco_le_one n) hv (G_hasSum_b r)
  have hTS : v * S - T ≤ (16/15 : ℝ) * S := by
    rw [hv_def, hS_def, hT_def]
    exact shift_bound (bco ·) (r ^ 2 / 2) (16/15 : ℝ) (Upper.G r) (r * G1 r / 2)
      hv (by norm_num) (fun n => bco_nonneg n) (fun n => bco_beta n)
      (G_hasSum_b r) (rG1_hasSum_b r)
  have h_poisson : 2 * Real.log (S / bco 0) - 2 * T / S ≤
      2 * Real.log (bco 1 / bco 0) + 2 * (16/15 : ℝ) := by
    rw [hS_def, hT_def]
    exact poisson_combine S T (bco 1) (bco 0) v (16/15 : ℝ)
      hb0 hSpos hSb0 hTS
  calc
    2 * Real.log (Upper.G r / Upper.G 0) - r * G1 r / Upper.G r
        = 2 * Real.log (S / bco 0) - 2 * T / S := by
      rw [hS_def, hT_def, bco_zero, G_zero]
      ring
    _ ≤ 2 * Real.log (bco 1 / bco 0) + 2 * (16/15 : ℝ) := h_poisson
    _ = kappaB := by
      rw [bco_zero, bco_one, kappaB]

/-- **The scale lemma**, pointwise: `2P(w) - wP'(w) ≤ 2 kappaB`. -/
theorem scale_pointwise {l A : ℝ} (hl : 0 ≤ l) (hA : l + Upper.G 0 ≤ A) {w : ℝ} (hw : 0 < w) :
    2 * (2 * Real.log ((l + Upper.G w) / A)) - w * (2 * G1 w / (l + Upper.G w)) ≤ 2 * kappaB := by
  have hG0 := G_pos 0
  have hGw := G_pos w
  have hlg0 : 0 < l + Upper.G 0 := by linarith
  have hlgw : 0 < l + Upper.G w := by linarith
  have hA0 : 0 < A := by linarith
  have hlogA : Real.log ((l + Upper.G w) / A) ≤ Real.log ((l + Upper.G w) / (l + Upper.G 0)) :=
    Real.log_le_log (div_pos hlgw hA0) (div_le_div_of_nonneg_left hlgw.le hlg0 hA)
  have hred := lam_reduction l (Upper.G w) (Upper.G 0) (w * G1 w) hl hG0 hGw
  have hP := G0_le hw
  have hk := kappaB_nonneg
  have hmax : max (2 * Real.log (Upper.G w / Upper.G 0) - w * G1 w / Upper.G w) 0 ≤ kappaB :=
    max_le (by rw [mul_div_assoc] at hP ⊢; linarith) hk
  have e : w * (2 * G1 w / (l + Upper.G w)) = 2 * (w * G1 w / (l + Upper.G w)) := by ring
  rw [e]
  linarith

theorem hasDerivAt_P {l A : ℝ} (hl : 0 ≤ l) (hA : 0 < A) (w : ℝ) :
    HasDerivAt (fun v => 2 * Real.log ((l + Upper.G v) / A)) (2 * G1 w / (l + Upper.G w)) w := by
  have hGpos : 0 < Upper.G w := G_pos w
  have hpos : (l + Upper.G w) / A ≠ 0 := by
    have : 0 < l + Upper.G w := by linarith
    have : 0 < (l + Upper.G w) / A := div_pos this hA
    linarith
  have h_deriv : HasDerivAt (fun v : ℝ => (l + Upper.G v) / A) (G1 w / A) w := by
    have hG : HasDerivAt Upper.G (G1 w) w := hasDerivAt_G w
    have h_add : HasDerivAt (fun v : ℝ => l + Upper.G v) (G1 w) w :=
      HasDerivAt.const_add l hG
    exact HasDerivAt.div_const h_add A
  have h_log : HasDerivAt (fun v : ℝ => Real.log ((l + Upper.G v) / A)) ((G1 w / A) / ((l + Upper.G w) / A)) w :=
    HasDerivAt.log h_deriv hpos
  have h_simp : (G1 w / A) / ((l + Upper.G w) / A) = G1 w / (l + Upper.G w) := by
    field_simp [hA.ne.symm]
  have h_log_simp : HasDerivAt (fun v : ℝ => Real.log ((l + Upper.G v) / A)) (G1 w / (l + Upper.G w)) w := by
    simpa [h_simp] using h_log
  have h_mul : HasDerivAt (fun v : ℝ => 2 * Real.log ((l + Upper.G v) / A)) (2 * (G1 w / (l + Upper.G w))) w :=
    HasDerivAt.const_mul 2 h_log_simp
  simpa [mul_div_assoc] using h_mul

/-- **The scale lemma**: `m² P(r/m) - P(r) ≤ kappaB (m² - 1)` for `m ≥ 1`. -/
theorem scale_lemma {l A : ℝ} (hl : 0 ≤ l) (hA : l + Upper.G 0 ≤ A) (r : ℝ) {m : ℝ} (hm : 1 ≤ m) :
    m ^ 2 * (2 * Real.log ((l + Upper.G (r / m)) / A)) - 2 * Real.log ((l + Upper.G r) / A) ≤
      kappaB * (m ^ 2 - 1) := by
  have hA0 : 0 < A := by have := G_pos 0; linarith
  have hpos : ∀ s : ℝ, 0 < s →
      m ^ 2 * (2 * Real.log ((l + Upper.G (s / m)) / A)) - 2 * Real.log ((l + Upper.G s) / A) ≤
        kappaB * (m ^ 2 - 1) := fun s hs =>
    scale_abstract (fun v => 2 * Real.log ((l + Upper.G v) / A))
      (fun w => 2 * G1 w / (l + Upper.G w)) kappaB s m (fun w _ => hasDerivAt_P hl hA0 w)
      (fun w hw => scale_pointwise hl hA hw) hs hm
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have h := hpos (-r) (by linarith)
    rwa [neg_div, Upper.G_neg, Upper.G_neg] at h
  · subst hr
    rw [zero_div]
    have h1 : (l + Upper.G 0) / A ≤ 1 := (div_le_one hA0).2 hA
    have h0 : 0 < (l + Upper.G 0) / A := div_pos (by have := G_pos 0; linarith) hA0
    have hlog : Real.log ((l + Upper.G 0) / A) ≤ 0 := Real.log_nonpos h0.le h1
    have hm2 : 0 ≤ m ^ 2 - 1 := by nlinarith
    have := kappaB_nonneg
    nlinarith [mul_nonneg hm2 this, mul_nonneg hm2 (neg_nonneg.2 hlog)]
  · exact hpos r hr

end RegretKappa.UnknownBT.UB
