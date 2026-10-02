import RegretKappa.UpperSharp.Moments
import RegretKappa.Upper.Gamma

/-!
# Theorem 3.1 with the paper's constants: the moments of the weight and the derivative of `g`

In the units of the library `Upper` (`G = Γ/2`). The paper's Lemma A.1 (b) to (d), in the form the
large steps use:

* `Mw j = ∫_1^∞ θ^{2j} wt(θ) dθ`, half the paper's `Γ_j`, in closed form from `e^{-1/2}` and `K0`
  (`Mw_one`, `Mw_add_two`, `mom_odd`), with `Mw (n + 1) ≤ 2^{n+1} n!` (`Mw_le`) and the coefficient
  bound `(n + 1) Mw (n + 1)/(2n + 2)! ≤ 1/(n + 1)!` (`coeff_le`);
* `Dg Y = ∫_1^∞ θ sinh(θ√Y)/(2√Y) wt(θ) dθ`, half the derivative of `g(Y) = Γ(√Y)`, equal to
  `∑_n (n + 1) Y^n Mw (n + 1)/(2n + 2)!` (`Dg_hasSum`, the interchange of the series and the
  integral), nondecreasing (`Dg_mono`), and bounded by the series truncated at `30` plus a geometric
  tail (`Dg_le`);
* the convexity of `g`: `G √Y - G √X ≤ (Y - X) Dg Y` for `0 ≤ X ≤ Y` (`G_sqrt_sub_le`).
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set Finset Filter Topology

/-- `k_1 = 1`, `k_{m+1} = 1 + 2 m k_m` (so that `mom (2m - 1) = e^{-1/2} k_m`). -/
def kk : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (m + 1) => 1 + 2 * m * kk m

/-- The moments of the weight: `∫_1^∞ θ^{2j} wt(θ) dθ` (half of the paper's `Γ_j`). -/
noncomputable def Mw (j : ℕ) : ℝ := ∫ θ in Ioi 1, θ ^ (2 * j) * Upper.wt θ

/-- Half the derivative of `g(Y) = Γ(√Y)`: `∫_1^∞ θ sinh(θ√Y)/(2√Y) wt(θ) dθ`. -/
noncomputable def Dg (Y : ℝ) : ℝ := ∫ θ in Ioi 1, θ * sinh (θ * √Y) / (2 * √Y) * Upper.wt θ

/-- The paper's `Γ_n` from `E = e^{-1/2}` and `K = K_0`: `Γ_1 = 2E + 4K`,
`Γ_n = 2E (k_n + 2 k_{n-1})` for `n ≥ 2`. -/
noncomputable def GamC (E K : ℝ) (n : ℕ) : ℝ :=
  if n = 1 then 2 * E + 4 * K else 2 * E * ((kk n : ℝ) + 2 * kk (n - 1))

/-- The series of `g'` (paper units) truncated at `N`: `∑_{n=1}^N n Γ_n x^{n-1} / (2n)!`. -/
noncomputable def gpN (E K : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) * GamC E K (n + 1) * x ^ n / ((2 * (n + 1)).factorial : ℝ)

/-- The tail bound (paper units) `2 x^N / ((N+1)! (1 - x/(N+2)))`. -/
noncomputable def tailN (N : ℕ) (x : ℝ) : ℝ :=
  2 * x ^ N / (((N + 1).factorial : ℝ) * (1 - x / (N + 2)))

/-! ### Leaves -/

theorem integrableOn_pow_exp (k : ℕ) :
    IntegrableOn (fun θ : ℝ => θ ^ k * exp (-θ ^ 2 / 2)) (Ioi 1) := by
  have hb : 0 < (1/2 : ℝ) := by norm_num
  have hs : -1 < (k : ℝ) := by
    have : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have h_int : Integrable (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb hs
  have h_on : IntegrableOn (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ 2)) (Ioi 1) :=
    h_int.integrableOn
  have h_meas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
  refine h_on.congr_fun ?_ h_meas
  intro x hx
  have hxpos : 0 < x := by
    have : 1 < x := hx
    linarith
  calc
    x ^ (k : ℝ) * Real.exp (-(1/2 : ℝ) * x ^ 2) = x ^ k * Real.exp (-(1/2 : ℝ) * x ^ 2) := by
      simp [Real.rpow_natCast]
    _ = x ^ k * Real.exp (-x ^ 2 / 2) := by ring_nf

theorem integrableOn_pow_cosh_wt (p : ℕ) (r : ℝ) :
    IntegrableOn (fun θ : ℝ => θ ^ p * cosh (θ * r) * Upper.wt θ) (Ioi 1) := by
  have hcw : ∀ θ : ℝ, 1 < θ → cosh (θ * r) * Upper.wt θ ≤ 3 * exp (r ^ 2) * exp (-θ ^ 2 / 4) := by
    intro θ hθ
    have hθ0 : 0 < θ := by linarith
    have h1 : cosh (θ * r) ≤ exp (|θ * r|) := Upper.cosh_le_exp_abs_u _
    have h2 : Upper.wt θ ≤ 3 * exp (-θ ^ 2 / 2) := Upper.wt_le hθ.le
    have h3 : |θ * r| - θ ^ 2 / 2 ≤ r ^ 2 - θ ^ 2 / 4 := by
      rw [abs_mul, abs_of_pos hθ0]
      nlinarith [sq_nonneg (θ / 2 - |r|), sq_abs r]
    calc cosh (θ * r) * Upper.wt θ ≤ exp (|θ * r|) * (3 * exp (-θ ^ 2 / 2)) :=
          mul_le_mul h1 h2 (Upper.wt_pos hθ0).le (exp_pos _).le
      _ = 3 * exp (|θ * r| - θ ^ 2 / 2) := by rw [sub_eq_add_neg, exp_add]; ring_nf
      _ ≤ 3 * exp (r ^ 2 - θ ^ 2 / 4) := by gcongr
      _ = 3 * exp (r ^ 2) * exp (-θ ^ 2 / 4) := by rw [sub_eq_add_neg, exp_add]; ring_nf
  have hpow : ∀ θ : ℝ, 1 < θ → θ ^ p ≤ 8 ^ p * (p.factorial : ℝ) * exp (θ ^ 2 / 8) := by
    intro θ hθ
    have h1 : θ ^ p ≤ θ ^ (2 * p) := pow_le_pow_right₀ hθ.le (by omega)
    have h2 := Real.pow_div_factorial_le_exp (x := θ ^ 2 / 8) (by positivity) p
    have hf : (0 : ℝ) < (p.factorial : ℝ) := by positivity
    rw [div_le_iff₀ hf, div_pow] at h2
    have h8 : (0 : ℝ) < 8 ^ p := by positivity
    have e : θ ^ (2 * p) = (θ ^ 2) ^ p := by rw [pow_mul]
    calc θ ^ p ≤ (θ ^ 2) ^ p := e ▸ h1
      _ = 8 ^ p * ((θ ^ 2) ^ p / 8 ^ p) := by field_simp
      _ ≤ 8 ^ p * (exp (θ ^ 2 / 8) * (p.factorial : ℝ)) := by gcongr
      _ = 8 ^ p * (p.factorial : ℝ) * exp (θ ^ 2 / 8) := by ring
  refine Upper.integrableOn_Ioi_of_le_gauss (M := 8 ^ p * (p.factorial : ℝ) * (3 * exp (r ^ 2)))
    (by norm_num : (0 : ℝ) < 1 / 8) ?_ fun θ hθ => ?_
  · have hw : ContinuousOn Upper.wt (Ioi 1) := by
      unfold Upper.wt
      refine ContinuousOn.mul (by fun_prop) (ContinuousOn.add ?_ ?_)
      · exact continuousOn_const.div continuousOn_id fun θ hθ => (lt_trans one_pos hθ).ne'
      · exact continuousOn_const.div (continuousOn_id.pow 3) fun θ hθ =>
          pow_ne_zero 3 (lt_trans one_pos hθ).ne'
    exact ContinuousOn.mul (by fun_prop) hw
  · have hθ : 1 < θ := hθ
    have hθ0 : 0 < θ := by linarith
    have hnn : 0 ≤ θ ^ p * cosh (θ * r) * Upper.wt θ :=
      mul_nonneg (mul_nonneg (pow_nonneg hθ0.le _) (cosh_pos _).le) (Upper.wt_pos hθ0).le
    rw [abs_of_nonneg hnn, mul_assoc]
    have hc0 : 0 ≤ cosh (θ * r) * Upper.wt θ := mul_nonneg (cosh_pos _).le (Upper.wt_pos hθ0).le
    calc θ ^ p * (cosh (θ * r) * Upper.wt θ)
        ≤ (8 ^ p * (p.factorial : ℝ) * exp (θ ^ 2 / 8)) * (3 * exp (r ^ 2) * exp (-θ ^ 2 / 4)) :=
          mul_le_mul (hpow θ hθ) (hcw θ hθ) hc0 (by positivity)
      _ = 8 ^ p * (p.factorial : ℝ) * (3 * exp (r ^ 2)) * (exp (θ ^ 2 / 8) * exp (-θ ^ 2 / 4)) := by ring
      _ = 8 ^ p * (p.factorial : ℝ) * (3 * exp (r ^ 2)) * exp (-(1 / 8) * θ ^ 2) := by
          rw [← exp_add]; ring_nf

theorem hasSum_sinh_div (θ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n / ((2 * n + 2).factorial : ℝ))
      (θ * sinh (θ * √Y) / (2 * √Y)) := by
  have hsinh := Real.hasSum_sinh (θ * √Y)
  have h_mul : HasSum (fun n : ℕ => (θ / (2 * √Y)) * ((θ * √Y) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)))
      ((θ / (2 * √Y)) * sinh (θ * √Y)) :=
    hsinh.mul_left (θ / (2 * √Y))
  have h_target_eq : (θ / (2 * √Y)) * sinh (θ * √Y) = θ * sinh (θ * √Y) / (2 * √Y) := by
    ring
  rw [h_target_eq] at h_mul
  refine h_mul.congr_fun ?_
  intro n
  have hYpos' : √Y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hY)
  have h_fact1 : ((2 * n + 1).factorial : ℝ) ≠ 0 := by exact mod_cast Nat.factorial_ne_zero _
  have h_fact_eq : ((2 * n + 2).factorial : ℝ) = (2 * (n : ℝ) + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  calc
    ((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n / ((2 * n + 2).factorial : ℝ)
        = ((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n / ((2 * (n : ℝ) + 2) * ((2 * n + 1).factorial : ℝ)) := by
      rw [h_fact_eq]
    _ = θ ^ (2 * n + 2) * Y ^ n / (2 * ((2 * n + 1).factorial : ℝ)) := by
      field_simp [h_fact1]
    _ = (θ / (2 * √Y)) * ((θ * √Y) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
      field_simp [hYpos', h_fact1]
      have h_sqY : (√Y) ^ 2 = Y := Real.sq_sqrt (by linarith)
      calc
        θ ^ (2 * n + 2) * Y ^ n * √Y
            = θ ^ (2 * n + 2) * ((√Y) ^ 2) ^ n * √Y := by rw [h_sqY]
        _ = θ ^ (2 * n + 2) * (√Y) ^ (2 * n) * √Y := by rw [← pow_mul]
        _ = θ ^ (2 * n + 2) * ((√Y) ^ (2 * n) * √Y) := by ring
        _ = θ ^ (2 * n + 2) * (√Y) ^ (2 * n + 1) := by rw [← pow_succ]
        _ = (θ ^ (2 * n + 1) * θ) * (√Y) ^ (2 * n + 1) := by rw [pow_succ]
        _ = θ * (θ ^ (2 * n + 1) * (√Y) ^ (2 * n + 1)) := by ring
        _ = θ * (θ * √Y) ^ (2 * n + 1) := by rw [mul_pow]


theorem pow_succ_sub_pow_le (n : ℕ) {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    Y ^ (n + 1) - X ^ (n + 1) ≤ ((n : ℝ) + 1) * Y ^ n * (Y - X) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hY : 0 ≤ Y := le_trans hX hXY
      have hsub : 0 ≤ Y - X := sub_nonneg.mpr hXY
      have hpow : X ^ (n + 1) ≤ Y ^ (n + 1) :=
        pow_le_pow_left₀ hX hXY (n + 1)
      have hpos : 0 ≤ Y ^ (n + 1) := pow_nonneg hY (n + 1)
      have h_eq : Y ^ (n + 2) - X ^ (n + 2) = Y * (Y ^ (n + 1) - X ^ (n + 1)) + X ^ (n + 1) * (Y - X) := by
        rw [pow_succ, pow_succ]
        ring_nf
      have h1 : Y * (Y ^ (n + 1) - X ^ (n + 1)) ≤ Y * (((n : ℝ) + 1) * Y ^ n * (Y - X)) :=
        mul_le_mul_of_nonneg_left ih hY
      have h2 : X ^ (n + 1) * (Y - X) ≤ Y ^ (n + 1) * (Y - X) :=
        mul_le_mul_of_nonneg_right hpow hsub
      have h_sum : ((n : ℝ) + 1) * Y ^ (n + 1) * (Y - X) + Y ^ (n + 1) * (Y - X) =
        (((n : ℝ) + 1) + 1) * Y ^ (n + 1) * (Y - X) := by
        ring_nf
      have h_mul : Y * (((n : ℝ) + 1) * Y ^ n * (Y - X)) = ((n : ℝ) + 1) * Y ^ (n + 1) * (Y - X) := by
        simp [mul_assoc, mul_comm, mul_left_comm, pow_succ Y n]
      have h_temp : Y * (((n : ℝ) + 1) * Y ^ n * (Y - X)) + Y ^ (n + 1) * (Y - X) =
        ((n : ℝ) + 1) * Y ^ (n + 1) * (Y - X) + Y ^ (n + 1) * (Y - X) := by
        rw [h_mul]
      calc
        Y ^ (n + 2) - X ^ (n + 2) = Y * (Y ^ (n + 1) - X ^ (n + 1)) + X ^ (n + 1) * (Y - X) := h_eq
        _ ≤ Y * (((n : ℝ) + 1) * Y ^ n * (Y - X)) + Y ^ (n + 1) * (Y - X) :=
          add_le_add h1 h2
        _ = ((n : ℝ) + 1) * Y ^ (n + 1) * (Y - X) + Y ^ (n + 1) * (Y - X) := h_temp
        _ = (((n : ℝ) + 1) + 1) * Y ^ (n + 1) * (Y - X) := h_sum
        _ = ((n : ℝ) + 2) * Y ^ (n + 1) * (Y - X) := by
          rw [show ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 by ring]
        _ = (((n.succ : ℕ) : ℝ) + 1) * Y ^ (n.succ : ℕ) * (Y - X) := by
          push_cast
          rw [show ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 by ring]

theorem cosh_sqrt_sub_le (θ : ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) (hY : 0 < Y) :
    cosh (θ * √Y) - cosh (θ * √X) ≤ (Y - X) * (θ * sinh (θ * √Y) / (2 * √Y)) := by
  have hY' : 0 ≤ Y := le_of_lt hY
  -- Series for cosh
  have hcoshY := Real.hasSum_cosh (θ * √Y)
  have hcoshX := Real.hasSum_cosh (θ * √X)
  -- Difference of series
  have hdiff := hcoshY.sub hcoshX
  -- hdiff : HasSum (fun n => (θ*√Y)^(2*n)/(2*n)! - (θ*√X)^(2*n)/(2*n)!) (cosh(θ√Y) - cosh(θ√X))
  set f := fun n : ℕ => ((θ * √Y) ^ (2 * n) / ((2 * n).factorial : ℝ) - (θ * √X) ^ (2 * n) / ((2 * n).factorial : ℝ)) with hf
  set g := cosh (θ * √Y) - cosh (θ * √X) with hg
  have hf0 : f 0 = 0 := by
    dsimp [f]
    norm_num
  -- Shift index: f 0 = 0, so sum of f equals sum of f ∘ (·+1)
  have hshift : HasSum (fun n => f (n + 1)) g := by
    have := (hasSum_nat_add_iff (f := f) (g := g) 1).mpr ?_
    · exact this
    · -- Need: HasSum f (g + ∑ i ∈ range 1, f i)
      have hsum0 : ∑ i ∈ Finset.range 1, f i = 0 := by
        simp [hf0]
      rw [hsum0, add_zero]
      exact hdiff
  -- hasSum_sinh_div θ hY : HasSum (fun n => ((n:ℝ)+1) * θ^(2*n+2) * Y^n / ((2*n+2).factorial : ℝ)) (θ * sinh (θ * √Y) / (2 * √Y))
  have hsinh := hasSum_sinh_div θ hY
  -- Multiply by (Y-X)
  have hsinh_mul : HasSum (fun n : ℕ => (Y - X) * (((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n / ((2 * n + 2).factorial : ℝ)))
      ((Y - X) * (θ * sinh (θ * √Y) / (2 * √Y))) :=
    HasSum.mul_left (Y - X) hsinh
  -- Apply hasSum_le
  apply hasSum_le ?_ hshift hsinh_mul
  intro n
  -- Need: f (n+1) ≤ (Y-X) * (((n:ℝ)+1) * θ^(2*n+2) * Y^n / ((2*n+2).factorial : ℝ))
  dsimp [f]
  -- Goal: (θ*√Y)^(2*(n+1))/(2*(n+1))! - (θ*√X)^(2*(n+1))/(2*(n+1))! ≤ (Y-X) * (((n:ℝ)+1) * θ^(2*n+2) * Y^n / ((2*n+2).factorial : ℝ))
  -- Rewrite (θ*√Y)^(2*(n+1)) = θ^(2*n+2) * Y^(n+1)
  have hYterm : (θ * √Y) ^ (2 * (n+1)) = θ ^ (2 * (n+1)) * Y ^ (n+1) := by
    calc
      (θ * √Y) ^ (2 * (n+1)) = ((θ * √Y) ^ 2) ^ (n+1) := by rw [pow_mul]
      _ = (θ ^ 2 * (√Y) ^ 2) ^ (n+1) := by rw [mul_pow]
      _ = (θ ^ 2 * Y) ^ (n+1) := by rw [Real.sq_sqrt hY']
      _ = (θ ^ 2) ^ (n+1) * Y ^ (n+1) := by rw [mul_pow]
      _ = θ ^ (2 * (n+1)) * Y ^ (n+1) := by rw [pow_mul]
  have hXterm : (θ * √X) ^ (2 * (n+1)) = θ ^ (2 * (n+1)) * X ^ (n+1) := by
    calc
      (θ * √X) ^ (2 * (n+1)) = ((θ * √X) ^ 2) ^ (n+1) := by rw [pow_mul]
      _ = (θ ^ 2 * (√X) ^ 2) ^ (n+1) := by rw [mul_pow]
      _ = (θ ^ 2 * X) ^ (n+1) := by rw [Real.sq_sqrt hX]
      _ = (θ ^ 2) ^ (n+1) * X ^ (n+1) := by rw [mul_pow]
      _ = θ ^ (2 * (n+1)) * X ^ (n+1) := by rw [pow_mul]
  rw [hYterm, hXterm]
  -- Note: 2*(n+1) = 2*n+2
  have h_fact_eq : ((2*(n+1)).factorial : ℝ) = ((2*n+2).factorial : ℝ) := by
    have h : 2*(n+1) = 2*n+2 := by omega
    simp [h]
  rw [h_fact_eq]
  -- Combine LHS into single fraction
  have h_lhs : θ ^ (2 * (n+1)) * Y ^ (n+1) / ((2*n+2).factorial : ℝ) - θ ^ (2 * (n+1)) * X ^ (n+1) / ((2*n+2).factorial : ℝ) =
      θ ^ (2 * (n+1)) * (Y ^ (n+1) - X ^ (n+1)) / ((2*n+2).factorial : ℝ) := by
    ring
  rw [h_lhs]
  -- Note: 2*(n+1) = 2*n+2
  have h_exp_eq : θ ^ (2 * (n+1)) = θ ^ (2 * n + 2) := by ring
  rw [h_exp_eq]
  -- Now goal: θ^(2n+2) * (Y^(n+1) - X^(n+1)) / D ≤ (Y-X) * ((n+1) * θ^(2n+2) * Y^n / D)
  have h_denom_nonneg : 0 ≤ ((2*n+2).factorial : ℝ) := Nat.cast_nonneg _
  -- Use the bound from pow_succ_sub_pow_le
  have h_bound : Y ^ (n+1) - X ^ (n+1) ≤ ((n : ℝ) + 1) * Y ^ n * (Y - X) := by
    have h := pow_succ_sub_pow_le n hX hXY
    linarith
  have hθ_nonneg : 0 ≤ θ ^ (2 * n + 2) := by
    have : θ ^ (2 * n + 2) = (θ ^ 2) ^ (n + 1) := by
      calc
        θ ^ (2 * n + 2) = θ ^ (2 * (n + 1)) := by ring
        _ = (θ ^ 2) ^ (n + 1) := by rw [pow_mul]
    rw [this]
    apply pow_nonneg
    nlinarith [sq_nonneg θ]
  -- Combine to get numerator inequality
  have h_num : θ ^ (2 * n + 2) * (Y ^ (n+1) - X ^ (n+1)) ≤ (Y - X) * (((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n) := by
    nlinarith
  calc
    θ ^ (2 * n + 2) * (Y ^ (n+1) - X ^ (n+1)) / ((2*n+2).factorial : ℝ)
        ≤ ((Y - X) * (((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n)) / ((2*n+2).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right h_num h_denom_nonneg
    _ = (Y - X) * (((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n / ((2*n+2).factorial : ℝ)) := by ring

theorem sinh_div_le {θ Y : ℝ} (hθ : 0 ≤ θ) (hY : 0 < Y) :
    0 ≤ θ * sinh (θ * √Y) / (2 * √Y) ∧ θ * sinh (θ * √Y) / (2 * √Y) ≤ θ ^ 2 * cosh (θ * √Y) / 2 := by
  set z := θ * √Y with hz_def
  have hz : 0 ≤ z := mul_nonneg hθ (Real.sqrt_nonneg Y)
  have h_sqrtY_pos : 0 < √Y := Real.sqrt_pos.mpr hY
  have h_denom_pos : 0 < 2 * √Y := by nlinarith
  have h_sinh_nonneg : 0 ≤ sinh z := (Real.sinh_nonneg_iff.mpr hz)
  have h_nonneg : 0 ≤ θ * sinh (θ * √Y) / (2 * √Y) := by
    refine div_nonneg ?_ (by positivity)
    exact mul_nonneg hθ h_sinh_nonneg
  have h_upper : θ * sinh (θ * √Y) / (2 * √Y) ≤ θ ^ 2 * cosh (θ * √Y) / 2 := by
    by_cases hθ0 : θ = 0
    · subst hθ0; simp
    · have hθ_pos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
      have h_sinh_le : sinh z ≤ z * cosh z := by
        set f := fun t : ℝ => t * cosh t - sinh t with hf_def
        have hf0 : f 0 = 0 := by simp [f]
        have h_deriv : ∀ t, HasDerivAt f (t * sinh t) t := by
          intro t
          have h := ((hasDerivAt_id t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)
          -- h : HasDerivAt ((id * cosh) - sinh) ((1 * cosh t + id t * sinh t) - cosh t) t
          convert h using 1
          · ext x; simp [f, id, mul_comm]
          · simp [id]
        have h_deriv_nonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ t * sinh t := by
          intro t ht
          have ht' : 0 ≤ t := le_of_lt ht
          have hsinh_nonneg : 0 ≤ sinh t := (Real.sinh_nonneg_iff.mpr ht')
          exact mul_nonneg ht' hsinh_nonneg
        have h_mono : MonotoneOn f (Set.Ici 0) := by
          refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => t * sinh t) ?_ ?_ ?_
          · refine (Continuous.sub ?_ ?_).continuousOn
            · exact (continuous_id.mul continuous_cosh)
            · exact continuous_sinh
          · intro t ht
            have h_deriv_at : HasDerivAt f (t * sinh t) t := h_deriv t
            exact h_deriv_at.hasDerivWithinAt
          · rw [interior_Ici]
            exact h_deriv_nonneg
        have hz_mem : z ∈ Set.Ici 0 := hz
        have h0_mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
        have h_fz_ge_f0 : f 0 ≤ f z := h_mono h0_mem hz_mem hz
        rw [hf0] at h_fz_ge_f0
        dsimp [f] at h_fz_ge_f0
        linarith
      have h_eq : θ ^ 2 * cosh (θ * √Y) / 2 - θ * sinh (θ * √Y) / (2 * √Y) =
          (θ / (2 * √Y)) * (z * cosh z - sinh z) := by
        dsimp [z]
        field_simp [show √Y ≠ 0 from by positivity]
      have h_nonneg_diff : 0 ≤ θ ^ 2 * cosh (θ * √Y) / 2 - θ * sinh (θ * √Y) / (2 * √Y) := by
        rw [h_eq]
        refine mul_nonneg ?_ ?_
        · refine div_nonneg hθ (by positivity)
        · linarith
      linarith
  exact And.intro h_nonneg h_upper


theorem half_pow_two_pow (m : ℕ) : ((1/2 : ℝ) ^ m) * ((2 : ℝ) ^ m) = 1 := by
  calc
    (1/2 : ℝ) ^ m * (2 : ℝ) ^ m = ((1/2 : ℝ) * (2 : ℝ)) ^ m := by rw [mul_pow]
    _ = (1 : ℝ) ^ m := by ring
    _ = 1 := by simp

theorem kk_closed_form (m : ℕ) : (kk (m + 1) : ℝ) = (2 ^ m : ℝ) * (m.factorial : ℝ) *
    (∑ j ∈ Finset.range (m + 1), ((1/2 : ℝ) ^ j / (j.factorial : ℝ))) := by
  induction' m with m ih
  · simp [kk]
  · have hkk : (kk ((m + 1) + 1) : ℝ) = 1 + 2 * ((m : ℝ) + 1) * (kk (m + 1) : ℝ) := by
      simp [kk]
    rw [hkk, ih]
    have hsum : (∑ j ∈ Finset.range ((m + 1) + 1), ((1/2 : ℝ) ^ j / (j.factorial : ℝ))) =
        (∑ j ∈ Finset.range (m + 1), ((1/2 : ℝ) ^ j / (j.factorial : ℝ))) + ((1/2 : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by
      simp [Finset.sum_range_succ]
    rw [hsum]
    have hfact : ((m + 1 : ℕ).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      simp [Nat.factorial_succ]
    rw [hfact]
    field_simp
    ring_nf
    rw [half_pow_two_pow m]
    ring

theorem kk_le (m : ℕ) : exp (-1 / 2) * (kk (m + 1) : ℝ) ≤ 2 ^ m * (m.factorial : ℝ) := by
  rw [kk_closed_form m]
  set s := ∑ j ∈ Finset.range (m + 1), ((1/2 : ℝ) ^ j / (j.factorial : ℝ)) with hs
  have hsum_le : s ≤ Real.exp (1/2) := by
    rw [hs]
    have hx : 0 ≤ (1/2 : ℝ) := by norm_num
    simpa using Real.sum_le_exp_of_nonneg hx (m + 1)
  have h_exp_prod : Real.exp (-1/2) * Real.exp (1/2) = 1 := by
    calc
      Real.exp (-1/2) * Real.exp (1/2) = Real.exp ((-1/2) + (1/2)) := by rw [Real.exp_add]
      _ = Real.exp 0 := by ring_nf
      _ = 1 := by simp
  have h_nonneg : 0 ≤ (2 : ℝ) ^ m * (m.factorial : ℝ) := by
    positivity
  have h_exp_nonneg : 0 ≤ Real.exp (-1/2) := (Real.exp_pos _).le
  have h_mul : Real.exp (-1/2) * s ≤ Real.exp (-1/2) * Real.exp (1/2) := by
    exact mul_le_mul_of_nonneg_left hsum_le h_exp_nonneg
  calc
    Real.exp (-1/2) * ((2 : ℝ) ^ m * (m.factorial : ℝ) * s)
        = ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (Real.exp (-1/2) * s) := by ring
    _ ≤ ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (Real.exp (-1/2) * Real.exp (1/2)) := by
      exact mul_le_mul_of_nonneg_left h_mul h_nonneg
    _ = ((2 : ℝ) ^ m * (m.factorial : ℝ)) * 1 := by rw [h_exp_prod]
    _ = (2 : ℝ) ^ m * (m.factorial : ℝ) := by ring

theorem mom_odd (m : ℕ) : mom (2 * m + 1) = exp (-1 / 2) * (kk (m + 1) : ℝ) := by
  induction' m with m ih
  · -- m = 0
    simp [kk, mom_one]
  · -- m → m+1
    have h := mom_add_two (2 * m + 1)
    calc
      mom (2 * (m + 1) + 1) = mom ((2 * m + 1) + 2) := by
        congr 1
      _ = exp (-1 / 2) + ((2 * m + 1) + 1 : ℝ) * mom (2 * m + 1) := by
        simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_assoc] using h
      _ = exp (-1 / 2) + (2 * (m : ℝ) + 2) * mom (2 * m + 1) := by
        have htemp : ((2 * m + 1) + 1 : ℝ) = (2 * (m : ℝ) + 2) := by
          ring
        rw [htemp]
      _ = exp (-1 / 2) + (2 * (m : ℝ) + 2) * (exp (-1 / 2) * (kk (m + 1) : ℝ)) := by rw [ih]
      _ = exp (-1 / 2) * (1 + (2 * (m : ℝ) + 2) * (kk (m + 1) : ℝ)) := by ring
      _ = exp (-1 / 2) * (kk (m + 2) : ℝ) := by
        have hk : kk (m + 2) = 1 + 2 * (m + 1) * kk (m + 1) := by
          simp [kk]
        have hk' : (kk (m + 2) : ℝ) = 1 + 2 * ((m : ℝ) + 1) * (kk (m + 1) : ℝ) := by
          simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using congrArg (fun x : ℕ => (x : ℝ)) hk
        rw [hk']
        ring

theorem Mw_one : Mw 1 = mom 1 + 2 * K0 := by
  unfold Mw mom K0 RegretKappa.Upper.wt
  simp
  have h_eq : ∀ θ, θ ∈ Ioi (1 : ℝ) → θ ^ 2 * (exp (-θ ^ 2 / 2) * (θ⁻¹ + 2 / θ ^ 3)) =
      (θ * exp (-θ ^ 2 / 2)) + 2 * (exp (-θ ^ 2 / 2) / θ) := by
    intro θ hθ
    have hθpos : θ ≠ 0 := by
      have : (1 : ℝ) < θ := hθ
      linarith
    field_simp [hθpos]
  have h_int1 : IntegrableOn (fun θ : ℝ => θ * exp (-θ ^ 2 / 2)) (Ioi 1) := by
    simpa using integrableOn_pow_exp 1
  have h_int2 : IntegrableOn (fun θ : ℝ => exp (-θ ^ 2 / 2) / θ) (Ioi 1) := integrableOn_K0
  have h_congr : ∫ θ in Ioi 1, θ ^ 2 * (exp (-θ ^ 2 / 2) * (θ⁻¹ + 2 / θ ^ 3)) =
      ∫ θ in Ioi 1, ((θ * exp (-θ ^ 2 / 2)) + 2 * (exp (-θ ^ 2 / 2) / θ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi h_eq
  calc
    ∫ θ in Ioi 1, θ ^ 2 * (exp (-θ ^ 2 / 2) * (θ⁻¹ + 2 / θ ^ 3))
        = ∫ θ in Ioi 1, ((θ * exp (-θ ^ 2 / 2)) + 2 * (exp (-θ ^ 2 / 2) / θ)) := h_congr
    _ = (∫ θ in Ioi 1, θ * exp (-θ ^ 2 / 2)) + (∫ θ in Ioi 1, 2 * (exp (-θ ^ 2 / 2) / θ)) := by
      rw [integral_add h_int1 (h_int2.const_mul 2)]
    _ = (∫ θ in Ioi 1, θ * exp (-θ ^ 2 / 2)) + 2 * (∫ θ in Ioi 1, exp (-θ ^ 2 / 2) / θ) := by
      rw [integral_const_mul 2 (fun θ => exp (-θ ^ 2 / 2) / θ)]

theorem Mw_add_two (j : ℕ) : Mw (j + 2) = mom (2 * j + 3) + 2 * mom (2 * j + 1) := by
  unfold Mw mom Upper.wt
  have hint_eq : (fun (θ : ℝ) => θ ^ (2 * (j + 2)) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))) =
      (fun (θ : ℝ) => θ ^ (2 * j + 3) * exp (-θ ^ 2 / 2) + 2 * θ ^ (2 * j + 1) * exp (-θ ^ 2 / 2)) := by
    ext θ
    by_cases hθ0 : θ = 0
    · subst θ; simp
    · field_simp [hθ0]
      ring
  calc
    ∫ θ in Ioi 1, θ ^ (2 * (j + 2)) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))
        = ∫ θ in Ioi 1, (θ ^ (2 * j + 3) * exp (-θ ^ 2 / 2) + 2 * θ ^ (2 * j + 1) * exp (-θ ^ 2 / 2)) := by
      rw [hint_eq]
    _ = (∫ θ in Ioi 1, θ ^ (2 * j + 3) * exp (-θ ^ 2 / 2)) +
        (∫ θ in Ioi 1, 2 * θ ^ (2 * j + 1) * exp (-θ ^ 2 / 2)) := by
      rw [integral_add (integrableOn_pow_exp (2 * j + 3)) ?_]
      · have h := (integrableOn_pow_exp (2 * j + 1)).const_mul 2
        simpa [mul_assoc] using h
    _ = (∫ θ in Ioi 1, θ ^ (2 * j + 3) * exp (-θ ^ 2 / 2)) +
        2 * (∫ θ in Ioi 1, θ ^ (2 * j + 1) * exp (-θ ^ 2 / 2)) := by
      simp [integral_const_mul (2 : ℝ) (fun θ => θ ^ (2 * j + 1) * exp (-θ ^ 2 / 2)), mul_assoc]
    _ = mom (2 * j + 3) + 2 * mom (2 * j + 1) := by
      unfold mom
      ring

theorem two_pow_factorial_sq_le (n : ℕ) : 2 ^ n * n.factorial ^ 2 ≤ (2 * n).factorial := by
  induction' n with n ih
  · simp
  · have hineq : 2 * (n + 1) ^ 2 ≤ (2 * n + 2) * (2 * n + 1) := by
      nlinarith
    calc
      2 ^ (n + 1) * (n + 1).factorial ^ 2
          = (2 * 2 ^ n) * ((n + 1) * n.factorial) ^ 2 := by
            simp [Nat.factorial_succ, pow_succ, mul_comm]
      _ = 2 * (n + 1) ^ 2 * (2 ^ n * n.factorial ^ 2) := by ring
      _ ≤ 2 * (n + 1) ^ 2 * (2 * n).factorial :=
            Nat.mul_le_mul_left _ ih
      _ ≤ (2 * n + 2) * (2 * n + 1) * (2 * n).factorial :=
            Nat.mul_le_mul_right _ hineq
      _ = (2 * (n + 1)).factorial := by
            rw [show (2 * (n + 1)) = 2 * n + 2 by omega]
            rw [Nat.factorial_succ, Nat.factorial_succ]
            ring


theorem factorial_mul_pow_le_factorial_add (N n : ℕ) :
    ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ n) ≤ ((N+n+1).factorial : ℝ) := by
  induction' n with k ih
  · norm_num
  · have h_eq : ((N+(k+1)+1).factorial : ℝ) = ((N+k+1).factorial : ℝ) * (N+k+2 : ℝ) := by
      rw [show (N+(k+1)+1 : ℕ) = (N+k+1)+1 by omega]
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [h_eq, pow_succ]
    -- Goal: ↑(N+1)! * ((↑N+2)^k * (↑N+2)) ≤ ↑(N+k+1)! * (↑N+↑k+2)
    rw [← mul_assoc]
    -- Goal: (↑(N+1)! * (↑N+2)^k) * (↑N+2) ≤ ↑(N+k+1)! * (↑N+↑k+2)
    have h_ineq1 : ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ k) * (N+2 : ℝ) ≤
        ((N+k+1).factorial : ℝ) * (N+2 : ℝ) := by
      nlinarith
    have h_ineq2 : ((N+k+1).factorial : ℝ) * (N+2 : ℝ) ≤
        ((N+k+1).factorial : ℝ) * (N+k+2 : ℝ) := by
      have h_le : (N+2 : ℝ) ≤ (N+k+2 : ℝ) := by
        exact mod_cast (show N+2 ≤ N+k+2 from by omega)
      nlinarith
    nlinarith

theorem sum_tail_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (hxN : x < N + 2) (M : ℕ) :
    ∑ n ∈ range M, x ^ (N + n) / ((N + n + 1).factorial : ℝ) ≤
      x ^ N / (((N + 1).factorial : ℝ) * (1 - x / (N + 2))) := by
  set q := x / (N + 2 : ℝ) with hq
  have hNpos : 0 < (N : ℝ) + 2 := by
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hq_nonneg : 0 ≤ q := div_nonneg hx (by nlinarith)
  have hq_lt_one : q < 1 := by
    rw [hq]
    exact (div_lt_one hNpos).mpr hxN
  have h_term (n : ℕ) : x ^ (N + n) / ((N + n + 1).factorial : ℝ) ≤
      x ^ N / ((N + 1).factorial : ℝ) * q ^ n := by
    rw [hq]
    have h_fact : ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ n) ≤ ((N+n+1).factorial : ℝ) :=
      factorial_mul_pow_le_factorial_add N n
    have h_denom1_pos : 0 < ((N+n+1).factorial : ℝ) :=
      mod_cast Nat.factorial_pos (N+n+1)
    have h_denom2_pos : 0 < ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ n) := by
      positivity
    -- RHS = x^N/(N+1)! * (x/(N+2))^n = x^(N+n) / ((N+1)! * (N+2)^n)
    -- LHS = x^(N+n) / (N+n+1)!
    -- So we need: x^(N+n) / (N+n+1)! ≤ x^(N+n) / ((N+1)! * (N+2)^n)
    -- which follows from (N+n+1)! ≥ (N+1)! * (N+2)^n
    have h_rhs : x ^ N / ((N + 1).factorial : ℝ) * ((x / (N + 2)) ^ n) =
        x ^ (N + n) / (((N + 1).factorial : ℝ) * ((N + 2 : ℝ) ^ n)) := by
      rw [div_pow]
      ring
    rw [h_rhs]
    rw [div_le_div_iff₀ h_denom1_pos h_denom2_pos]
    have h_pow_nonneg : 0 ≤ x ^ (N + n) := pow_nonneg hx (N + n)
    nlinarith
  have h_geom : ∑ n ∈ range M, q ^ n ≤ (1 - q)⁻¹ := by
    -- Use geom_sum_Ico_le_of_lt_one which works for ℝ
    have h := geom_sum_Ico_le_of_lt_one hq_nonneg hq_lt_one (m := 0) (n := M)
    -- h : ∑ i ∈ Ico 0 M, q ^ i ≤ q ^ 0 / (1 - q)
    -- q^0 = 1, and Ico 0 M = range M
    rw [← range_eq_Ico] at h
    rw [pow_zero] at h
    -- h : ∑ n ∈ range M, q ^ n ≤ 1 / (1 - q)
    simpa [div_eq_inv_mul] using h
  calc
    ∑ n ∈ range M, x ^ (N + n) / ((N + n + 1).factorial : ℝ) ≤
        ∑ n ∈ range M, (x ^ N / ((N + 1).factorial : ℝ) * q ^ n) :=
      Finset.sum_le_sum fun i hi => h_term i
    _ = (x ^ N / ((N + 1).factorial : ℝ)) * (∑ n ∈ range M, q ^ n) := by
      rw [Finset.mul_sum]
    _ ≤ (x ^ N / ((N + 1).factorial : ℝ)) * ((1 - q)⁻¹) := by
      gcongr
    _ = x ^ N / (((N + 1).factorial : ℝ) * (1 - x / (N + 2))) := by
      rw [hq]
      field_simp

/-! ### The moments of the weight -/

theorem integrableOn_pow_wt (p : ℕ) : IntegrableOn (fun θ : ℝ => θ ^ p * Upper.wt θ) (Ioi 1) := by
  have h := integrableOn_pow_cosh_wt p 0
  simp only [mul_zero, cosh_zero, mul_one] at h
  exact h

theorem Mw_nonneg (j : ℕ) : 0 ≤ Mw j :=
  setIntegral_nonneg measurableSet_Ioi fun _ hθ =>
    mul_nonneg (pow_nonneg (lt_trans one_pos hθ).le _) (Upper.wt_pos (lt_trans one_pos hθ)).le

theorem K0_nonneg : 0 ≤ K0 :=
  setIntegral_nonneg measurableSet_Ioi fun _ hθ =>
    div_nonneg (exp_pos _).le (lt_trans one_pos hθ).le

/-- `Mw n` is half the paper's `Γ_n`, in closed form. -/
theorem Mw_eq_GamC {n : ℕ} (hn : 1 ≤ n) : Mw n = GamC (exp (-1 / 2)) K0 n / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rcases j with _ | j
  · simp only [GamC, zero_add, ite_true, Mw_one, mom_one]
    ring
  · have h1 : j + 1 + 1 = j + 2 := rfl
    rw [h1, Mw_add_two, show 2 * j + 3 = 2 * (j + 1) + 1 by ring, mom_odd, mom_odd]
    simp only [GamC, show j + 2 ≠ 1 by omega, ite_false, show j + 2 - 1 = j + 1 by omega]
    ring

theorem Mw_le (n : ℕ) : Mw (n + 1) ≤ 2 ^ (n + 1) * (n.factorial : ℝ) := by
  rcases n with _ | j
  · rw [Mw_one, mom_one]
    have h1 := (exp_neg_half_bounds).2
    have h2 := K0_le
    norm_num
    linarith
  · rw [show j + 1 + 1 = j + 2 by ring, Mw_add_two, show 2 * j + 3 = 2 * (j + 1) + 1 by ring,
      mom_odd, mom_odd]
    have h1 := kk_le (j + 1)
    have h2 := kk_le j
    have hf : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj : (0 : ℝ) ≤ j.factorial := by positivity
    rw [hf] at h1 ⊢
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have e1 : (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have e2 : (2 : ℝ) ^ (j + 1 + 1) = 2 ^ j * 4 := by rw [pow_succ, pow_succ]; ring
    rw [e1] at h1
    rw [e2]
    nlinarith [mul_nonneg (mul_nonneg hp.le hj0) hj]

/-- The coefficient bound of the paper's Lemma A.1 (c), `n Γ_n/(2n)! ≤ 2/n!`, in the units of `G`. -/
theorem coeff_le (n : ℕ) :
    ((n : ℝ) + 1) * Mw (n + 1) / ((2 * n + 2).factorial : ℝ) ≤ 1 / ((n + 1).factorial : ℝ) := by
  have hM := Mw_le n
  have hc : ((2 ^ (n + 1) * (n + 1).factorial ^ 2 : ℕ) : ℝ) ≤ ((2 * (n + 1)).factorial : ℕ) := by
    exact_mod_cast two_pow_factorial_sq_le (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 2 by ring] at hc
  push_cast at hc
  have hf : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf] at hc ⊢
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hF : (0 : ℝ) < ((2 * n + 2).factorial : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ hF (by positivity)]
  have hM0 := Mw_nonneg (n + 1)
  calc ((n : ℝ) + 1) * Mw (n + 1) * ((n + 1) * n.factorial)
      ≤ ((n : ℝ) + 1) * (2 ^ (n + 1) * n.factorial) * ((n + 1) * n.factorial) := by gcongr
    _ = 2 ^ (n + 1) * ((n + 1) * n.factorial) ^ 2 := by ring
    _ ≤ ((2 * n + 2).factorial : ℝ) := hc
    _ = 1 * ((2 * n + 2).factorial : ℝ) := by ring

/-! ### The series of `Dg` -/

theorem integrableOn_Dg {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun θ => θ * sinh (θ * √Y) / (2 * √Y) * Upper.wt θ) (Ioi 1) := by
  have hb : IntegrableOn (fun θ => (1 / 2 : ℝ) * (θ ^ 2 * cosh (θ * √Y) * Upper.wt θ)) (Ioi 1) :=
    (integrableOn_pow_cosh_wt 2 (√Y)).const_mul _
  refine hb.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hw : ContinuousOn Upper.wt (Ioi 1) := by
      unfold Upper.wt
      refine ContinuousOn.mul (by fun_prop) (ContinuousOn.add ?_ ?_)
      · exact continuousOn_const.div continuousOn_id fun θ hθ => (lt_trans one_pos hθ).ne'
      · exact continuousOn_const.div (continuousOn_id.pow 3) fun θ hθ =>
          pow_ne_zero 3 (lt_trans one_pos hθ).ne'
    exact ContinuousOn.mul (by fun_prop) hw
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_)
    have hθ0 : 0 ≤ θ := (lt_trans one_pos hθ).le
    have hw := (Upper.wt_pos (lt_trans one_pos hθ)).le
    obtain ⟨h1, h2⟩ := sinh_div_le hθ0 hY
    rw [Real.norm_of_nonneg (mul_nonneg h1 hw)]
    calc θ * sinh (θ * √Y) / (2 * √Y) * Upper.wt θ ≤ θ ^ 2 * cosh (θ * √Y) / 2 * Upper.wt θ :=
          mul_le_mul_of_nonneg_right h2 hw
      _ = 1 / 2 * (θ ^ 2 * cosh (θ * √Y) * Upper.wt θ) := by ring

/-- **The interchange of the series and the integral**: `Dg Y = ∑ (n+1) Y^n Mw (n+1)/(2n+2)!`. -/
theorem Dg_hasSum {Y : ℝ} (hY : 0 < Y) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * Y ^ n / ((2 * n + 2).factorial : ℝ) * Mw (n + 1)) (Dg Y) := by
  set F : ℕ → ℝ → ℝ := fun n θ =>
    ((n : ℝ) + 1) * θ ^ (2 * n + 2) * Y ^ n / ((2 * n + 2).factorial : ℝ) * Upper.wt θ with hF
  have hFi : ∀ n, IntegrableOn (F n) (Ioi 1) := fun n => by
    have h : IntegrableOn (fun θ => ((n : ℝ) + 1) * Y ^ n / ((2 * n + 2).factorial : ℝ) *
        (θ ^ (2 * n + 2) * Upper.wt θ)) (Ioi 1) := (integrableOn_pow_wt (2 * n + 2)).const_mul _
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioi
    simp only [hF]
    ring
  have hlim : ∀ θ, HasSum (fun n => F n θ) (θ * sinh (θ * √Y) / (2 * √Y) * Upper.wt θ) :=
    fun θ => (hasSum_sinh_div θ hY).mul_right (Upper.wt θ)
  have hFn : ∀ n, ∀ θ ∈ Ioi (1 : ℝ), 0 ≤ F n θ := fun n θ hθ => by
    have hθ0 : 0 ≤ θ := (lt_trans one_pos hθ).le
    have := (Upper.wt_pos (lt_trans one_pos hθ)).le
    simp only [hF]
    positivity
  have key := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := F) (f := fun θ => θ * sinh (θ * √Y) / (2 * √Y) * Upper.wt θ) F
    (fun n => (hFi n).aestronglyMeasurable)
    (fun n => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (hFn n θ hθ)]))
    (Eventually.of_forall fun θ => (hlim θ).summable)
    ((integrableOn_Dg hY).congr_fun (fun θ _ => (hlim θ).tsum_eq.symm) measurableSet_Ioi)
    (Eventually.of_forall hlim)
  refine key.congr_fun fun n => ?_
  simp only [hF, Mw]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  simp only [show 2 * (n + 1) = 2 * n + 2 by ring]
  ring

theorem Dg_coeff_nonneg {Y : ℝ} (hY : 0 ≤ Y) (n : ℕ) :
    0 ≤ ((n : ℝ) + 1) * Y ^ n / ((2 * n + 2).factorial : ℝ) * Mw (n + 1) := by
  have := Mw_nonneg (n + 1)
  positivity

theorem Dg_nonneg {Y : ℝ} (hY : 0 < Y) : 0 ≤ Dg Y :=
  (Dg_hasSum hY).nonneg fun n => Dg_coeff_nonneg hY.le n

theorem Dg_mono {Y Y' : ℝ} (hY : 0 < Y) (hYY : Y ≤ Y') : Dg Y ≤ Dg Y' := by
  refine hasSum_le (fun n => ?_) (Dg_hasSum hY) (Dg_hasSum (lt_of_lt_of_le hY hYY))
  have := Mw_nonneg (n + 1)
  have hp : Y ^ n ≤ Y' ^ n := pow_le_pow_left₀ hY.le hYY n
  have hf : (0 : ℝ) < ((2 * n + 2).factorial : ℝ) := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  gcongr

/-- **Convexity of `g`**: `G √Y - G √X ≤ (Y - X) Dg Y` for `0 ≤ X ≤ Y`, `Y > 0`. -/
theorem G_sqrt_sub_le {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) (hY : 0 < Y) :
    Upper.G √Y - Upper.G √X ≤ (Y - X) * Dg Y := by
  unfold Upper.G Dg
  rw [← integral_sub (Upper.integrableOn_G _) (Upper.integrableOn_G _), ← integral_const_mul]
  refine setIntegral_mono_on ((Upper.integrableOn_G _).sub (Upper.integrableOn_G _))
    ((integrableOn_Dg hY).const_mul _) measurableSet_Ioi fun θ hθ => ?_
  have hw := (Upper.wt_pos (lt_trans one_pos hθ)).le
  have h := cosh_sqrt_sub_le θ hX hXY hY
  calc cosh (θ * √Y) * Upper.wt θ - cosh (θ * √X) * Upper.wt θ
      = (cosh (θ * √Y) - cosh (θ * √X)) * Upper.wt θ := by ring
    _ ≤ ((Y - X) * (θ * sinh (θ * √Y) / (2 * √Y))) * Upper.wt θ := mul_le_mul_of_nonneg_right h hw
    _ = (Y - X) * (θ * sinh (θ * √Y) / (2 * √Y) * Upper.wt θ) := by ring

/-- `Dg x` is at most half the truncated series of the paper plus half its tail bound. -/
theorem Dg_le {x : ℝ} (hx : 0 < x) (hx32 : x < 32) :
    Dg x ≤ (gpN (exp (-1 / 2)) K0 30 x + tailN 30 x) / 2 := by
  have hS := Dg_hasSum hx
  set a : ℕ → ℝ := fun n => ((n : ℝ) + 1) * x ^ n / ((2 * n + 2).factorial : ℝ) * Mw (n + 1) with ha
  rw [← hS.tsum_eq, ← hS.summable.sum_add_tsum_nat_add 30]
  have h1 : ∑ i ∈ range 30, a i = gpN (exp (-1 / 2)) K0 30 x / 2 := by
    unfold gpN
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha, Mw_eq_GamC (by omega : 1 ≤ n + 1), show 2 * (n + 1) = 2 * n + 2 by ring]
    push_cast
    ring
  have h2 : ∑' i, a (i + 30) ≤ tailN 30 x / 2 := by
    refine Real.tsum_le_of_sum_range_le (fun n => Dg_coeff_nonneg hx.le (n + 30)) fun M => ?_
    have hb := sum_tail_le hx.le 30 (by norm_num; linarith) M
    have ht : tailN 30 x / 2 = x ^ 30 / (((30 + 1).factorial : ℝ) * (1 - x / (30 + 2))) := by
      unfold tailN
      push_cast
      ring
    rw [ht]
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) hb
    have hc := coeff_le (n + 30)
    have hp : 0 ≤ x ^ (30 + n) := pow_nonneg hx.le _
    simp only [ha]
    calc ((((n + 30 : ℕ) : ℝ) + 1) * x ^ (n + 30) / ((2 * (n + 30) + 2).factorial : ℝ) * Mw (n + 30 + 1))
        = x ^ (30 + n) * ((((n + 30 : ℕ) : ℝ) + 1) * Mw (n + 30 + 1) /
            ((2 * (n + 30) + 2).factorial : ℝ)) := by rw [add_comm n 30]; ring
      _ ≤ x ^ (30 + n) * (1 / ((n + 30 + 1).factorial : ℝ)) := mul_le_mul_of_nonneg_left hc hp
      _ = x ^ (30 + n) / ((30 + n + 1).factorial : ℝ) := by rw [add_comm n 30]; ring
  linarith

end RegretKappa.UpperSharp
