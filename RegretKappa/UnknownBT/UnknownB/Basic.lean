import Mathlib
import RegretKappa.UnknownBT.Statement
import RegretKappa.UpperSharp.Weights
import RegretKappa.Upper.Sums

/-!
# Unknown `B`: elementary lemmas

Real-number, series, calculus and integer facts used for the unknown `B`, with no reference
to the potential: the reduction in the level (`lam_reduction`), the pieces of the Poisson bound
(`hasSum_le_exp`, `shift_bound`, `poisson_combine`), the integrated scale inequality
(`scale_abstract`), two-point majorization for convex functions (`convex_two_point`), log-convexity
from a discriminant (`convex_log`), the recursions of the integers `kk` (`kk_ratio_beta`,
`kk_ratio_mono`), and the running maximum `pmax` of the outcomes.
-/

namespace RegretKappa.UnknownBT.UB

open Real RegretKappa.UpperSharp RegretKappa.Upper

/-- The running maximum of `|y i|` over the first `n` rounds. -/
noncomputable def pmax {T : ℕ} (y : Fin T → ℝ) (n : ℕ) : ℝ :=
  runMax (fun i : Fin n => RegretKappa.Upper.ext y i)

theorem lam_reduction (x g g0 d : ℝ) (hx : 0 ≤ x) (hg0 : 0 < g0) (hg : 0 < g) :
    2 * Real.log ((x + g) / (x + g0)) - d / (x + g) ≤ max (2 * Real.log (g / g0) - d / g) 0 := by
  have hxg0 : 0 < x + g0 := by linarith
  have hxg : 0 < x + g := by linarith
  have hz : 0 < (x + g) / (x + g0) := div_pos hxg hxg0
  set z := (x + g) / (x + g0) with hz_def
  set N := d * (x + g0) - 2 * (g - g0) * (x + g) with hN_def
  by_cases hN : 0 ≤ N
  · -- Case 1: N ≥ 0, so d*(x+g0) ≥ 2*(g-g0)*(x+g)
    have hN' : d * (x + g0) ≥ 2 * (g - g0) * (x + g) := by linarith
    have hdiv : 2 * (g - g0) / (x + g0) ≤ d / (x + g) :=
      (div_le_div_iff₀ (a := 2 * (g - g0)) (c := d) hxg0 hxg).mpr (by nlinarith)
    have hlog : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz
    have hz_sub_one : z - 1 = (g - g0) / (x + g0) := by
      dsimp [z]
      field_simp [hxg0.ne.symm]
      ring
    have hlog_mul : 2 * Real.log z ≤ 2 * (g - g0) / (x + g0) := by
      have htemp : Real.log z ≤ (g - g0) / (x + g0) := by linarith
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      have h := mul_le_mul_of_nonneg_left htemp h2
      simpa [mul_div_assoc] using h
    have h_nonpos : 2 * Real.log z - d / (x + g) ≤ 0 := by
      linarith
    have h_zero_le_max : (0 : ℝ) ≤ max (2 * Real.log (g / g0) - d / g) 0 :=
      le_max_right _ _
    linarith
  · -- Case 2: N < 0, so d*(x+g0) < 2*(g-g0)*(x+g)
    have hN_lt : d * (x + g0) < 2 * (g - g0) * (x + g) := by linarith
    have hu_pos : 0 < g * (x + g0) / (g0 * (x + g)) := by
      refine div_pos (mul_pos hg hxg0) (mul_pos hg0 hxg)
    set u := g * (x + g0) / (g0 * (x + g)) with hu_def
    have h_one_sub_inv : 1 - u⁻¹ = x * (g - g0) / (g * (x + g0)) := by
      dsimp [u]
      field_simp [hg.ne.symm, hg0.ne.symm, hxg.ne.symm, hxg0.ne.symm]
      ring
    have hlog_u : 1 - u⁻¹ ≤ Real.log u := Real.one_sub_inv_le_log_of_pos hu_pos
    have hlog_u_mul : 2 * (x * (g - g0) / (g * (x + g0))) ≤ 2 * Real.log u := by
      linarith
    by_cases hx0 : x = 0
    · subst hx0
      simp [z]
    · have hx_pos : 0 < x := Ne.lt_of_le (Ne.symm hx0) hx
      have h_aux : d * x / (g * (x + g)) ≤ 2 * (x * (g - g0) / (g * (x + g0))) := by
        have htemp : d * (x + g0) ≤ 2 * (g - g0) * (x + g) := hN_lt.le
        field_simp [hg.ne.symm, hxg.ne.symm, hxg0.ne.symm]
        nlinarith
      have h_log_ineq : d * x / (g * (x + g)) ≤ 2 * Real.log u := by
        linarith
      -- Key algebraic identity:
      -- (2*log(z) - d/(x+g)) - (2*log(g/g0) - d/g) = d*x/(g*(x+g)) - 2*log(u)
      have h_arg_eq : ((x + g) / (x + g0)) / (g / g0) = (g * (x + g0) / (g0 * (x + g)))⁻¹ := by
        field_simp [hg.ne.symm, hg0.ne.symm, hxg.ne.symm, hxg0.ne.symm]
      have h_log_sub : Real.log z - Real.log (g / g0) = -Real.log u := by
        dsimp [z, u]
        rw [← Real.log_div, h_arg_eq]
        rw [Real.log_inv]
        · exact div_ne_zero (by linarith) (by linarith)
        · exact div_ne_zero hg.ne.symm hg0.ne.symm
      have h_diff_eq : (2 * Real.log z - d / (x + g)) - (2 * Real.log (g / g0) - d / g) =
          d * x / (g * (x + g)) - 2 * Real.log u := by
        have h_temp : d / g - d / (x + g) = d * (x + g - g) / (g * (x + g)) := by
          field_simp [hg.ne.symm, hxg.ne.symm]
        calc
          (2 * Real.log z - d / (x + g)) - (2 * Real.log (g / g0) - d / g)
              = 2 * (Real.log z - Real.log (g / g0)) + (d / g - d / (x + g)) := by ring
          _ = 2 * (-Real.log u) + (d * (x + g - g) / (g * (x + g))) := by
            rw [h_log_sub, h_temp]
          _ = -2 * Real.log u + d * x / (g * (x + g)) := by ring
          _ = d * x / (g * (x + g)) - 2 * Real.log u := by ring
      have h_diff_nonpos : (2 * Real.log z - d / (x + g)) - (2 * Real.log (g / g0) - d / g) ≤ 0 := by
        rw [h_diff_eq]
        linarith
      have h_target : 2 * Real.log z - d / (x + g) ≤ 2 * Real.log (g / g0) - d / g := by
        linarith
      exact le_max_of_le_left h_target

theorem hasSum_le_exp (b : ℕ → ℝ) (B v S : ℝ) (hB : ∀ n, b n ≤ B) (hv : 0 ≤ v)
    (hS : HasSum (fun n : ℕ => b n * v ^ n / (n.factorial : ℝ)) S) : S ≤ B * Real.exp v := by
  have h_exp : HasSum (fun n : ℕ => v ^ n / (n.factorial : ℝ)) (Real.exp v) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp v
  have h_mul : HasSum (fun n : ℕ => B * (v ^ n / (n.factorial : ℝ))) (B * Real.exp v) :=
    HasSum.mul_left B h_exp
  have h_nonneg : ∀ n : ℕ, 0 ≤ v ^ n / (n.factorial : ℝ) := by
    intro n
    have h_pow : 0 ≤ v ^ n := pow_nonneg hv n
    have h_fact_pos : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    exact div_nonneg h_pow (by positivity)
  have hS' : HasSum (fun n : ℕ => b n * (v ^ n / (n.factorial : ℝ))) S := by
    simpa [mul_div_assoc] using hS
  have h_le : ∀ n : ℕ, b n * (v ^ n / (n.factorial : ℝ)) ≤ B * (v ^ n / (n.factorial : ℝ)) := by
    intro n
    exact mul_le_mul_of_nonneg_right (hB n) (h_nonneg n)
  exact hasSum_le h_le hS' h_mul

theorem shift_bound (b : ℕ → ℝ) (v β S T : ℝ) (hv : 0 ≤ v) (hβ0 : 0 ≤ β) (hb : ∀ n, 0 ≤ b n)
    (hβ : ∀ n : ℕ, ((n : ℝ) + 1) * (b n - b (n + 1)) ≤ β * b (n + 1))
    (hS : HasSum (fun n : ℕ => b n * v ^ n / (n.factorial : ℝ)) S)
    (hT : HasSum (fun n : ℕ => (n : ℝ) * b n * v ^ n / (n.factorial : ℝ)) T) :
    v * S - T ≤ β * S := by
  -- Notation for the two given series
  set f := fun n : ℕ => b n * v ^ n / (n.factorial : ℝ) with hf
  set g := fun n : ℕ => (n : ℝ) * b n * v ^ n / (n.factorial : ℝ) with hg
  have hS_f : HasSum f S := hS
  have hT_g : HasSum g T := hT
  -- The 0-th term of g is 0
  have hg0 : g 0 = 0 := by
    dsimp [g]
    simp
  -- Step 1: v * S = sum_n ((n:ℝ)+1) * b n * v^(n+1) / ((n+1).factorial : ℝ)
  have h_vS : HasSum (fun n : ℕ => ((n : ℝ) + 1) * b n * v ^ (n + 1) / ((n + 1).factorial : ℝ)) (v * S) := by
    -- v * f n = ((n:ℝ)+1) * b n * v^(n+1) / ((n+1).factorial : ℝ)
    have h_term_eq : ∀ n : ℕ, v * f n = ((n : ℝ) + 1) * b n * v ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      intro n
      dsimp [f]
      field_simp [show (n.factorial : ℝ) ≠ 0 from by exact_mod_cast Nat.factorial_ne_zero n,
        show ((n + 1).factorial : ℝ) ≠ 0 from by exact_mod_cast Nat.factorial_ne_zero (n + 1)]
      simp [Nat.factorial_succ]
      ring
    -- v * S = HasSum (v * f) (v * S) by HasSum.mul_left
    have h_mul : HasSum (fun n => v * f n) (v * S) := HasSum.mul_left v hS_f
    -- Now rewrite using the term equality
    simpa [h_term_eq] using h_mul
  -- Step 2: T = sum_n ((n:ℝ)+1) * b(n+1) * v^(n+1) / ((n+1).factorial : ℝ)
  have h_T_shift : HasSum (fun n : ℕ => ((n : ℝ) + 1) * b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ)) T := by
    -- Use hasSum_nat_add_iff to shift g by 1
    have h_shift := ((hasSum_nat_add_iff (G := ℝ) (f := g) (g := T) 1).mpr ?_)
    · simpa [g] using h_shift
    · have hsum : (∑ i ∈ Finset.range 1, g i) = g 0 := by simp
      simpa [hsum, hg0] using hT_g
  -- Step 3: v * S - T = sum_n (n+1) * (b n - b(n+1)) * v^(n+1) / ((n+1).factorial : ℝ)
  have h_diff : HasSum (fun n : ℕ => ((n : ℝ) + 1) * (b n - b (n + 1)) * v ^ (n + 1) / ((n + 1).factorial : ℝ)) (v * S - T) := by
    have h_sub := HasSum.sub h_vS h_T_shift
    have h_eq : (fun n : ℕ => ((n : ℝ) + 1) * b n * v ^ (n + 1) / ((n + 1).factorial : ℝ) -
      (((n : ℝ) + 1) * b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ))) =
      (fun n : ℕ => ((n : ℝ) + 1) * (b n - b (n + 1)) * v ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      ext n
      field_simp [show ((n + 1).factorial : ℝ) ≠ 0 from by exact_mod_cast Nat.factorial_ne_zero (n + 1)]
    rw [h_eq] at h_sub
    exact h_sub
  -- Step 4: Shift hS to relate sum_n b(n+1) * v^(n+1) / ((n+1).factorial : ℝ) to S - f 0
  have h_S_shift : HasSum (fun n : ℕ => b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ)) (S - f 0) := by
    have h_shift := ((hasSum_nat_add_iff (G := ℝ) (f := f) (g := S - f 0) 1).mpr ?_)
    · simpa [f] using h_shift
    · have hsum : (∑ i ∈ Finset.range 1, f i) = f 0 := by simp
      simpa [hsum] using hS_f
  -- Step 5: Multiply by β
  have h_beta_shift : HasSum (fun n : ℕ => β * (b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ))) (β * (S - f 0)) :=
    HasSum.mul_left β h_S_shift
  -- Simplify the term
  have h_beta_term_eq : ∀ n : ℕ, β * (b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ)) = β * b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    intro n; ring
  have h_beta_shift' : HasSum (fun n : ℕ => β * b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ)) (β * (S - f 0)) := by
    simpa [h_beta_term_eq] using h_beta_shift
  -- Step 6: Termwise inequality using hβ
  have h_term_ineq : ∀ n : ℕ, ((n : ℝ) + 1) * (b n - b (n + 1)) * v ^ (n + 1) / ((n + 1).factorial : ℝ) ≤
      β * b (n + 1) * v ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    intro n
    -- The denominator is positive, so we can multiply both sides by it
    -- Actually, we need to use hβ and the nonnegativity of v^(n+1)/(n+1)!
    -- Since v ≥ 0, v^(n+1) ≥ 0
    -- Since (n+1)! > 0, the fraction is ≥ 0
    have h_pow_nonneg : 0 ≤ v ^ (n + 1) := pow_nonneg hv (n + 1)
    have h_denom_pos : 0 < ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n + 1)
    have h_frac_nonneg : 0 ≤ v ^ (n + 1) / ((n + 1).factorial : ℝ) :=
      div_nonneg h_pow_nonneg (by positivity)
    -- Now use hβ
    -- hβ n : ((n : ℝ) + 1) * (b n - b (n + 1)) ≤ β * b (n + 1)
    -- Multiply both sides by the nonnegative fraction
    have h_mul : ((n : ℝ) + 1) * (b n - b (n + 1)) * (v ^ (n + 1) / ((n + 1).factorial : ℝ)) ≤
        (β * b (n + 1)) * (v ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (hβ n) h_frac_nonneg
    -- Now rearrange the multiplication
    -- LHS: ((n:ℝ)+1) * (b n - b(n+1)) * v^(n+1) / ((n+1).factorial : ℝ)
    -- RHS: β * b(n+1) * v^(n+1) / ((n+1).factorial : ℝ)
    -- These are the same as the expressions in h_mul after ring
    simpa [mul_div_assoc] using h_mul
  -- Step 7: Apply hasSum_le
  have h_ineq : v * S - T ≤ β * (S - f 0) :=
    hasSum_le h_term_ineq h_diff h_beta_shift'
  -- Step 8: Show β * (S - f 0) ≤ β * S
  have h_f0_nonneg : 0 ≤ f 0 := by
    dsimp [f]
    have hb0 : 0 ≤ b 0 := hb 0
    have hv0 : 0 ≤ v ^ 0 := by simp
    positivity
  have h_final : β * (S - f 0) ≤ β * S := by
    nlinarith
  -- Combine
  linarith

theorem poisson_combine (S T B b0 v β : ℝ) (hb0 : 0 < b0) (hS : 0 < S)
    (hSB : S ≤ B * Real.exp v) (hT : v * S - T ≤ β * S) :
    2 * Real.log (S / b0) - 2 * T / S ≤ 2 * Real.log (B / b0) + 2 * β := by
  have h_exp_pos : 0 < Real.exp v := Real.exp_pos v
  have hBpos : 0 < B := by
    have hpos : 0 < B * Real.exp v := by linarith
    exact (mul_pos_iff_of_pos_right h_exp_pos).mp hpos
  have h_log_div : Real.log (S / b0) ≤ Real.log (B / b0) + v := by
    have h_div_le : S / b0 ≤ (B / b0) * Real.exp v := by
      calc
        S / b0 ≤ (B * Real.exp v) / b0 := div_le_div_of_nonneg_right hSB (by linarith)
        _ = (B / b0) * Real.exp v := by ring
    have hpos1 : 0 < S / b0 := div_pos hS hb0
    calc
      Real.log (S / b0) ≤ Real.log ((B / b0) * Real.exp v) := Real.log_le_log hpos1 h_div_le
      _ = Real.log (B / b0) + Real.log (Real.exp v) := by
        rw [Real.log_mul (div_ne_zero hBpos.ne.symm hb0.ne.symm) h_exp_pos.ne.symm]
      _ = Real.log (B / b0) + v := by rw [Real.log_exp v]
  have h_T_div : -2 * T / S ≤ -2 * (v - β) := by
    have hineq : (v - β) * S ≤ T := by linarith
    have hdiv_ineq : v - β ≤ T / S := by
      calc
        v - β = ((v - β) * S) / S := by field_simp [hS.ne.symm]
        _ ≤ T / S := div_le_div_of_nonneg_right hineq (by linarith)
    have := mul_le_mul_of_nonpos_right hdiv_ineq (by norm_num : (-2 : ℝ) ≤ 0)
    -- this gives (T / S) * (-2) ≤ (v - β) * (-2)
    -- rewrite to get -2 * T / S ≤ -2 * (v - β)
    calc
      -2 * T / S = (T / S) * (-2) := by ring
      _ ≤ (v - β) * (-2) := this
      _ = -2 * (v - β) := by ring
  have h_mul_log : 2 * Real.log (S / b0) ≤ 2 * (Real.log (B / b0) + v) := by
    nlinarith
  have h_main : 2 * Real.log (S / b0) - 2 * T / S ≤ 2 * (Real.log (B / b0) + v) - 2 * T / S := by
    nlinarith
  have h_T_div' : -(2 * T / S) ≤ -(2 * (v - β)) := by
    calc
      -(2 * T / S) = (-2 * T) / S := by ring
      _ ≤ (-2) * (v - β) := h_T_div
      _ = -(2 * (v - β)) := by ring
  calc
    2 * Real.log (S / b0) - 2 * T / S ≤ 2 * (Real.log (B / b0) + v) - 2 * T / S := h_main
    _ = 2 * Real.log (B / b0) + 2 * v - 2 * T / S := by ring
    _ ≤ 2 * Real.log (B / b0) + 2 * v - 2 * (v - β) := by
      linarith
    _ = 2 * Real.log (B / b0) + 2 * β := by ring

theorem scale_abstract (P P' : ℝ → ℝ) (κ r m : ℝ) (hP : ∀ w, 0 < w → HasDerivAt P (P' w) w)
    (hineq : ∀ w, 0 < w → 2 * P w - w * P' w ≤ 2 * κ) (hr : 0 < r) (hm : 1 ≤ m) :
    m ^ 2 * P (r / m) - P r ≤ κ * (m ^ 2 - 1) := by
  set φ := fun (u : ℝ) => u ^ 2 * P (r / u) - κ * u ^ 2 with hφ
  set φ' := fun (u : ℝ) => 2 * u * P (r / u) - r * P' (r / u) - 2 * κ * u with hφ'
  have hφderiv : ∀ u, 0 < u → HasDerivAt φ (φ' u) u := by
    intro u hu
    dsimp [φ, φ']
    have h_u2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h_inv : HasDerivAt (fun u : ℝ => u⁻¹) (-((u : ℝ) ^ 2)⁻¹) u :=
      hasDerivAt_inv (by linarith)
    have h_rdiv : HasDerivAt (fun u : ℝ => r / u) (-(r / (u ^ 2))) u := by
      have h1 : HasDerivAt (fun u : ℝ => r * u⁻¹) (r * (-((u : ℝ) ^ 2)⁻¹)) u :=
        HasDerivAt.const_mul r h_inv
      simpa [div_eq_mul_inv] using h1
    have h_P_rdiv : HasDerivAt (fun u : ℝ => P (r / u)) (P' (r / u) * (-(r / (u ^ 2)))) u := by
      have hP_at : HasDerivAt P (P' (r / u)) (r / u) := hP (r / u) (div_pos hr hu)
      exact HasDerivAt.comp u hP_at h_rdiv
    have h_prod : HasDerivAt (fun u : ℝ => u ^ 2 * P (r / u))
      ((2 * u) * P (r / u) + (u ^ 2) * (P' (r / u) * (-(r / (u ^ 2))))) u :=
      HasDerivAt.mul h_u2 h_P_rdiv
    have h_κu2 : HasDerivAt (fun u : ℝ => κ * u ^ 2) (κ * (2 * u)) u :=
      HasDerivAt.const_mul κ h_u2
    have h_φ : HasDerivAt (fun u : ℝ => u ^ 2 * P (r / u) - κ * u ^ 2)
      (((2 * u) * P (r / u) + (u ^ 2) * (P' (r / u) * (-(r / (u ^ 2))))) - κ * (2 * u)) u :=
      HasDerivAt.sub h_prod h_κu2
    have h_simp : (2 * u * P (r / u) + -(u ^ 2 * (P' (r / u) * (r / u ^ 2)))) - κ * (2 * u) =
      2 * u * P (r / u) - r * P' (r / u) - 2 * κ * u := by
      field_simp [hu.ne.symm]
      ring
    simpa [h_simp] using h_φ
  have hφderiv_nonpos : ∀ u, 0 < u → φ' u ≤ 0 := by
    intro u hu
    dsimp [φ']
    have hwpos : 0 < r / u := div_pos hr hu
    have hineq_w := hineq (r / u) hwpos
    have h := mul_le_mul_of_nonneg_left hineq_w hu.le
    have hleft : u * (2 * P (r / u) - (r / u) * P' (r / u)) = 2 * u * P (r / u) - r * P' (r / u) := by
      field_simp [hu.ne.symm]
    have hright : u * (2 * κ) = 2 * κ * u := by ring
    rw [hleft, hright] at h
    linarith
  have h_cont : ContinuousOn φ (Set.Icc 1 m) := by
    have h_diff : ∀ x ∈ Set.Icc (1 : ℝ) m, HasDerivAt φ (φ' x) x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx.1
      exact hφderiv x hxpos
    exact HasDerivAt.continuousOn h_diff
  have h_interior_nonpos : ∀ x ∈ interior (Set.Icc 1 m), φ' x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hx1, hx2⟩
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1.le
    exact hφderiv_nonpos x hxpos
  have h_interior_deriv : ∀ x ∈ interior (Set.Icc 1 m), HasDerivWithinAt φ (φ' x) (interior (Set.Icc 1 m)) x := by
    intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hx1, hx2⟩
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx1.le
    exact (hφderiv x hxpos).hasDerivWithinAt
  have h_antitone : AntitoneOn φ (Set.Icc 1 m) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 1 m) h_cont h_interior_deriv h_interior_nonpos
  have h1_mem : (1 : ℝ) ∈ Set.Icc 1 m := ⟨by rfl, hm⟩
  have hm_mem : m ∈ Set.Icc 1 m := ⟨hm, by rfl⟩
  have h_ineq : φ m ≤ φ 1 := h_antitone h1_mem hm_mem hm
  dsimp [φ] at h_ineq
  have h_ineq' : m ^ 2 * P (r / m) - κ * m ^ 2 ≤ P r - κ := by simpa using h_ineq
  nlinarith

theorem convex_two_point (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (x₁ x₂ y₁ y₂ : ℝ)
    (h1 : x₁ ≤ y₁) (h2 : y₁ ≤ x₂) (h3 : x₁ ≤ y₂) (h4 : y₂ ≤ x₂) (hs : y₁ + y₂ = x₁ + x₂) :
    f y₁ + f y₂ ≤ f x₁ + f x₂ := by
  have hx1x2 : x₁ ≤ x₂ := le_trans h1 h2
  by_cases h_eq : x₁ = x₂
  · subst h_eq
    have hy1 : y₁ = x₁ := by linarith
    have hy2 : y₂ = x₁ := by linarith
    subst hy1 hy2
    rfl
  · have h_lt : x₁ < x₂ := lt_of_le_of_ne hx1x2 h_eq
    have h_denom_pos : 0 < x₂ - x₁ := sub_pos.mpr h_lt
    set t := (x₂ - y₁) / (x₂ - x₁) with ht_def
    have ht_nonneg : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht_le_one : t ≤ 1 := by
      refine (div_le_one (by linarith)).mpr ?_
      linarith
    have h_sum_t : t + (1 - t) = 1 := by ring
    have h_onemt_nonneg : 0 ≤ 1 - t := by linarith
    have hy1_eq : y₁ = t * x₁ + (1 - t) * x₂ := by
      dsimp [t]
      field_simp [ne_of_gt h_denom_pos]
      ring
    have hy2_eq : y₂ = (1 - t) * x₁ + t * x₂ := by
      linarith
    have hx1_mem : x₁ ∈ Set.univ := Set.mem_univ _
    have hx2_mem : x₂ ∈ Set.univ := Set.mem_univ _
    have h_ineq1 : f y₁ ≤ t * f x₁ + (1 - t) * f x₂ := by
      rw [hy1_eq]
      simpa [smul_eq_mul] using hf.2 hx1_mem hx2_mem ht_nonneg h_onemt_nonneg h_sum_t
    have h_ineq2 : f y₂ ≤ (1 - t) * f x₁ + t * f x₂ := by
      rw [hy2_eq]
      simpa [smul_eq_mul, add_comm] using hf.2 hx1_mem hx2_mem h_onemt_nonneg ht_nonneg (by linarith)
    linarith

theorem convex_log (g g1 g2 : ℝ → ℝ) (l : ℝ) (hpos : ∀ v, 0 < l + g v)
    (hg : ∀ v, HasDerivAt g (g1 v) v) (hg1 : ∀ v, HasDerivAt g1 (g2 v) v)
    (hdisc : ∀ v, g1 v ^ 2 ≤ (l + g v) * g2 v) :
    ConvexOn ℝ Set.univ (fun v => Real.log (l + g v)) := by
  set f := fun v : ℝ => Real.log (l + g v) with hf
  set f' := fun v : ℝ => g1 v / (l + g v) with hf'
  set f'' := fun v : ℝ => (g2 v * (l + g v) - g1 v * g1 v) / (l + g v) ^ 2 with hf''
  have hpos_ne : ∀ v, l + g v ≠ 0 := fun v => by linarith [hpos v]
  have h_cont : ContinuousOn f Set.univ := by
    intro v _
    have h_add : HasDerivAt (fun x : ℝ => l + g x) (g1 v) v :=
      (hg v).const_add l
    have h_ne : l + g v ≠ 0 := hpos_ne v
    exact ((h_add.log h_ne).continuousAt).continuousWithinAt
  have h_deriv1 : ∀ x ∈ interior (Set.univ : Set ℝ), HasDerivWithinAt f (f' x) (interior Set.univ) x := by
    intro x hx
    have h_add : HasDerivAt (fun y : ℝ => l + g y) (g1 x) x :=
      (hg x).const_add l
    have h_ne : l + g x ≠ 0 := hpos_ne x
    have h_log : HasDerivAt f (f' x) x := by
      dsimp [f, f']
      exact h_add.log h_ne
    exact h_log.hasDerivWithinAt
  have h_deriv2 : ∀ x ∈ interior (Set.univ : Set ℝ), HasDerivWithinAt f' (f'' x) (interior Set.univ) x := by
    intro x hx
    have h_add : HasDerivAt (fun y : ℝ => l + g y) (g1 x) x :=
      (hg x).const_add l
    have h_ne : l + g x ≠ 0 := hpos_ne x
    have h_div : HasDerivAt f' (f'' x) x := by
      dsimp [f', f'']
      exact (hg1 x).div h_add h_ne
    exact h_div.hasDerivWithinAt
  have h_nonneg : ∀ x ∈ interior (Set.univ : Set ℝ), 0 ≤ f'' x := by
    intro x hx
    dsimp [f'']
    have h_num : 0 ≤ g2 x * (l + g x) - g1 x * g1 x := by
      have hdisc_x := hdisc x
      linarith
    have h_denom : 0 ≤ (l + g x) ^ 2 := by
      have hpos_x : 0 < l + g x := hpos x
      exact pow_two_nonneg _
    refine div_nonneg h_num h_denom
  have h_conv : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have h_interior : interior (Set.univ : Set ℝ) = Set.univ := interior_univ
  apply convexOn_of_hasDerivWithinAt2_nonneg h_conv h_cont
  · exact h_deriv1
  · exact h_deriv2
  · exact h_nonneg

theorem cost_bound (e₁ e m : ℝ) (he : 0 ≤ e) (he1 : e ≤ e₁) (h1 : e₁ ≤ 1) (hm : 1 ≤ m) :
    (e₁ ^ 2 - 2 * e₁ * m) - ((m * e) ^ 2 - 2 * (m * e) * m) ≤ 2 * (m ^ 2 - 1) := by
  have h_factor : (e₁ ^ 2 - 2 * e₁ * m) - ((m * e) ^ 2 - 2 * (m * e) * m) = (m * e - e₁) * (2 * m - e₁ - m * e) := by
    ring
  rw [h_factor]
  by_cases hme_le_e₁ : m * e ≤ e₁
  · have h1_nonpos : m * e - e₁ ≤ 0 := by linarith
    have h2_nonneg : 0 ≤ 2 * m - e₁ - m * e := by
      have : m * e ≤ 1 := by linarith
      nlinarith
    nlinarith
  · have h1_pos : 0 ≤ m * e - e₁ := by linarith
    have h1_bound : m * e - e₁ ≤ m - 1 := by
      have he_le_one : e ≤ 1 := by linarith
      nlinarith
    have h2_bound : 2 * m - e₁ - m * e ≤ 2 * m := by
      have he₁_nonneg : 0 ≤ e₁ := by linarith
      have hme_nonneg : 0 ≤ m * e := by nlinarith
      nlinarith
    have h_prod : (m * e - e₁) * (2 * m - e₁ - m * e) ≤ (m - 1) * (2 * m) := by
      nlinarith
    have h_final : (m - 1) * (2 * m) ≤ 2 * (m ^ 2 - 1) := by
      nlinarith
    nlinarith

theorem abs_cases (p b m : ℝ) (hp : 0 ≤ p) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hm : 1 ≤ m) :
    (b ≤ p → |p - b| ≤ |p - b / m|) ∧
      (p < b → |p - b| ≤ 1 ∧ |p - b / m| ≤ 1 ∧ |p - b| - |p - b / m| ≤ (m - 1) / m) := by
  have hbm : b / m ≤ b := div_le_self hb hm
  have hbm_nonneg : 0 ≤ b / m := div_nonneg hb (by linarith : 0 ≤ m)
  have hm_pos : 0 < m := by linarith
  constructor
  · intro hbp
    have hpb_nonneg : 0 ≤ p - b := sub_nonneg.mpr hbp
    have hpbm_nonneg : 0 ≤ p - b / m := by linarith
    rw [abs_of_nonneg hpb_nonneg, abs_of_nonneg hpbm_nonneg]
    linarith
  · intro hpb
    have hpb_neg : p - b < 0 := sub_neg.mpr hpb
    have habs1 : |p - b| = b - p := by
      rw [abs_of_neg hpb_neg]
      ring
    have h1 : |p - b| ≤ 1 := by
      rw [habs1]
      linarith
    have h2 : |p - b / m| ≤ 1 := by
      have h_abs_le_b : |p - b / m| ≤ b := by
        apply abs_le.mpr
        constructor
        · -- -b ≤ p - b/m
          linarith
        · -- p - b/m ≤ b
          linarith
      linarith
    have h3 : |p - b| - |p - b / m| ≤ (m - 1) / m := by
      rw [habs1]
      have h_abs_sub : b - p - |p - b / m| ≤ |(p - b) - (p - b / m)| := by
        have h := abs_sub_abs_le_abs_sub (p - b) (p - b / m)
        linarith
      have h_diff_abs : |(p - b) - (p - b / m)| = b - b / m := by
        have h_diff : (p - b) - (p - b / m) = b / m - b := by ring
        rw [h_diff]
        have h_nonpos : b / m - b ≤ 0 := by linarith
        rw [abs_of_nonpos h_nonpos]
        ring
      rw [h_diff_abs] at h_abs_sub
      have h_bound : b - b / m ≤ (m - 1) / m := by
        have h_inv_le_one : 1 / m ≤ 1 := div_le_self (by norm_num : 0 ≤ (1 : ℝ)) hm
        have h_nonneg_factor : 0 ≤ 1 - 1 / m := by linarith
        calc
          b - b / m = b * (1 - 1 / m) := by ring
          _ ≤ 1 * (1 - 1 / m) := mul_le_mul_of_nonneg_right hb1 h_nonneg_factor
          _ = 1 - 1 / m := by ring
          _ = (m - 1) / m := by field_simp [hm_pos.ne.symm]
      linarith
    exact And.intro h1 (And.intro h2 h3)

theorem lip_log (l gx gz g0 A : ℝ) (hl : 0 ≤ l) (hg0 : 0 < g0) (hz : g0 ≤ gz) (hzx : gz ≤ gx)
    (hA : 0 < A) :
    2 * Real.log ((l + gx) / A) - 2 * Real.log ((l + gz) / A) ≤ 2 * (gx - gz) / g0 := by
  have hpos_gx : 0 < l + gx := by linarith
  have hpos_gz : 0 < l + gz := by linarith
  have hpos_gx' : l + gx ≠ 0 := by linarith
  have hpos_gz' : l + gz ≠ 0 := by linarith
  have hA' : A ≠ 0 := by linarith
  have hsub_nonneg : 0 ≤ gx - gz := by linarith
  have hgz_ge_g0 : g0 ≤ l + gz := by linarith
  calc
    2 * Real.log ((l + gx) / A) - 2 * Real.log ((l + gz) / A)
        = 2 * (Real.log ((l + gx) / A) - Real.log ((l + gz) / A)) := by ring
    _ = 2 * ((Real.log (l + gx) - Real.log A) - (Real.log (l + gz) - Real.log A)) := by
      rw [Real.log_div hpos_gx' hA', Real.log_div hpos_gz' hA']
    _ = 2 * (Real.log (l + gx) - Real.log (l + gz)) := by ring
    _ = 2 * Real.log ((l + gx) / (l + gz)) := by rw [Real.log_div hpos_gx' hpos_gz']
    _ ≤ 2 * (((l + gx) / (l + gz)) - 1) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hpos_gx hpos_gz)
      nlinarith
    _ = 2 * ((gx - gz) / (l + gz)) := by
      field_simp [hpos_gz']
      ring
    _ ≤ 2 * ((gx - gz) / g0) := by
      have hdiv := div_le_div_of_nonneg_left hsub_nonneg hg0 hgz_ge_g0
      nlinarith
    _ = 2 * (gx - gz) / g0 := by ring

theorem kk_succ_eq (m : ℕ) : kk (m + 1) = 1 + 2 * m * kk m := by
  cases m with
  | zero => simp [kk]
  | succ k => simp [kk]

theorem kk_one_le {m : ℕ} (hm : 1 ≤ m) : 1 ≤ kk m := by
  refine Nat.le_induction (by simp [kk]) (fun k hk ih => ?_) m hm
  rw [kk_succ_eq]
  omega

theorem kk_ratio_beta (n : ℕ) (hn : 2 ≤ n) :
    15 * ((n + 1) * (2 * n + 1)) * (kk n + 2 * kk (n - 1)) ≤
      (15 * (n + 1) + 16) * (kk (n + 1) + 2 * kk n) := by
  -- case split: n = 2, n = 3, n ≥ 4
  by_cases h4 : n < 4
  · -- n = 2 or n = 3
    have hnle3 : n ≤ 3 := by omega
    interval_cases n
    · norm_num [kk]
    · norm_num [kk]
  · -- n ≥ 4
    have hn4 : 4 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    -- work in ℚ to use division
    have hk_eq : (kk n : ℚ) = 1 + 2 * ((n : ℚ) - 1) * (kk (n - 1) : ℚ) := by
      have h := kk_succ_eq (n - 1)
      -- h : kk ((n - 1) + 1) = 1 + 2 * (n - 1) * kk (n - 1)
      have h_add : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel hn1
      rw [h_add] at h
      exact mod_cast h
    have hc_eq : (kk (n + 1) : ℚ) = 1 + 2 * (n : ℚ) * (kk n : ℚ) := by
      have h := kk_succ_eq n
      -- h : kk (n + 1) = 1 + 2 * n * kk n
      exact mod_cast h
    have h_ineq : (15 : ℚ) * (((n : ℚ) + 1) * (2 * (n : ℚ) + 1)) * ((kk n : ℚ) + 2 * (kk (n - 1) : ℚ)) ≤
      ((15 : ℚ) * ((n : ℚ) + 1) + 16) * ((kk (n + 1) : ℚ) + 2 * (kk n : ℚ)) := by
      set a := (kk (n - 1) : ℚ) with ha
      set N := (n : ℚ) with hN
      have hk_eq' : (kk n : ℚ) = 1 + 2 * (N - 1) * a := by
        have h := kk_succ_eq (n - 1)
        have h_add : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel hn1
        rw [h_add] at h
        simpa [ha, hN] using mod_cast h
      have hc_eq' : (kk (n + 1) : ℚ) = 1 + 2 * N * (1 + 2 * (N - 1) * a) := by
        have h := kk_succ_eq n
        have h_cast : (kk (n + 1) : ℚ) = 1 + 2 * (n : ℚ) * (kk n : ℚ) := by exact mod_cast h
        simpa [ha, hN, hk_eq'] using h_cast
      rw [hk_eq', hc_eq']
      -- Goal: 15*(N+1)*(2*N+1)*((1 + 2*(N-1)*a) + 2*a) ≤ (15*(N+1)+16)*((1 + 2*N*(1 + 2*(N-1)*a)) + 2*(1 + 2*(N-1)*a))
      have hL : (1 + 2*(N-1)*a) + 2*a = 1 + 2*N*a := by ring
      have hR : (1 + 2*N*(1 + 2*(N-1)*a)) + 2*(1 + 2*(N-1)*a) = 3 + 2*N + 4*(N-1)*(N+1)*a := by ring
      rw [hL, hR]
      -- Goal: 15*(N+1)*(2*N+1)*(1 + 2*N*a) ≤ (15*(N+1)+16)*(3 + 2*N + 4*(N-1)*(N+1)*a)
      have h_diff : ((15*(N+1)+16)*(3 + 2*N + 4*(N-1)*(N+1)*a) - 15*(N+1)*(2*N+1)*(1 + 2*N*a)) =
        (62*N + 78) + a*(34*N^2 - 90*N - 124) := by ring
      have h_nonneg : 0 ≤ (62*N + 78) + a*(34*N^2 - 90*N - 124) := by
        have hN4 : (4 : ℚ) ≤ N := by
          simpa [hN] using mod_cast hn4
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          exact mod_cast Nat.zero_le _
        have h_coeff : 0 ≤ 34*N^2 - 90*N - 124 := by nlinarith
        have h_const : 0 ≤ 62*N + 78 := by nlinarith
        have h_mul : 0 ≤ a*(34*N^2 - 90*N - 124) := mul_nonneg ha_nonneg h_coeff
        exact add_nonneg h_const h_mul
      linarith
    exact_mod_cast h_ineq

theorem kk_ratio_mono (n : ℕ) (hn : 2 ≤ n) :
    kk (n + 1) + 2 * kk n ≤ (2 * n + 1) * (kk n + 2 * kk (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hpos : (1 : ℤ) ≤ (kk (n - 1) : ℤ) := by
    have : 1 ≤ kk (n - 1) := by
      apply kk_one_le
      omega
    exact_mod_cast this
  -- express kk (n+1) in terms of kk n
  rw [kk_succ_eq n]
  -- express kk n in terms of kk (n-1): kk n = 1 + 2*(n-1)*kk (n-1)
  have hkn : kk n = 1 + 2 * (n - 1) * kk (n - 1) := by
    have hn_eq : n = (n - 1) + 1 := by omega
    rw [hn_eq, kk_succ_eq]
    -- simplify (n-1+1-1) to (n-1)
    have : (n - 1 + 1 - 1) = (n - 1) := by omega
    simp [this]
  rw [hkn]
  -- goal is now a polynomial inequality in n and a := kk (n-1)
  -- use nlinarith on ℤ to avoid subtraction issues
  have h : (1 + 2 * (n : ℤ) * (1 + 2 * ((n : ℤ) - 1) * (kk (n - 1) : ℤ)) +
           2 * (1 + 2 * ((n : ℤ) - 1) * (kk (n - 1) : ℤ)) : ℤ) ≤
          ((2 : ℤ) * (n : ℤ) + 1) * ((1 + 2 * ((n : ℤ) - 1) * (kk (n - 1) : ℤ)) +
          2 * (kk (n - 1) : ℤ)) := by
    set a := (kk (n - 1) : ℤ) with ha
    have ha_pos : (1 : ℤ) ≤ a := hpos
    nlinarith
  exact_mod_cast h

theorem runMax_le_iff {n : ℕ} (y : Fin n → ℝ) (c : ℝ) :
    runMax y ≤ c ↔ 0 ≤ c ∧ ∀ i, |y i| ≤ c := by
  unfold runMax
  simp [Finset.fold_max_le]

theorem pmax_succ {T : ℕ} (y : Fin T → ℝ) (n : ℕ) :
    pmax y (n + 1) = max (pmax y n) |ext y n| := by
  unfold pmax runMax
  apply le_antisymm
  · -- LHS ≤ RHS: fold over Fin (n+1) ≤ max (fold over Fin n) |ext y n|
    apply (Finset.fold_max_le (β := ℝ) (c := max (Finset.univ.fold max (0 : ℝ) (fun i : Fin n => |ext y i|)) |ext y n|)).mpr
    constructor
    · -- 0 ≤ max (fold ...) |ext y n|
      have h0 : (0 : ℝ) ≤ Finset.univ.fold max (0 : ℝ) (fun i : Fin n => |ext y i|) := by
        apply (Finset.le_fold_max (β := ℝ) (c := (0 : ℝ))).mpr
        left; rfl
      exact le_trans h0 (le_max_left _ _)
    · -- ∀ x ∈ univ, |ext y x| ≤ max (fold ...) |ext y n|
      intro i hi
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last n
        -- Need |ext y (Fin.last n)| ≤ max (fold ...) |ext y n|
        -- But ext y (Fin.last n : ℕ) = ext y n by definition
        -- So we need |ext y n| ≤ max (fold ...) |ext y n|
        exact le_max_right _ _
      · -- i = Fin.castSucc j for some j : Fin n
        intro j
        -- Need |ext y (Fin.castSucc j)| ≤ max (fold ...) |ext y n|
        -- ext y (Fin.castSucc j : ℕ) = ext y j by definition
        -- And |ext y j| ≤ fold over Fin n by Finset.le_fold_max
        -- Then ≤ max (fold ...) |ext y n|
        have hle : |ext y j| ≤ Finset.univ.fold max (0 : ℝ) (fun i : Fin n => |ext y i|) := by
          -- Using Finset.le_fold_max
          apply (Finset.le_fold_max (β := ℝ) (c := |ext y j|) (s := Finset.univ (α := Fin n)) (f := fun i : Fin n => |ext y i|)).mpr
          right
          refine ⟨j, Finset.mem_univ _, ?_⟩
          rfl
        exact le_trans hle (le_max_left _ _)
  · -- RHS ≤ LHS: max (fold over Fin n) |ext y n| ≤ fold over Fin (n+1)
    rw [max_le_iff]
    constructor
    · -- fold over Fin n ≤ fold over Fin (n+1)
      apply (Finset.fold_max_le (β := ℝ) (c := Finset.univ.fold max (0 : ℝ) (fun i : Fin (n+1) => |ext y i|))).mpr
      constructor
      · -- 0 ≤ fold over Fin (n+1)
        -- Using Finset.le_fold_max: 0 ≤ fold iff 0 ≤ 0 ∨ ∃ x ∈ univ, 0 ≤ f x
        apply (Finset.le_fold_max (β := ℝ) (c := (0 : ℝ))).mpr
        left; rfl
      · -- ∀ x ∈ univ (Fin n), |ext y x| ≤ fold over Fin (n+1)
        intro i hi
        -- Using Finset.le_fold_max
        apply (Finset.le_fold_max (β := ℝ) (c := |ext y i|) (s := Finset.univ (α := Fin (n+1))) (f := fun i : Fin (n+1) => |ext y i|)).mpr
        right
        -- Need to find x ∈ Finset.univ (Fin (n+1)) such that |ext y x| ≤ |ext y x|
        -- Take x = Fin.castSucc i
        refine ⟨Fin.castSucc i, Finset.mem_univ _, ?_⟩
        -- Need |ext y (Fin.castSucc i)| ≤ |ext y (Fin.castSucc i)|
        -- But ext y (Fin.castSucc i : ℕ) = ext y i by definition
        rfl
    · -- |ext y n| ≤ fold over Fin (n+1)
      apply (Finset.le_fold_max (β := ℝ) (c := |ext y n|) (s := Finset.univ (α := Fin (n+1))) (f := fun i : Fin (n+1) => |ext y i|)).mpr
      right
      refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
      -- Need |ext y n| ≤ |ext y (Fin.last n)|
      -- But ext y (Fin.last n : ℕ) = ext y n by definition
      rfl

theorem pmax_round {T : ℕ} (y : Fin T → ℝ) (t : Fin T) :
    runMax (fun s : Fin t => y (Fin.castLE t.isLt.le s)) = pmax y t := by
  unfold pmax
  congr 1
  funext s
  unfold RegretKappa.Upper.ext
  have hs : (s : ℕ) < T := Nat.lt_trans s.2 t.2
  simp [hs]
  congr

theorem pmax_all {T : ℕ} (y : Fin T → ℝ) : runMax y = pmax y T := by
  unfold pmax
  congr 1
  funext i
  simp [ext]

theorem le_pmax {T : ℕ} (y : Fin T → ℝ) (n i : ℕ) (hi : i < n) : |ext y i| ≤ pmax y n := by
  unfold pmax RegretKappa.UnknownBT.runMax
  rw [Finset.le_fold_max]
  right
  refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
  rfl

end RegretKappa.UnknownBT.UB
