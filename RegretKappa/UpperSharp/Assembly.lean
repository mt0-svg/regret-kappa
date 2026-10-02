import RegretKappa.UpperSharp.Step
import RegretKappa.UpperSharp.Terminal
import RegretKappa.Upper.Sums

/-!
# The upper bound with the paper's constants: the potential along the play

The supersolution argument of the paper for the learner `learnerU` of the
statement, with `Φ_k(ρ) = 2 log(C (λ₀ + 3k + Γ(ρ)))` (`PhiU`): along the play the learner's
partial loss plus `Φ_{T-n}(ρ_n)` does not increase (`potential_leU`, from `step_paper`); with the
regret identity (`regret_eqU`) and the terminal condition (`terminal_sharp`),
`Regret_T ≤ Φ_T(0)` (`regret_leU`), and `Φ_T(0)` is the upper bound (`PhiU_T_zero`, by
`Γ(0) = 2e^{-1/2}`). The state `Ssum`, `Vsum` and the extension `ext` are those of `Upper`.
-/

namespace RegretKappa.UpperSharp

open Real Finset MeasureTheory Set

theorem G_zero : Upper.G 0 = exp (-1 / 2) := by
  unfold Upper.G Upper.wt
  simp only [mul_zero, Real.cosh_zero, one_mul]
  have h_integrand : (fun θ : ℝ => exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3)) =
      (fun θ : ℝ => exp (-θ ^ 2 / 2) / θ + 2 * (exp (-θ ^ 2 / 2) / θ ^ 3)) := by
    ext θ
    ring
  rw [h_integrand]
  rw [integral_add integrableOn_K0 (integrableOn_J0.const_mul 2)]
  rw [integral_const_mul]
  rw [← K0, ← J0]
  linarith [J0_add]

/-- `Γ(0) = 2e^{-1/2}`. -/
theorem Gam_zero : Gam 0 = 2 * exp (-1 / 2) := by
  rw [Gam_eq, G_zero]

/-- The prediction of `learnerU` in round `n`, from the state. -/
noncomputable def yhatU {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ :=
  predU T n (Upper.Ssum x y n) (Upper.Vsum x n) (Upper.ext x n)

theorem predictionU_eq {T : ℕ} (x y : Fin T → ℝ) (t : Fin T) :
    (learnerU T).prediction x y t = yhatU x y t := by
  have hX : ∀ i : Fin t, x (Fin.castLE t.isLt (Fin.castSucc i)) = Upper.ext x i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [Upper.ext, hi, ↓reduceDIte]
    rfl
  have hY : ∀ i : Fin t, y (Fin.castLE t.isLt.le i) = Upper.ext y i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [Upper.ext, hi, ↓reduceDIte]
    rfl
  have hL : x (Fin.castLE t.isLt (Fin.last t)) = Upper.ext x t := by
    simp only [Upper.ext, t.isLt, ↓reduceDIte]
    rfl
  unfold Learner.prediction learnerU yhatU Upper.Ssum Upper.Vsum
  simp only [hX, hY, hL]
  rw [Fin.sum_univ_eq_sum_range (fun i => Upper.ext x i * Upper.ext y i) t,
    Fin.sum_univ_eq_sum_range (fun i => Upper.ext x i ^ 2) t]

theorem regret_eqU {T : ℕ} (x y : Fin T → ℝ) :
    regret (learnerU T) x y =
      ∑ i ∈ range T, (yhatU x y i ^ 2 - 2 * yhatU x y i * Upper.ext y i) +
        (Upper.Ssum x y T / √(Upper.Vsum x T)) ^ 2 := by
  unfold regret learnerLoss
  have e1 : ∑ t, ((learnerU T).prediction x y t - y t) ^ 2 =
      ∑ t : Fin T, (yhatU x y t ^ 2 - 2 * yhatU x y t * Upper.ext y t) + ∑ t, y t ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [predictionU_eq, Upper.ext_val]
    ring
  rw [e1, add_sub_assoc, Upper.sum_sq_sub_bestLinearLoss, Upper.Ssum_univ, Upper.Vsum_univ,
    Fin.sum_univ_eq_sum_range (fun i => yhatU x y i ^ 2 - 2 * yhatU x y i * Upper.ext y i) T]

/-- The potential with `k` rounds left: `Φ_k(ρ) = 2 log(C (λ₀ + 3k + Γ(ρ)))`. -/
noncomputable def PhiU (T : ℕ) (k ρ : ℝ) : ℝ := 2 * log (Cst T * (lam0 T + beta * k + Gam ρ))

theorem PhiU_split (T : ℕ) {k : ℝ} (hk : 0 ≤ k) (ρ : ℝ) :
    PhiU T k ρ = 2 * log (Cst T) + 2 * log (lam0 T + beta * k + Gam ρ) := by
  have h1 := Cst_pos T
  have h2 : 0 < lam0 T + beta * k + Gam ρ := by
    have := lam0_pos T
    have := Gam_nonneg ρ
    unfold beta
    positivity
  unfold PhiU
  rw [Real.log_mul h1.ne' h2.ne']
  ring

theorem potential_leU {T : ℕ} (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) (n : ℕ) (hn : n ≤ T) :
    ∑ i ∈ range n, (yhatU x y i ^ 2 - 2 * yhatU x y i * Upper.ext y i) +
      PhiU T ((T : ℝ) - n) (Upper.Ssum x y n / √(Upper.Vsum x n)) ≤ PhiU T T 0 := by
  induction n with
  | zero => simp [Upper.Ssum, Upper.Vsum]
  | succ n ih =>
    have hn' : n < T := hn
    have hnT : (n : ℝ) + 1 ≤ T := by exact_mod_cast hn
    refine le_trans ?_ (ih hn'.le)
    have hlam : 0 < lamU T n := by
      have := lam0_pos T
      unfold lamU beta
      nlinarith
    have hSV : Upper.Vsum x n = 0 → Upper.Ssum x y n = 0 := fun h => by
      have := Upper.Ssum_sq_le x hy n
      rw [h, mul_zero] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    have hs := step_paper (T := T) (t := n) (x := Upper.ext x n) hlam (Upper.Vsum_nonneg x n) hSV
      (Upper.abs_ext_le hy n)
    have hS1 : Upper.Ssum x y (n + 1) = Upper.Ssum x y n + Upper.ext x n * Upper.ext y n :=
      Finset.sum_range_succ _ _
    have hV1 : Upper.Vsum x (n + 1) = Upper.Vsum x n + Upper.ext x n ^ 2 :=
      Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, hS1, hV1]
    rw [PhiU_split T (by push_cast; linarith), PhiU_split T (by linarith)]
    have e1 : lam0 T + beta * ((T : ℝ) - ((n + 1 : ℕ) : ℝ)) = lamU T n := by
      unfold lamU
      push_cast
      ring
    have e2 : lam0 T + beta * ((T : ℝ) - n) = lamU T n + beta := by
      unfold lamU
      ring
    rw [e1, e2]
    unfold yhatU
    linarith

/-- `Regret_T ≤ Φ_T(0)` for outcomes in `[-1, 1]` (the proof of the upper bound). -/
theorem regret_leU {T : ℕ} (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) :
    regret (learnerU T) x y ≤ PhiU T T 0 := by
  have h1 := potential_leU x y hy T le_rfl
  have h2 := terminal_sharp (Upper.rho_sq_le x hy T)
  have h3 : PhiU T ((T : ℝ) - T) (Upper.Ssum x y T / √(Upper.Vsum x T)) =
      2 * log (Cst T * (lam0 T + Gam (Upper.Ssum x y T / √(Upper.Vsum x T)))) := by
    simp [PhiU]
  rw [regret_eqU]
  linarith

/-- `Φ_T(0) = 2 log(e² + (√T + 1)(3T + 2e^{-1/2})/√(2π))`, the upper bound. -/
theorem PhiU_T_zero (T : ℕ) :
    PhiU T T 0 = 2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π)) := by
  have h1 : (√(T : ℝ) + 1) ≠ 0 := by positivity
  have h2 : √(2 * π) ≠ 0 := by positivity
  unfold PhiU
  rw [Gam_zero]
  congr 2
  unfold lam0 Cst beta
  field_simp
  ring

end RegretKappa.UpperSharp
