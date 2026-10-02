import RegretKappa.Upper.Step
import RegretKappa.Upper.Terminal
import RegretKappa.Upper.Identity

/-!
# Upper bound: the learner and the target `UpperBound`

The learner of Theorem 3.1 of the paper, with the potential `G = Γ/2` and the constants
`β = 60`, `C = 4 (√T + 1)`, `λ₀ = 2/C` (the paper proves `β = 3`, `C = (√T + 1)/√(2π)`,
`λ₀ = e²/C`; any constant `β` and any `C` of order `√T` give the leading term `3 log T`, which is
all that `UpperBound` asks). In round `t` (0-indexed) it predicts
`clip(½ log((λ_t + G((S + x)/√(V + x²))) / (λ_t + G((S - x)/√(V + x²)))))`, with
`S = ∑_{i<t} x_i y_i`, `V = ∑_{i<t} x_i²`, `x = x_t`, `λ_t = λ₀ + β (T - t - 1)`.

`potential_le` is the supersolution argument of Lemma 3.3 of the paper, along the play (no
recursion `W`): the learner's partial loss plus `Φ_{T-n}(ρ_n)` does not increase. With the regret
identity and the terminal condition, `regret_le` gives `Regret_T ≤ Φ_T(0) ≤ 3 log T + 2 log 962`
for outcomes in `[-1, 1]`, and `upperBound` scales the outcomes by `B`.
-/

namespace RegretKappa.Upper

open Real Finset Filter

/-- The learner of the upper bound, for outcomes in `[-1, 1]`. -/
noncomputable def learner (T : ℕ) : Learner T where
  predict t xs ys := pred (lamAt T t) (∑ i : Fin t, xs (Fin.castSucc i) * ys i)
    (∑ i : Fin t, xs (Fin.castSucc i) ^ 2) (xs (Fin.last t))

/-- A sequence on `Fin T` extended by `0` to `ℕ`. -/
noncomputable def ext {T : ℕ} (x : Fin T → ℝ) (i : ℕ) : ℝ := if h : i < T then x ⟨i, h⟩ else 0

/-- `S_n = ∑_{i<n} x_i y_i`. -/
noncomputable def Ssum {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, ext x i * ext y i

/-- `V_n = ∑_{i<n} x_i²`. -/
noncomputable def Vsum {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, ext x i ^ 2

/-- The learner's prediction in round `n`, from the state. -/
noncomputable def yhat {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ :=
  pred (lamAt T n) (Ssum x y n) (Vsum x n) (ext x n)

theorem ext_val {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : ext x t = x t := by
  simp [ext, t.isLt]

theorem abs_ext_le {T : ℕ} {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1) (i : ℕ) : |ext y i| ≤ 1 := by
  unfold ext
  split_ifs with h
  · exact hy _
  · simp

theorem prediction_eq {T : ℕ} (x y : Fin T → ℝ) (t : Fin T) :
    (learner T).prediction x y t = yhat x y t := by
  have hX : ∀ i : Fin t, x (Fin.castLE t.isLt (Fin.castSucc i)) = ext x i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [ext, hi, ↓reduceDIte]
    rfl
  have hY : ∀ i : Fin t, y (Fin.castLE t.isLt.le i) = ext y i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [ext, hi, ↓reduceDIte]
    rfl
  have hL : x (Fin.castLE t.isLt (Fin.last t)) = ext x t := by
    simp only [ext, t.isLt, ↓reduceDIte]
    rfl
  unfold Learner.prediction learner yhat Ssum Vsum
  simp only [hX, hY, hL]
  rw [Fin.sum_univ_eq_sum_range (fun i => ext x i * ext y i) t,
    Fin.sum_univ_eq_sum_range (fun i => ext x i ^ 2) t]

theorem Ssum_univ {T : ℕ} (x y : Fin T → ℝ) : ∑ t, x t * y t = Ssum x y T := by
  unfold Ssum
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext x i * ext y i) T]
  simp [ext_val]

theorem Vsum_univ {T : ℕ} (x : Fin T → ℝ) : ∑ t, x t ^ 2 = Vsum x T := by
  unfold Vsum
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext x i ^ 2) T]
  simp [ext_val]

theorem regret_eq {T : ℕ} (x y : Fin T → ℝ) :
    regret (learner T) x y = ∑ i ∈ range T, (yhat x y i ^ 2 - 2 * yhat x y i * ext y i) +
      (Ssum x y T / √(Vsum x T)) ^ 2 := by
  unfold regret learnerLoss
  have e1 : ∑ t, ((learner T).prediction x y t - y t) ^ 2 =
      ∑ t : Fin T, (yhat x y t ^ 2 - 2 * yhat x y t * ext y t) + ∑ t, y t ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [prediction_eq, ext_val]
    ring
  rw [e1, add_sub_assoc, sum_sq_sub_bestLinearLoss, Ssum_univ, Vsum_univ,
    Fin.sum_univ_eq_sum_range (fun i => yhat x y i ^ 2 - 2 * yhat x y i * ext y i) T]

theorem Vsum_nonneg {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : 0 ≤ Vsum x n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem Ssum_sq_le {T : ℕ} (x : Fin T → ℝ) {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1) (n : ℕ) :
    Ssum x y n ^ 2 ≤ n * Vsum x n :=
  sq_sum_mul_le (ext x) (ext y) (abs_ext_le hy) n

theorem rho_sq_le {T : ℕ} (x : Fin T → ℝ) {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1) (n : ℕ) :
    (Ssum x y n / √(Vsum x n)) ^ 2 ≤ n := by
  rcases eq_or_lt_of_le (Vsum_nonneg x n) with h | h
  · rw [← h, Real.sqrt_zero, div_zero]
    simp
  · rw [div_pow, Real.sq_sqrt h.le, div_le_iff₀ h]
    exact Ssum_sq_le x hy n

theorem Phi_split (T : ℕ) {k : ℝ} (hk : 0 ≤ k) (ρ : ℝ) :
    Phi T k ρ = 2 * log (Cst T) + 2 * log (lam0 T + beta * k + G ρ) := by
  have h1 := Cst_pos T
  have h2 : 0 < lam0 T + beta * k + G ρ := by
    have := lam0_pos T
    have := G_nonneg ρ
    unfold beta
    positivity
  unfold Phi
  rw [Real.log_mul h1.ne' h2.ne']
  ring

theorem potential_le {T : ℕ} (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) (n : ℕ) (hn : n ≤ T) :
    ∑ i ∈ range n, (yhat x y i ^ 2 - 2 * yhat x y i * ext y i) +
      Phi T ((T : ℝ) - n) (Ssum x y n / √(Vsum x n)) ≤ Phi T T 0 := by
  induction n with
  | zero => simp [Ssum, Vsum]
  | succ n ih =>
    have hn' : n < T := hn
    have hnT : (n : ℝ) + 1 ≤ T := by exact_mod_cast hn
    refine le_trans ?_ (ih hn'.le)
    have hlam : 0 < lamAt T n := by
      have := lam0_pos T
      unfold lamAt beta
      nlinarith
    have hSV : Vsum x n = 0 → Ssum x y n = 0 := fun h => by
      have := Ssum_sq_le x hy n
      rw [h, mul_zero] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    have hs := step (x := ext x n) hlam (Vsum_nonneg x n) hSV (abs_ext_le hy n)
    have hS1 : Ssum x y (n + 1) = Ssum x y n + ext x n * ext y n := Finset.sum_range_succ _ _
    have hV1 : Vsum x (n + 1) = Vsum x n + ext x n ^ 2 := Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, hS1, hV1]
    rw [Phi_split T (by push_cast; linarith), Phi_split T (by linarith)]
    have e1 : lam0 T + beta * ((T : ℝ) - ((n + 1 : ℕ) : ℝ)) = lamAt T n := by
      unfold lamAt
      push_cast
      ring
    have e2 : lam0 T + beta * ((T : ℝ) - n) = lamAt T n + beta := by
      unfold lamAt
      ring
    rw [e1, e2]
    unfold yhat
    linarith

/-- Theorem 3.1 of the paper (constants of this file) for outcomes in `[-1, 1]`. -/
theorem regret_le {T : ℕ} (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) :
    regret (learner T) x y ≤ Phi T T 0 := by
  have h1 := potential_le x y hy T le_rfl
  have h2 := terminal (rho_sq_le x hy T)
  have h3 : Phi T ((T : ℝ) - T) (Ssum x y T / √(Vsum x T)) =
      2 * log (Cst T * (lam0 T + G (Ssum x y T / √(Vsum x T)))) := by
    simp [Phi]
  rw [regret_eq]
  linarith

theorem Phi_le_aux {T : ℕ} (hT : 1 ≤ T) {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 60) :
    2 * log (Cst T * (lam0 T + beta * T + g)) ≤ 3 * log T + 2 * log 962 := by
  -- Convert hT to ℝ
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hT_pos : 0 < (T : ℝ) := by linarith
  have hT_nonneg : 0 ≤ (T : ℝ) := by linarith
  -- sqrt(T) ≥ 1 since T ≥ 1
  have h_sqrtT_ge_one : (1 : ℝ) ≤ √(T : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hT'
  have h_sqrtT_nonneg : 0 ≤ √(T : ℝ) := Real.sqrt_nonneg _
  -- g ≤ 60 * T since g ≤ 60 and T ≥ 1
  have hg_le_60T : g ≤ 60 * (T : ℝ) := by
    nlinarith
  -- Cst T * lam0 T = 2
  have h_Cst_lam0 : Cst T * lam0 T = 2 := by
    dsimp [lam0, Cst]
    field_simp
  -- sqrt(T) + 1 ≤ 2 * sqrt(T)
  have h_sqrtT_plus_one_le_2sqrtT : √(T : ℝ) + 1 ≤ 2 * √(T : ℝ) := by
    nlinarith
  -- 60 * T + g ≤ 120 * T
  have h_60T_plus_g_le_120T : 60 * (T : ℝ) + g ≤ 120 * (T : ℝ) := by
    nlinarith
  have h_nonneg_60T_plus_g : 0 ≤ 60 * (T : ℝ) + g := by nlinarith
  -- Cst T * (60 * T + g) ≤ 960 * T * sqrt(T)
  have h_Cst_bound : Cst T * (60 * (T : ℝ) + g) ≤ 960 * (T : ℝ) * √(T : ℝ) := by
    dsimp [Cst]
    have h_2sqrtT_nonneg : 0 ≤ 2 * √(T : ℝ) := by nlinarith
    calc
      4 * (√(T : ℝ) + 1) * (60 * (T : ℝ) + g) = 4 * ((√(T : ℝ) + 1) * (60 * (T : ℝ) + g)) := by ring
      _ ≤ 4 * ((2 * √(T : ℝ)) * (120 * (T : ℝ))) := by
        apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 4)
        apply mul_le_mul h_sqrtT_plus_one_le_2sqrtT h_60T_plus_g_le_120T h_nonneg_60T_plus_g h_2sqrtT_nonneg
      _ = 960 * (T : ℝ) * √(T : ℝ) := by ring
  -- Main inequality: Cst T * (lam0 T + beta * T + g) ≤ 962 * T * sqrt(T)
  have h_main : Cst T * (lam0 T + beta * (T : ℝ) + g) ≤ 962 * (T : ℝ) * √(T : ℝ) := by
    calc
      Cst T * (lam0 T + beta * (T : ℝ) + g) =
          Cst T * lam0 T + Cst T * beta * (T : ℝ) + Cst T * g := by ring
      _ = 2 + Cst T * 60 * (T : ℝ) + Cst T * g := by
        simp [h_Cst_lam0, beta]
      _ = 2 + Cst T * (60 * (T : ℝ) + g) := by ring
      _ ≤ (2 * (T : ℝ) * √(T : ℝ)) + Cst T * (60 * (T : ℝ) + g) := by
        have h2le : (2 : ℝ) ≤ 2 * (T : ℝ) * √(T : ℝ) := by
          have h_T_sqrtT_ge_one : (1 : ℝ) ≤ (T : ℝ) * √(T : ℝ) := by
            nlinarith
          nlinarith
        nlinarith
      _ ≤ (2 * (T : ℝ) * √(T : ℝ)) + 960 * (T : ℝ) * √(T : ℝ) := by
        nlinarith
      _ = 962 * (T : ℝ) * √(T : ℝ) := by ring
  -- Positivity for log monotonicity
  have h_pos : 0 < Cst T * (lam0 T + beta * (T : ℝ) + g) := by
    have h_Cst_pos : 0 < Cst T := by
      dsimp [Cst]
      have h_sqrt_pos : 0 < √(T : ℝ) := Real.sqrt_pos.mpr hT_pos
      nlinarith
    have h_lam0_pos : 0 < lam0 T := by
      dsimp [lam0]
      apply div_pos (by norm_num : (0 : ℝ) < 2) h_Cst_pos
    have h_betaT_nonneg : 0 ≤ beta * (T : ℝ) := by
      dsimp [beta]
      nlinarith
    have h_sum_pos : 0 < lam0 T + beta * (T : ℝ) + g := by nlinarith
    exact mul_pos h_Cst_pos h_sum_pos
  have h_rhs_pos : 0 < 962 * (T : ℝ) * √(T : ℝ) := by
    have h_sqrt_pos : 0 < √(T : ℝ) := Real.sqrt_pos.mpr hT_pos
    nlinarith
  -- Apply log monotonicity
  have h_log : log (Cst T * (lam0 T + beta * (T : ℝ) + g)) ≤ log (962 * (T : ℝ) * √(T : ℝ)) :=
    Real.log_le_log h_pos h_main
  -- Expand log of RHS
  have h_log_rhs : log (962 * (T : ℝ) * √(T : ℝ)) = log 962 + (3/2) * log (T : ℝ) := by
    have h962_ne_zero : (962 : ℝ) ≠ 0 := by norm_num
    have hT_ne_zero : (T : ℝ) ≠ 0 := by linarith
    have h_sqrtT_ne_zero : √(T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hT_pos)
    have h_962T_ne_zero : 962 * (T : ℝ) ≠ 0 := mul_ne_zero h962_ne_zero hT_ne_zero
    calc
      log (962 * (T : ℝ) * √(T : ℝ)) = log ((962 * (T : ℝ)) * √(T : ℝ)) := by ring
      _ = log (962 * (T : ℝ)) + log (√(T : ℝ)) := by
        rw [Real.log_mul h_962T_ne_zero h_sqrtT_ne_zero]
      _ = (log 962 + log (T : ℝ)) + log (√(T : ℝ)) := by
        rw [Real.log_mul h962_ne_zero hT_ne_zero]
      _ = (log 962 + log (T : ℝ)) + (log (T : ℝ) / 2) := by
        rw [Real.log_sqrt hT_nonneg]
      _ = log 962 + (3/2) * log (T : ℝ) := by ring
  -- Final calculation
  calc
    2 * log (Cst T * (lam0 T + beta * (T : ℝ) + g)) ≤ 2 * log (962 * (T : ℝ) * √(T : ℝ)) := by
      nlinarith
    _ = 2 * (log 962 + (3/2) * log (T : ℝ)) := by rw [h_log_rhs]
    _ = 3 * log (T : ℝ) + 2 * log 962 := by ring
    _ = 3 * log T + 2 * log 962 := by simp

theorem Phi_le {T : ℕ} (hT : 1 ≤ T) : Phi T T 0 ≤ 3 * log T + 2 * log 962 :=
  Phi_le_aux hT (G_nonneg 0) ((G_mono (by norm_num)).trans G_two_le)

theorem eventually_log (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in Filter.atTop, 3 * log T + K ≤ (3 + ε) * log T := by
  have hlog : Filter.Tendsto (fun (T : ℕ) => Real.log (T : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hge : ∀ᶠ (T : ℕ) in Filter.atTop, K / ε ≤ Real.log (T : ℝ) :=
    hlog.eventually_ge_atTop (K / ε)
  filter_upwards [hge] with T hT
  have hK : K ≤ ε * Real.log (T : ℝ) := by
    have := (div_le_iff₀ hε).mp hT
    -- this gives K ≤ log T * ε
    simpa [mul_comm] using this
  nlinarith

/-- The learner for outcomes in `[-B, B]`: it runs `learner` on `y / B` and predicts `B ŷ`. -/
noncomputable def learnerB (B : ℝ) (T : ℕ) : Learner T where
  predict t xs ys := B * (learner T).predict t xs (fun i => ys i / B)

theorem regret_learnerB {B : ℝ} (hB : 0 < B) {T : ℕ} (x y : Fin T → ℝ) :
    regret (learnerB B T) x y = B ^ 2 * regret (learner T) x (fun t => y t / B) := by
  have hy : (fun t => B * (y t / B)) = y := funext fun t => by field_simp
  have hb : bestLinearLoss x y = B ^ 2 * bestLinearLoss x (fun t => y t / B) := by
    conv_lhs => rw [← hy]
    exact bestLinearLoss_mul x (fun t => y t / B) B
  unfold regret learnerLoss
  rw [hb, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  show (B * (learner T).prediction x (fun t => y t / B) t - y t) ^ 2 =
    B ^ 2 * ((learner T).prediction x (fun t => y t / B) t - y t / B) ^ 2
  field_simp

/-- **The upper bound `UpperBound`.** -/
theorem upperBound : UpperBound := by
  intro B hB ε hε
  filter_upwards [eventually_log (2 * log 962) hε, Filter.eventually_ge_atTop 1] with T hT hT1
  refine ⟨learnerB B T, fun x y hy => ?_⟩
  rw [regret_learnerB hB]
  have hy' : ∀ t, |y t / B| ≤ 1 := fun t => by
    rw [abs_div, abs_of_pos hB, div_le_one hB]
    exact hy t
  have h1 := (regret_le x _ hy').trans (Phi_le hT1)
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  calc B ^ 2 * regret (learner T) x (fun t => y t / B) ≤ B ^ 2 * (3 * log T + 2 * log 962) :=
        mul_le_mul_of_nonneg_left h1 hB2
    _ ≤ B ^ 2 * ((3 + ε) * log T) := mul_le_mul_of_nonneg_left hT hB2
    _ = (3 + ε) * B ^ 2 * Real.log T := by ring

end RegretKappa.Upper
