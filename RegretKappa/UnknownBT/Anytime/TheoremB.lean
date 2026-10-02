import RegretKappa.UnknownBT.Anytime.Potential
import RegretKappa.UnknownBT.Anytime.Weights

/-!
# The anytime potential bound and `TheoremB`

The terminal lemma (`terminal_anytime`): for `a, b > 0` with
`√(2π) e^{min(4, T)/2} b ≤ a (√T + 1)` and `ρ² ≤ T`,
`ρ² ≤ 2 log(a + b Γ(ρ)) + 2 log((√T + 1)/(√(2π) b))`. With the potential of `Potential.lean` this is
`theoremA`: `Regret_T ≤ 2 log(a_0 + b_1 Γ(0)) + 2 log((√T + 1)/(√(2π) b_T))`.

The weights of `TheoremB`, 0-indexed: `alphaB n = 3/log(n + 2)` (the tail `a_n`),
`wB t = 1/log(t + 2) - 1/log(t + 3)` (the weight of round `t`), `betaB n = wB (n - 1)` (the weight
`b_n` of the potential after `n` rounds, with `b_0 = b_1`: the truncated subtraction `0 - 1 = 0` is
meant). The level `levelOf alphaB betaB` is `lamB` (`levelOf_B`), so `learnerB` is the potential
learner of this schedule, and `theoremB`, `theoremBNum` prove the two forms `TheoremB` and
`TheoremBNum` of the statement.
-/

namespace RegretKappa.UnknownBT

open RegretKappa RegretKappa.UpperSharp Real Finset

/-- `Γ` is even: `Γ(|ρ|) = Γ(ρ)`. -/
theorem Gam_abs (ρ : ℝ) : Gam |ρ| = Gam ρ := by
  rcases abs_choice ρ with h | h <;> rw [h]
  exact Gam_neg ρ

/-- **The terminal lemma** (the terminal condition of `theoremA`). -/
theorem terminal_anytime {T : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcond : √(2 * π) * exp (min 4 (T : ℝ) / 2) * b ≤ a * (√(T : ℝ) + 1)) {ρ : ℝ}
    (hρ : ρ ^ 2 ≤ T) :
    ρ ^ 2 ≤ 2 * log (a + b * Gam ρ) + 2 * log ((√(T : ℝ) + 1) / (√(2 * π) * b)) := by
  have hs : 0 < √(2 * π) := by positivity
  have hT1 : 0 < √(T : ℝ) + 1 := by positivity
  have hG := Gam_nonneg ρ
  have hpos : 0 < a + b * Gam ρ := by positivity
  have hC : 0 < (√(T : ℝ) + 1) / (√(2 * π) * b) := by positivity
  suffices h : exp (ρ ^ 2 / 2) * (√(2 * π) * b) ≤ (√(T : ℝ) + 1) * (a + b * Gam ρ) by
    have h' : exp (ρ ^ 2 / 2) ≤ (√(T : ℝ) + 1) / (√(2 * π) * b) * (a + b * Gam ρ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact h
    have := (Real.le_log_iff_exp_le (by positivity)).2 h'
    rw [Real.log_mul hC.ne' hpos.ne'] at this
    linarith
  rcases le_or_gt 2 |ρ| with h2 | h2
  · have ht := terminal_ineq h2
    rw [sq_abs, Gam_abs] at ht
    have hρT : |ρ| ≤ √(T : ℝ) := Real.abs_le_sqrt hρ
    have h1 : (|ρ| + 1) * Gam ρ ≤ (√(T : ℝ) + 1) * Gam ρ :=
      mul_le_mul_of_nonneg_right (by linarith) hG
    have h3 : √(2 * π) * exp (ρ ^ 2 / 2) * b ≤ (√(T : ℝ) + 1) * Gam ρ * b :=
      mul_le_mul_of_nonneg_right (ht.trans h1) hb.le
    have h4 : 0 ≤ (√(T : ℝ) + 1) * a := by positivity
    nlinarith
  · have hm : ρ ^ 2 ≤ min 4 (T : ℝ) := by
      refine le_min ?_ hρ
      have : ρ ^ 2 = |ρ| ^ 2 := (sq_abs ρ).symm
      nlinarith [abs_nonneg ρ]
    have he : exp (ρ ^ 2 / 2) ≤ exp (min 4 (T : ℝ) / 2) := exp_le_exp.2 (by linarith)
    have h3 : exp (ρ ^ 2 / 2) * (√(2 * π) * b) ≤ exp (min 4 (T : ℝ) / 2) * (√(2 * π) * b) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    have h4 : 0 ≤ (√(T : ℝ) + 1) * (b * Gam ρ) := by positivity
    nlinarith

/-- **The anytime bound** (with its terminal condition): for a schedule `α + β Γ` as in
`potential_leLam`,
`T ≥ 1` with `√(2π) e^{min(4, T)/2} β T ≤ α T (√T + 1)`, and every play with outcomes in
`[-1, 1]`, `Regret_T ≤ 2 log(α 0 + β 0 Γ(0)) + 2 log((√T + 1)/(√(2π) β T))`. -/
theorem theoremA (α β : ℕ → ℝ) (hα : ∀ n, 0 < α n) (hβ : ∀ n, 0 < β n)
    (hstep : ∀ t ρ, α (t + 1) + 3 * β (t + 1) + β (t + 1) * Gam ρ ≤ α t + β t * Gam ρ)
    {T : ℕ} (hcond : √(2 * π) * exp (min 4 (T : ℝ) / 2) * β T ≤ α T * (√(T : ℝ) + 1))
    (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) :
    regret ((learnerLam (levelOf α β)).restrict T) x y ≤
      2 * log (α 0 + β 0 * Gam 0) + 2 * log ((√(T : ℝ) + 1) / (√(2 * π) * β T)) :=
  regret_leLam α β hα hβ hstep x y hy _ fun _ hρ => terminal_anytime (hα T) (hβ T) hcond hρ

/-! ## The weights of `TheoremB` -/

/-- The tail `a_n = 3/log(n + 2)` (0-indexed: `3 ∑` of the weights of the rounds `≥ n`). -/
noncomputable def alphaB (n : ℕ) : ℝ := 3 / log ((n : ℝ) + 2)

/-- The weight of round `t`: `1/log(t + 2) - 1/log(t + 3)`. -/
noncomputable def wB (t : ℕ) : ℝ := 1 / log ((t : ℝ) + 2) - 1 / log ((t : ℝ) + 3)

/-- The weight of the potential after `n` rounds: `wB (n - 1)`, so `betaB 0 = betaB 1 = wB 0`. -/
noncomputable def betaB (n : ℕ) : ℝ := wB (n - 1)

theorem log_add_two_pos (t : ℕ) : 0 < log ((t : ℝ) + 2) :=
  Real.log_pos (by linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)])

theorem alphaB_pos (n : ℕ) : 0 < alphaB n := div_pos (by norm_num) (log_add_two_pos n)

theorem wB_pos' (t : ℕ) : 0 < wB t := wB_pos t

theorem betaB_pos (n : ℕ) : 0 < betaB n := wB_pos (n - 1)

theorem wB_succ_le (t : ℕ) : wB (t + 1) ≤ wB t := by
  have h := wB_antitone t
  unfold wB
  push_cast
  rw [show (t : ℝ) + 1 + 2 = (t : ℝ) + 3 by ring, show (t : ℝ) + 1 + 3 = (t : ℝ) + 4 by ring]
  exact h

theorem betaB_succ_le (t : ℕ) : betaB (t + 1) ≤ betaB t := by
  unfold betaB
  rcases t with _ | t
  · exact le_rfl
  · simpa using wB_succ_le t

theorem wB_le_wB_zero (t : ℕ) : wB t ≤ wB 0 := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (wB_succ_le t).trans ih

/-- The recursion `a_t = a_{t+1} + 3 b_{t+1}` (0-indexed: `alphaB t = alphaB (t + 1) + 3 wB t`). -/
theorem alphaB_rec (t : ℕ) : alphaB (t + 1) + 3 * wB t = alphaB t := by
  unfold alphaB wB
  push_cast
  have e : (t : ℝ) + 1 + 2 = (t : ℝ) + 3 := by ring
  rw [e]
  ring

theorem alphaB_le_alphaB_zero (n : ℕ) : alphaB n ≤ alphaB 0 := by
  unfold alphaB
  apply div_le_div_of_nonneg_left (by norm_num) (log_add_two_pos 0)
  exact Real.log_le_log (by norm_num) (by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

/-- The step inequality of the schedule `alphaB + betaB Γ`. -/
theorem hstepB (t : ℕ) (ρ : ℝ) :
    alphaB (t + 1) + 3 * betaB (t + 1) + betaB (t + 1) * Gam ρ ≤ alphaB t + betaB t * Gam ρ := by
  have hb : betaB (t + 1) = wB t := by simp [betaB]
  have h1 := alphaB_rec t
  have h2 := mul_le_mul_of_nonneg_right (betaB_succ_le t) (Gam_nonneg ρ)
  rw [hb] at h2 ⊢
  linarith

/-- The level of the schedule is `lamB`. -/
theorem levelOf_B (t : ℕ) : levelOf alphaB betaB t = lamB t := by
  have h2 := log_add_two_pos t
  have h3 : 0 < log ((t : ℝ) + 3) := Real.log_pos (by linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)])
  have hlt : log ((t : ℝ) + 2) < log ((t : ℝ) + 3) := Real.log_lt_log (by positivity) (by linarith)
  have hd : log (((t : ℝ) + 3) / ((t : ℝ) + 2)) = log ((t : ℝ) + 3) - log ((t : ℝ) + 2) :=
    Real.log_div (by positivity) (by positivity)
  unfold levelOf lamB alphaB betaB wB
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [show (t : ℝ) + 1 + 2 = (t : ℝ) + 3 by ring, hd]
  have hne : log ((t : ℝ) + 3) - log ((t : ℝ) + 2) ≠ 0 := by linarith
  field_simp

theorem learnerB_eq_level : learnerB = learnerLam (levelOf alphaB betaB) := by
  rw [learnerB_eq]
  congr 1
  funext t
  exact (levelOf_B t).symm

/-- `a_T / b_T = λ_{T-1}` for `T ≥ 1`, that is `alphaB T = lamB (T - 1) * betaB T`. -/
theorem alphaB_eq_lamB {T : ℕ} (hT : 1 ≤ T) : alphaB T = lamB (T - 1) * betaB T := by
  have h := levelOf_B (T - 1)
  unfold levelOf at h
  rw [Nat.sub_add_cancel hT] at h
  rw [← h, div_mul_cancel₀ _ (betaB_pos T).ne']

/-- The terminal condition of `theoremA` for the weights of `TheoremB`. -/
theorem terminal_condB {T : ℕ} (hT : 1 ≤ T) :
    √(2 * π) * exp (min 4 (T : ℝ) / 2) * betaB T ≤ alphaB T * (√(T : ℝ) + 1) := by
  have hc := terminal_cond T hT
  have hcast : ((T - 1 : ℕ) : ℝ) + 2 = (T : ℝ) + 1 := by
    rw [Nat.cast_sub hT]; push_cast; ring
  have hl' : 3 * (((T - 1 : ℕ) : ℝ) + 2) * log (((T - 1 : ℕ) : ℝ) + 2) ≤ lamB (T - 1) :=
    lamB_lower (T - 1)
  rw [hcast] at hl'
  rw [alphaB_eq_lamB hT]
  have hb := betaB_pos T
  have hs : 0 < √(T : ℝ) + 1 := by positivity
  calc √(2 * π) * exp (min 4 (T : ℝ) / 2) * betaB T
      ≤ 3 * ((T : ℝ) + 1) * log ((T : ℝ) + 1) * (√(T : ℝ) + 1) * betaB T :=
        mul_le_mul_of_nonneg_right hc hb.le
    _ ≤ lamB (T - 1) * (√(T : ℝ) + 1) * betaB T := by
        gcongr
    _ = lamB (T - 1) * betaB T * (√(T : ℝ) + 1) := by ring

/-- **`theoremA` for the weights of `TheoremB`**: for `T ≥ 1` and outcomes in `[-1, 1]`,
`Regret_T ≤ 2 log(a_0 + b_1 Γ(0)) + 2 log((√T + 1)/(√(2π) b_T))`. -/
theorem regret_le_RB {T : ℕ} (hT : 1 ≤ T) (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) :
    regret (learnerB.restrict T) x y ≤
      2 * log (alphaB 0 + betaB 0 * Gam 0) +
        2 * log ((√(T : ℝ) + 1) / (√(2 * π) * betaB T)) := by
  rw [learnerB_eq_level]
  exact theoremA alphaB betaB alphaB_pos betaB_pos hstepB (terminal_condB hT) x y hy

theorem H0_eq : alphaB 0 + betaB 0 * Gam 0 =
    3 / log 2 + 2 * exp (-1 / 2) * (1 / log 2 - 1 / log 3) := by
  rw [Gam_zero]
  simp only [alphaB, betaB, wB, Nat.zero_sub, Nat.cast_zero, zero_add]
  norm_num
  ring

theorem betaB_lower {T : ℕ} (hT : 1 ≤ T) :
    1 / (((T : ℝ) + 2) * log ((T : ℝ) + 2) ^ 2) ≤ betaB T := by
  have h := wB_lower T hT
  unfold betaB wB
  rw [Nat.cast_sub hT]
  push_cast
  convert h using 3 <;> ring_nf

/-- **`TheoremB`**, the first form. -/
theorem theoremB : TheoremB := by
  intro T hT x y hy
  have h1 := regret_le_RB hT x y hy
  have h2 := closed_form T hT (betaB T) (betaB_lower hT)
  rw [H0_eq] at h1
  unfold constK
  linarith

/-- The constant `K` of `TheoremB` is at most `1.3706`. -/
theorem constK_le_num : constK ≤ 1.3706 :=
  constK_le log_three_lt exp_neg_half_bounds.2 exp_lower

/-- **`TheoremBNum`**, the second form. -/
theorem theoremBNum : TheoremBNum := by
  intro T hT x y hy
  have h := theoremB T hT x y hy
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < √(T : ℝ) := Real.sqrt_pos.2 hT0
  have l1 : log (1 + 1 / √(T : ℝ)) ≤ 1 / √(T : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / √(T : ℝ))
    linarith
  have l2 : log (1 + 2 / (T : ℝ)) ≤ 2 / T := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 2 / (T : ℝ))
    linarith
  have hK := constK_le_num
  have e1 : 2 / √(T : ℝ) = 2 * (1 / √(T : ℝ)) := by ring
  have e2 : 4 / (T : ℝ) = 2 * (2 / T) := by ring
  rw [e1, e2]
  linarith

end RegretKappa.UnknownBT
