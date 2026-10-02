import RegretKappa.UnknownBT.Anytime.TheoremB
import RegretKappa.UnknownBT.Anytime.Schedule

/-!
# The anytime schedule of `learnerB` as a potential schedule

The level `λ_t = a_t/b_t` and the normalizer `A_t = H₀(0)/b_t`, 0-indexed: the level
`lamB t` and the normalizer `AB t = H₀ / wB t` with `H₀ = a_0 + b_1 Γ(0)` (`H0B`). It is a
schedule (`isSchedule_B`: (H1) from the step inequality of the weights, (H2) from `a_t ≤ a_0` and
`b_t ≤ b_1`), and its terminal quantity `L_T = sup_{w² ≤ T} (w² - Ψ_{T-1}(w))` is at most the bound of
`theoremA` (`LT_le_RB`) and of `TheoremB` (`LT_le_first`, `LT_le_num`).
-/

namespace RegretKappa.UnknownBT

open RegretKappa.UpperSharp Real

/-- `H₀ = a_0 + b_1 Γ(0)`. -/
noncomputable def H0B : ℝ := alphaB 0 + betaB 0 * Gam 0

theorem H0B_pos : 0 < H0B := by
  have := Gam_nonneg 0
  have := alphaB_pos 0
  have := betaB_pos 0
  unfold H0B
  positivity

/-- The normalizer of the anytime schedule: `A t = H₀ / wB t`. -/
noncomputable def AB (t : ℕ) : ℝ := H0B / wB t

theorem lamB_mul_wB (t : ℕ) : lamB t * wB t = alphaB (t + 1) := by
  have h := levelOf_B t
  unfold levelOf at h
  have hb : betaB (t + 1) = wB t := by simp [betaB]
  rw [hb] at h
  rw [← h, div_mul_cancel₀ _ (wB_pos' t).ne']

/-- **The anytime schedule** satisfies (H1) and (H2). -/
theorem isSchedule_B : IsSchedule lamB AB where
  lam_pos t := by
    rw [← levelOf_B]
    exact div_pos (alphaB_pos _) (betaB_pos _)
  A_pos t := div_pos H0B_pos (wB_pos' t)
  h1 t w := by
    unfold AB
    rw [div_div_eq_mul_div, div_div_eq_mul_div]
    apply div_le_div_of_nonneg_right _ H0B_pos.le
    have e1 : (lamB (t + 1) + 3 + Gam w) * wB (t + 1) =
        alphaB (t + 1 + 1) + 3 * wB (t + 1) + wB (t + 1) * Gam w := by
      rw [add_mul, add_mul, lamB_mul_wB]
      ring
    have e2 : (lamB t + Gam w) * wB t = alphaB (t + 1) + wB t * Gam w := by
      rw [add_mul, lamB_mul_wB]
      ring
    rw [e1, e2]
    have h := hstepB (t + 1) w
    have hb1 : betaB (t + 1 + 1) = wB (t + 1) := by simp [betaB]
    have hb0 : betaB (t + 1) = wB t := by simp [betaB]
    rw [hb1, hb0] at h
    exact h
  h2 t := by
    unfold AB
    rw [le_div_iff₀ (wB_pos' t)]
    have e : (lamB t + 3 + Gam 0) * wB t = alphaB (t + 1) + 3 * wB t + wB t * Gam 0 := by
      rw [add_mul, add_mul, lamB_mul_wB]
      ring
    rw [e, alphaB_rec]
    unfold H0B
    have h1 := alphaB_le_alphaB_zero t
    have h2 := mul_le_mul_of_nonneg_right (wB_le_wB_zero t) (Gam_nonneg 0)
    have hb0 : betaB 0 = wB 0 := by simp [betaB]
    rw [hb0]
    linarith

/-- The potential after round `T - 1` of the anytime schedule is `2 log(H_T(w)/H₀)`. -/
theorem psiOf_B {T : ℕ} (hT : 1 ≤ T) (w : ℝ) :
    psiOf lamB AB (T - 1) w = 2 * log (alphaB T + betaB T * Gam w) - 2 * log H0B := by
  have hm := lamB_mul_wB (T - 1)
  rw [Nat.sub_add_cancel hT] at hm
  have hb : betaB T = wB (T - 1) := rfl
  have hw := wB_pos' (T - 1)
  have hG := Gam_nonneg w
  have hp : 0 < alphaB T + betaB T * Gam w := by
    have := alphaB_pos T
    have := betaB_pos T
    positivity
  have e : (lamB (T - 1) + Gam w) / AB (T - 1) = (alphaB T + betaB T * Gam w) / H0B := by
    unfold AB
    rw [div_div_eq_mul_div, hb, ← hm]
    ring
  unfold psiOf
  rw [e, Real.log_div hp.ne' H0B_pos.ne']
  ring

/-- **The bound on `L_T`, first form** (as in `theoremA`): for `T ≥ 1` and `w² ≤ T`,
`w² - Ψ_{T-1}(w) ≤ 2 log H₀ + 2 log((√T + 1)/(√(2π) b_T))`. -/
theorem LT_le_RB {T : ℕ} (hT : 1 ≤ T) {w : ℝ} (hw : w ^ 2 ≤ T) :
    w ^ 2 - psiOf lamB AB (T - 1) w ≤
      2 * log H0B + 2 * log ((√(T : ℝ) + 1) / (√(2 * π) * betaB T)) := by
  have h := terminal_anytime (alphaB_pos T) (betaB_pos T) (terminal_condB hT) hw
  rw [psiOf_B hT]
  linarith

/-- The bound of `theoremA` for the weights of `learnerB`, in the first form of `TheoremB`. -/
theorem RB_le_first {T : ℕ} (hT : 1 ≤ T) :
    2 * log H0B + 2 * log ((√(T : ℝ) + 1) / (√(2 * π) * betaB T)) ≤
      3 * log T + 4 * log (log (T + 2)) + constK + 2 * log (1 + 1 / √(T : ℝ)) +
        2 * log (1 + 2 / T) := by
  have h := closed_form T hT (betaB T) (betaB_lower hT)
  unfold H0B
  rw [H0_eq]
  unfold constK
  linarith

/-- The bound of `theoremA` for the weights of `learnerB`, in the second form of `TheoremB`. -/
theorem RB_le_num {T : ℕ} (hT : 1 ≤ T) :
    2 * log H0B + 2 * log ((√(T : ℝ) + 1) / (√(2 * π) * betaB T)) ≤
      3 * log T + 4 * log (log (T + 2)) + 1.3706 + 2 / √(T : ℝ) + 4 / T := by
  have h := RB_le_first hT
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

/-- **The bound on `L_T`, first form of `TheoremB`.** -/
theorem LT_le_first {T : ℕ} (hT : 1 ≤ T) {w : ℝ} (hw : w ^ 2 ≤ T) :
    w ^ 2 - psiOf lamB AB (T - 1) w ≤
      3 * log T + 4 * log (log (T + 2)) + constK + 2 * log (1 + 1 / √(T : ℝ)) +
        2 * log (1 + 2 / T) :=
  (LT_le_RB hT hw).trans (RB_le_first hT)

/-- **The bound on `L_T`, second form of `TheoremB`**: for `T ≥ 1` and `w² ≤ T`,
`w² - Ψ_{T-1}(w) ≤ 3 log T + 4 log log(T + 2) + 1.3706 + 2/√T + 4/T`. -/
theorem LT_le_num {T : ℕ} (hT : 1 ≤ T) {w : ℝ} (hw : w ^ 2 ≤ T) :
    w ^ 2 - psiOf lamB AB (T - 1) w ≤
      3 * log T + 4 * log (log (T + 2)) + 1.3706 + 2 / √(T : ℝ) + 4 / T :=
  (LT_le_RB hT hw).trans (RB_le_num hT)

end RegretKappa.UnknownBT
