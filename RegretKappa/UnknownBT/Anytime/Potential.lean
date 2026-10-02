import RegretKappa.UnknownBT.Anytime.Learner

/-!
# The anytime potential along the play

A schedule of potentials `H_n(ρ) = α n + β n Γ(ρ)` (`n` rounds played) with `α n > 0`, `β n > 0`
and, for every round `t` and every `ρ`,

`α (t + 1) + 3 β (t + 1) + β (t + 1) Γ(ρ) ≤ α t + β t Γ(ρ)`,

drives the learner `learnerLam` with the level `λ_t = α (t + 1) / β (t + 1)`: the learner's
partial loss plus `2 log H_n(ρ_n)` does not increase (`potential_leLam`), so a terminal bound
`ρ² ≤ 2 log H_T(ρ) + R` for `ρ² ≤ T` gives
`Regret_T ≤ 2 log H_0(0) + R` (`regret_leLam`). The anytime weights of `theoremA` are
`α = a`, `β n = b_n` (with `b_0 = b_1`), where the inequality is `a_t = a_{t+1} + 3 b_{t+1}` and
`b_{t+1} ≤ b_t`; the known horizon is `α n = C (λ₀ + 3 (T - n))`, `β n = C`.
-/

namespace RegretKappa.UnknownBT

open RegretKappa RegretKappa.UpperSharp Real Finset

/-- The level `λ_t = α (t + 1) / β (t + 1)` of a schedule. -/
noncomputable def levelOf (α β : ℕ → ℝ) (t : ℕ) : ℝ := α (t + 1) / β (t + 1)

/-- **The potential along the play.** Along a play with outcomes in `[-1, 1]`, the partial
loss of `learnerLam (levelOf α β)` plus `2 log(α n + β n Γ(ρ_n))` is at most `2 log(α 0 + β 0 Γ(0))`. -/
theorem potential_leLam (α β : ℕ → ℝ) (hα : ∀ n, 0 < α n) (hβ : ∀ n, 0 < β n)
    (hstep : ∀ t ρ, α (t + 1) + 3 * β (t + 1) + β (t + 1) * Gam ρ ≤ α t + β t * Gam ρ)
    {T : ℕ} (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) (n : ℕ) (hn : n ≤ T) :
    ∑ i ∈ range n, (yhatLam (levelOf α β) x y i ^ 2 -
        2 * yhatLam (levelOf α β) x y i * Upper.ext y i) +
      2 * log (α n + β n * Gam (Upper.Ssum x y n / √(Upper.Vsum x n))) ≤
        2 * log (α 0 + β 0 * Gam 0) := by
  induction n with
  | zero => simp [Upper.Ssum, Upper.Vsum]
  | succ n ih =>
    refine le_trans ?_ (ih (Nat.le_of_succ_le hn))
    have hb := hβ (n + 1)
    have hlam : 0 < levelOf α β n := div_pos (hα (n + 1)) hb
    have hs := stepLam (x := Upper.ext x n) hlam (Upper.Vsum_nonneg x n)
      (Ssum_eq_zero_of_Vsum x hy n) (Upper.abs_ext_le hy n)
    have hS1 : Upper.Ssum x y (n + 1) = Upper.Ssum x y n + Upper.ext x n * Upper.ext y n :=
      Finset.sum_range_succ _ _
    have hV1 : Upper.Vsum x (n + 1) = Upper.Vsum x n + Upper.ext x n ^ 2 :=
      Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, hS1, hV1]
    set ρ := Upper.Ssum x y n / √(Upper.Vsum x n)
    set ρ' := (Upper.Ssum x y n + Upper.ext x n * Upper.ext y n) /
      √(Upper.Vsum x n + Upper.ext x n ^ 2)
    have hG := Gam_nonneg ρ
    have hG' := Gam_nonneg ρ'
    have e1 : α (n + 1) + β (n + 1) * Gam ρ' = β (n + 1) * (levelOf α β n + Gam ρ') := by
      unfold levelOf; field_simp
    have e2 : α (n + 1) + 3 * β (n + 1) + β (n + 1) * Gam ρ =
        β (n + 1) * (levelOf α β n + 3 + Gam ρ) := by
      unfold levelOf; field_simp
    have p1 : 0 < levelOf α β n + Gam ρ' := by linarith
    have p2 : 0 < levelOf α β n + 3 + Gam ρ := by linarith
    have hmono : log (α (n + 1) + 3 * β (n + 1) + β (n + 1) * Gam ρ) ≤
        log (α n + β n * Gam ρ) :=
      Real.log_le_log (by rw [e2]; positivity) (hstep n ρ)
    have l1 : log (α (n + 1) + β (n + 1) * Gam ρ') =
        log (β (n + 1)) + log (levelOf α β n + Gam ρ') := by
      rw [e1, Real.log_mul hb.ne' p1.ne']
    have l2 : log (α (n + 1) + 3 * β (n + 1) + β (n + 1) * Gam ρ) =
        log (β (n + 1)) + log (levelOf α β n + 3 + Gam ρ) := by
      rw [e2, Real.log_mul hb.ne' p2.ne']
    unfold yhatLam
    linarith

/-- **The reduction to the terminal condition.** If `ρ² ≤ 2 log(α T + β T Γ(ρ)) + R`
for every `ρ² ≤ T`, then on every play with outcomes in `[-1, 1]`,
`Regret_T ≤ 2 log(α 0 + β 0 Γ(0)) + R`. -/
theorem regret_leLam (α β : ℕ → ℝ) (hα : ∀ n, 0 < α n) (hβ : ∀ n, 0 < β n)
    (hstep : ∀ t ρ, α (t + 1) + 3 * β (t + 1) + β (t + 1) * Gam ρ ≤ α t + β t * Gam ρ)
    {T : ℕ} (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) (R : ℝ)
    (hterm : ∀ ρ : ℝ, ρ ^ 2 ≤ T → ρ ^ 2 ≤ 2 * log (α T + β T * Gam ρ) + R) :
    regret ((learnerLam (levelOf α β)).restrict T) x y ≤ 2 * log (α 0 + β 0 * Gam 0) + R := by
  have h1 := potential_leLam α β hα hβ hstep x y hy T le_rfl
  have h2 := hterm _ (Upper.rho_sq_le x hy T)
  rw [regret_eqLam]
  linarith

end RegretKappa.UnknownBT
