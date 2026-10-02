import RegretKappa.CorollariesCheck.Junk
import RegretKappa.CorollariesCheck.Indep42a

/-!
# The first separate formalization of Remark 5.2 (randomized learners on one play): refuted

`Indep42a` calls it Corollary 4.2, its number in the text it was written from.

`Indep42a` models a randomized learner as a probability measure on `Learner T`, with the trivial
σ-algebra `⊥` on `Learner T` (its comment calls it discrete), and its expected regret as
`E (Reg⁺) - E (Reg⁻)`, two lintegrals subtracted in `EReal`. For `⊥` the lintegral of a function
that vanishes at some learner is `0` (`lintegral_bot_eq_zero`). On every play the learner that
predicts the outcomes has `Reg ≤ 0`, and the learner that predicts twice the outcomes has `Reg ≥ 0`
(`regret_perfect_nonpos`, `regret_double_nonneg`). So both lintegrals vanish, every randomized
learner has expected regret `0` on every play (`expectedRegret_eq_zero`), and
`Indep42a.RandLowerBound` is false (`not_randLowerBound`).
-/

namespace RegretKappa.CorollariesCheck

open MeasureTheory Filter

theorem expectedRegret_eq_zero {T : ℕ} (L : Indep42a.RandLearner T) (x y : Fin T → ℝ) :
    L.expectedRegret x y = 0 := by
  have h1 : ∫⁻ ω, ENNReal.ofReal (max (regret ω x y) 0) ∂L.μ = 0 :=
    lintegral_bot_eq_zero (a := perfect y) (by
      rw [max_eq_right (regret_perfect_nonpos x y), ENNReal.ofReal_zero])
  have h2 : ∫⁻ ω, ENNReal.ofReal (max (-regret ω x y) 0) ∂L.μ = 0 :=
    lintegral_bot_eq_zero (a := double y) (by
      rw [max_eq_right (by linarith [regret_double_nonneg x y]), ENNReal.ofReal_zero])
  unfold Indep42a.RandLearner.expectedRegret
  simp only [h1, h2, EReal.coe_ennreal_zero, sub_zero]

theorem not_randLowerBound : ¬Indep42a.RandLowerBound := by
  intro h
  obtain ⟨T, hT, hT2⟩ := ((h 1 one_pos 1 one_pos).and (eventually_ge_atTop 2)).exists
  have hprob : IsProbabilityMeasure (Measure.dirac (constLearner T 0)) := inferInstance
  obtain ⟨x, y, -, hc⟩ := hT ⟨Measure.dirac (constLearner T 0)⟩
  have e : (3 - ((1 : ℝ) : EReal)) * ((1 : ℝ) : EReal) ^ 2 * ((Real.log T : ℝ) : EReal) =
      (((3 - 1) * 1 ^ 2 * Real.log T : ℝ) : EReal) := by
    rw [← coe_three, ← EReal.coe_sub, ← EReal.coe_pow, ← EReal.coe_mul, ← EReal.coe_mul]
  rw [e, expectedRegret_eq_zero] at hc
  exact absurd (EReal.coe_nonpos.1 hc) (not_le.2 (bound_pos hT2))

end RegretKappa.CorollariesCheck
