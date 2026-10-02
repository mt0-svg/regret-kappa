import RegretKappa.Corollaries.Transfer
import RegretKappa.Corollaries.Expectation

/-!
# Explicit lower bounds over bounded features

The transfer of an explicit lower bound to bounded features, with no asymptotics. Suppose every
deterministic learner has weighted regret at least `b` against a finite family of plays with
nonnegative features and outcomes in `{-1, 0, 1}`, with weights `w ≥ 0` of sum `1`. Then for
every `B > 0` (`boundedFeatures_of_mixture`):
* the adversary that plays the scaled plays with the same weights, with features in `[0, 1]` and
  outcomes in `{-B, 0, B}`, forces expected regret at least `B ^ 2 b` on every randomized learner
  (the adversary for bounded features);
* every randomized learner has expected regret at least `B ^ 2 b` on one such play, every
  deterministic learner has regret at least `B ^ 2 b` on one such play, and so `B ^ 2 b` is at
  most `minimaxRegretBF T B` and `minimaxRegretBFI T B` (the randomized lower bound and the chain of
  inequalities for bounded features).

The scaling is `transfer`; the expectations are `le_advRegret`, `advRegret_eq_sum` and
`exists_le_of_le_sum`. An explicit lower bound `b(T)`, stated as a bound on
the weighted regret of every deterministic learner against the finitely many plays of its
adversary, transfers in this form.
-/

namespace RegretKappa.Corollaries

open MeasureTheory

universe u

/-- **Bounded features, for a given finite family of plays.** A lower bound `b` on the
weighted regret of every deterministic learner against plays with nonnegative features and
outcomes in `{-1, 0, 1}`, with weights `w ≥ 0` of sum `1`, gives `B ^ 2 b` over features in
`[0, 1]` and outcomes in `{-B, 0, B}`: against the scaled adversary for randomized learners, on
one play for randomized and for deterministic learners, and for both minimax regrets. -/
theorem boundedFeatures_of_mixture {T : ℕ} {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (x y : ι → Fin T → ℝ) (hx : ∀ i t, 0 ≤ x i t)
    (hy : ∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) {b : ℝ}
    (hb : ∀ L : Learner T, b ≤ ∑ i, w i * regret L (x i) (y i)) {B : ℝ} (hB : 0 < B) :
    (∃ x' y' : ι → Fin T → ℝ, (∀ i t, x' i t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ i t, y' i t ∈ ({-B, 0, B} : Set ℝ)) ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
          IsRandLearner μ L → ((B ^ 2 * b : ℝ) : EReal) ≤ advRegret μ L w x' y') ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
          IsRandLearner μ L → ∃ x' y' : Fin T → ℝ, (∀ t, x' t ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ t, y' t ∈ ({-B, 0, B} : Set ℝ)) ∧
            ((B ^ 2 * b : ℝ) : EReal) ≤ expRegret μ L x' y') ∧
      (∀ L : Learner T, ∃ x' y' : Fin T → ℝ, (∀ t, x' t ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ t, y' t ∈ ({-B, 0, B} : Set ℝ)) ∧ B ^ 2 * b ≤ regret L x' y') ∧
      ((B ^ 2 * b : ℝ) : EReal) ≤ minimaxRegretBF T B ∧
      ((B ^ 2 * b : ℝ) : EReal) ≤ minimaxRegretBFI T B := by
  obtain ⟨x', y', hx', hy', h⟩ := transfer w x y hx hy hb hB
  have hadv : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
      IsRandLearner μ L → ((B ^ 2 * b : ℝ) : EReal) ≤ advRegret μ L w x' y' := by
    intro Ω _ μ L hL
    have := hL.1
    exact le_advRegret μ L w hw x' y' _ fun ω => h (L ω)
  have hrand : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
      IsRandLearner μ L → ∃ x'' y'' : Fin T → ℝ, (∀ t, x'' t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y'' t ∈ ({-B, 0, B} : Set ℝ)) ∧
        ((B ^ 2 * b : ℝ) : EReal) ≤ expRegret μ L x'' y'' := by
    intro Ω _ μ L hL
    have hc := hadv Ω μ L hL
    rw [advRegret_eq_sum μ hL.2] at hc
    obtain ⟨i, hi⟩ := exists_le_of_le_sum w hw hs _ _ _ hc
    exact ⟨x' i, y' i, hx' i, hy' i, hi⟩
  have hdet : ∀ L : Learner T, ∃ x'' y'' : Fin T → ℝ, (∀ t, x'' t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, y'' t ∈ ({-B, 0, B} : Set ℝ)) ∧ B ^ 2 * b ≤ regret L x'' y'' := by
    intro L
    obtain ⟨x'', y'', hx'', hy'', hc⟩ := hrand PUnit.{u + 1} (Measure.dirac PUnit.unit)
      (fun _ => L) (isRandLearner_const _ L)
    rw [expRegret_const] at hc
    exact ⟨x'', y'', hx'', hy'', EReal.coe_le_coe_iff.1 hc⟩
  have hBF := le_minimaxRegretBF hdet
  exact ⟨⟨x', y', hx', hy', hadv⟩, hrand, hdet, hBF, hBF.trans (minimaxRegretBF_le_BFI T hB)⟩

end RegretKappa.Corollaries
