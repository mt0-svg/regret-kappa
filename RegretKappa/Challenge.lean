import RegretKappa.Challenge.LowerSharp
import RegretKappa.Challenge.Corollaries
import RegretKappa.Challenge.UpperSharp

/-! Challenge module for Comparator (config.json): the definitions of `RegretKappa/MainStatement.lean`, copied in order
with their docstrings and the theorems left out, and the targets with `sorry`. Nothing outside the challenge imports it. -/

namespace RegretKappa

open Real MeasureTheory

universe u

noncomputable def boundU (T : ℕ) : ℝ :=
  2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))

noncomputable def boundL (T : ℕ) : ℝ := 3 * log T - 2 * log (log T) - 15.2

def MainTheorem : Prop :=
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, LowerSharp.T0 ≤ T →
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ minimaxRegret T B ∧
      minimaxRegret T B ≤ ((B ^ 2 * (3 * log T + 0.37) : ℝ) : EReal)) ∧
  KappaEqThree

def MainTheoremChain : Prop :=
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, LowerSharp.T0 ≤ T →
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ∧
      ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ≤ minimaxRegret T B ∧
      minimaxRegret T B ≤ ((B ^ 2 * boundU T : ℝ) : EReal)) ∧
  KappaEqThree

def MainBoundedFeatures : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ, LowerSharp.T0 ≤ T →
    (∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
        Corollaries.IsRandLearner μ L →
          ((B ^ 2 * boundL T : ℝ) : EReal) ≤ Corollaries.advRegret μ L w x y) ∧
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ Corollaries.minimaxRegretBF T B ∧
    Corollaries.minimaxRegretBF T B ≤ Corollaries.minimaxRegretBFI T B ∧
    Corollaries.minimaxRegretBFI T B ≤ ((B ^ 2 * (3 * log T + 0.37) : ℝ) : EReal)

def MainBoundedFeaturesChain : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ, LowerSharp.T0 ≤ T →
    (∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
        Corollaries.IsRandLearner μ L →
          ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ≤ Corollaries.advRegret μ L w x y) ∧
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ∧
    ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ≤ Corollaries.minimaxRegretBF T B ∧
    Corollaries.minimaxRegretBF T B ≤ Corollaries.minimaxRegretBFI T B ∧
    Corollaries.minimaxRegretBFI T B ≤ ((B ^ 2 * boundU T : ℝ) : EReal)

theorem main : MainTheorem := sorry

theorem mainChain : MainTheoremChain := sorry

theorem mainBoundedFeatures : MainBoundedFeatures.{u} := sorry

theorem mainBoundedFeaturesChain : MainBoundedFeaturesChain.{u} := sorry

theorem randLowerBound : Corollaries.RandLowerBound.{u} := sorry

end RegretKappa
