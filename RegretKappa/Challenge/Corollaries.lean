import RegretKappa.Challenge.Statement

/-! Challenge module for Comparator (config.json): the definitions of `RegretKappa/Corollaries/Statement.lean`, copied in order
with their docstrings and the theorems left out, and the targets with `sorry`. Nothing outside the challenge imports it. -/

namespace RegretKappa.Corollaries

open MeasureTheory Filter

universe u

def IsRandLearner {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (t : Fin T) (xs : Fin (t + 1) → ℝ) (ys : Fin t → ℝ),
      Measurable fun ω => (L ω).predict t xs ys

noncomputable def expRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) (x y : Fin T → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (regret (L ω) x y + ∑ t, y t ^ 2) ∂μ : ENNReal) : EReal) -
    ((∑ t, y t ^ 2 : ℝ) : EReal)

noncomputable def advRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) {ι : Type*} [Fintype ι] (w : ι → ℝ) (x y : ι → Fin T → ℝ) : EReal :=
  ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) *
      ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) -
    ((∑ i, w i * ∑ t, y i t ^ 2 : ℝ) : EReal)

def RandLowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T), IsRandLearner μ L →
      ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧
        (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤ expRegret μ L x y

def BoundedFeatures : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
      (3 - ε) * B ^ 2 * Real.log T ≤ regret L x y

def BoundedFeaturesRand : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T), IsRandLearner μ L →
      ∃ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤ expRegret μ L x y

def BoundedFeaturesAdv : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
        IsRandLearner μ L → (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤ advRegret μ L w x y

noncomputable def minimaxRegretBF (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1)
    (_ : ∀ t, y t ∈ ({-B, 0, B} : Set ℝ)), (regret L x y : EReal)

def BoundedFeaturesUpper : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T,
    ∀ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) →
      regret L x y ≤ (3 + ε) * B ^ 2 * Real.log T

def KappaEqThreeBF : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxRegretBF T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop (nhds 3)

open Real in
def BoundedFeaturesUpperU : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ,
    minimaxRegretBF T B ≤
      ((B ^ 2 * (2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))) : ℝ) :
        EReal)

noncomputable def minimaxRegretBFI (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1)
    (_ : ∀ t, |y t| ≤ B), (regret L x y : EReal)

def KappaEqThreeBFI : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxRegretBFI T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop
      (nhds 3)

open Real in
def BoundedFeaturesUpperUI : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ,
    minimaxRegretBFI T B ≤
      ((B ^ 2 * (2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))) : ℝ) :
        EReal)

theorem randLowerBound : RandLowerBound.{u} := sorry

end RegretKappa.Corollaries
