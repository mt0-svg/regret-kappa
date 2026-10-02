import Mathlib

/-! Challenge module for Comparator (config.json): the definitions of `RegretKappa/Statement.lean`, copied in order
with their docstrings and the theorems left out, and the targets with `sorry`. Nothing outside the challenge imports it. -/

namespace RegretKappa

open Filter Topology

structure Learner (T : ℕ) where
    predict : (t : Fin T) → (Fin (t + 1) → ℝ) → (Fin t → ℝ) → ℝ

def Learner.prediction {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) (t : Fin T) : ℝ :=
  L.predict t (fun s => x (Fin.castLE t.isLt s)) (fun s => y (Fin.castLE t.isLt.le s))

def learnerLoss {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) : ℝ :=
  ∑ t, (L.prediction x y t - y t) ^ 2

def linearLoss {T : ℕ} (θ : ℝ) (x y : Fin T → ℝ) : ℝ :=
  ∑ t, (θ * x t - y t) ^ 2

noncomputable def bestLinearLoss {T : ℕ} (x y : Fin T → ℝ) : ℝ :=
  ⨅ θ : ℝ, linearLoss θ x y

noncomputable def regret {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) : ℝ :=
  learnerLoss L x y - bestLinearLoss x y

noncomputable def minimaxRegret (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B), (regret L x y : EReal)

def UpperBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T,
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ (3 + ε) * B ^ 2 * Real.log T

def LowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ (3 - ε) * B ^ 2 * Real.log T ≤ regret L x y

def KappaEqThree : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxRegret T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop (𝓝 3)

end RegretKappa
