import RegretKappa.Challenge.Statement

/-! Challenge module for Comparator (config.json): the definitions of `RegretKappa/LowerSharp/Statement.lean`, copied in order
with their docstrings and the theorems left out, and the targets with `sorry`. Nothing outside the challenge imports it. -/

namespace RegretKappa.LowerSharp

open Real

def T0 : ℕ := 355713

noncomputable def j0 (T : ℕ) : ℕ := ⌈log (3 * log T)⌉₊

noncomputable def level (T : ℕ) : ℝ := 2 * log (T / (20 * exp 1 * j0 T))

def T1 (T : ℕ) : ℕ := T / 2

def k0 (T : ℕ) : ℕ := T - T1 T

noncomputable def Jc : ℝ := π ^ 2 / 4

noncomputable def c1 : ℝ := 1 / 2 + 4 / 3 - 8 / π ^ 2 + log (π ^ 2) + (Jc - 2) / (π ^ 2 * exp 2)

noncomputable def bT (T : ℕ) : ℝ :=
  (1 - exp (-(j0 T : ℝ))) *
    (level T + log (k0 T / (√(level T) + 2) ^ 2) - c1 - log (k0 T) / (2 * k0 T) - 1 / k0 T)

def LowerSharpAdv : Prop :=
  ∀ T : ℕ, T0 ≤ T →
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i t, 0 ≤ x i t) ∧
      (∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) ∧
      ∀ L : Learner T, bT T ≤ ∑ i, w i * regret L (x i) (y i)

def LowerSharpBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ, T0 ≤ T → ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ B ^ 2 * bT T ≤ regret L x y

def LowerSharpSimplified : Prop :=
  ∀ T : ℕ, T0 ≤ T →
    3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 14.6 ≤ bT T ∧
      3 * log T - 2 * log (log T) - 15.2 ≤
        3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 14.6

theorem lowerSharpAdv : LowerSharpAdv := sorry

theorem lowerSharpBound : LowerSharpBound := sorry

theorem lowerSharpSimplified : LowerSharpSimplified := sorry

end RegretKappa.LowerSharp
