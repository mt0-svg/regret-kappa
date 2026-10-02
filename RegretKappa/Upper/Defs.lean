import Mathlib

/-!
# Upper bound: definitions

The potential, the learner's prediction and the constants of the Lean proof of the upper bound
(the paper, Theorem 3.1, with cruder constants).

* `wt θ = e^{-θ²/2} (1/θ + 2/θ³)`, the weight of the mixture on `θ > 1`;
* `G r = ∫_1^∞ cosh(θ r) wt(θ) dθ`, half the potential `Γ` of the paper;
* `Ghat a b = ∫_1^∞ cosh(θ a) e^{θ² b²/2} wt(θ) dθ`, half the mixability majorant `Γ̂(ρ, s)` of
  the paper at `a = ρ √(1 - s)`, `b² = s`;
* `Rf z = cosh z - 1 - z²/2`, the part of `cosh` of order at least four;
* `eta lam a b`, the clipped prediction `clip(½ log((λ + G(a + b))/(λ + G(a - b))))`;
* `pred lam S V x`, the same from the state: `S = ∑ x_i y_i`, `V = ∑ x_i²` over the past rounds,
  `x` the current feature, so that `a = S/√(V + x²)` and `b = x/√(V + x²)`.
-/

namespace RegretKappa.Upper

open Real MeasureTheory Set

/-- The weight of the mixture: `e^{-θ²/2} (1/θ + 2/θ³)`. -/
noncomputable def wt (θ : ℝ) : ℝ := exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3)

/-- The potential: `G r = ∫_1^∞ cosh(θ r) wt(θ) dθ`. -/
noncomputable def G (r : ℝ) : ℝ := ∫ θ in Ioi 1, cosh (θ * r) * wt θ

/-- The mixability majorant: `∫_1^∞ cosh(θ a) e^{θ² b²/2} wt(θ) dθ` (finite for `b² < 1`). -/
noncomputable def Ghat (a b : ℝ) : ℝ := ∫ θ in Ioi 1, cosh (θ * a) * exp (θ ^ 2 * b ^ 2 / 2) * wt θ

/-- The terms of order at least four of `cosh`. -/
noncomputable def Rf (z : ℝ) : ℝ := cosh z - 1 - z ^ 2 / 2

/-- Clipping to `[-1, 1]`. -/
noncomputable def clip (z : ℝ) : ℝ := max (-1) (min 1 z)

/-- The learner's prediction in the variables `a = ρ √(1 - b²)`, `b`. -/
noncomputable def eta (lam a b : ℝ) : ℝ := clip (log ((lam + G (a + b)) / (lam + G (a - b))) / 2)

/-- The learner's prediction from the state `(S, V)` and the current feature `x`. -/
noncomputable def pred (lam S V x : ℝ) : ℝ := eta lam (S / √(V + x ^ 2)) (x / √(V + x ^ 2))

/-- The increment of the potential per round. -/
def beta : ℝ := 60

/-- The constant `C` of the potential: `4 (√T + 1)`. -/
noncomputable def Cst (T : ℕ) : ℝ := 4 * (√(T : ℝ) + 1)

/-- The initial level `λ₀ = 2 / C`. -/
noncomputable def lam0 (T : ℕ) : ℝ := 2 / Cst T

/-- The level used in round `t` (0-indexed) of a game of horizon `T`: `λ₀ + β (T - t - 1)`. -/
noncomputable def lamAt (T t : ℕ) : ℝ := lam0 T + beta * ((T : ℝ) - t - 1)

/-- The potential with `k` rounds left: `Φ_k(ρ) = 2 log(C (λ₀ + β k + G ρ))`. -/
noncomputable def Phi (T : ℕ) (k ρ : ℝ) : ℝ := 2 * log (Cst T * (lam0 T + beta * k + G ρ))

end RegretKappa.Upper
