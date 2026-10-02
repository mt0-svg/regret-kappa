import RegretKappa.Statement

/-!
# The statement of the upper bound with its constants

The upper bound of the paper, for outcomes in `[-1, 1]` (`B = 1`), on the model of
`RegretKappa/Statement.lean` (`Learner`, `regret`). The learner is the one of the paper, written
from its formula, with `β = 3`, `C = (√T + 1)/√(2π)`, `λ₀ = e²/C` and the potential

`Γ(r) = ∫_{|θ| ≥ 1} e^{θ r - θ²/2} (1/|θ| + 2/|θ|³) dθ = 2 ∫_1^∞ cosh(θ r) e^{-θ²/2} (1/θ + 2/θ³) dθ`,

in its second form (`Gam`). The integrand is integrable for every `r` (Gaussian decay), so the
Bochner integral is the integral of the paper.

Rounds are indexed by `Fin T` as in `RegretKappa/Statement.lean`: round `t` here is round `t + 1`
of the paper. In round `t` the learner sees `S = ∑_{i<t} x_i y_i`, `V = ∑_{i<t} x_i²` and the
current feature `x = x_t`, and predicts (`predU`)

`ε clip_{[-1,1]}(½ log((λ + Γ(ρ √(1-s) + √s)) / (λ + Γ(ρ √(1-s) - √s))))`, `λ = λ₀ + β (T - t - 1)`,

with `ρ = S/√V` (`0` if `V = 0`), `s = x²/(V + x²)` (`0` if `V + x² = 0`), `ε = sign x` (`1` if
`x = 0`): the conventions of the paper for the state, written out (they do not rely on Lean's
`a / 0 = 0`). For `t < T` the level `λ` is at least `λ₀ > 0`, so both arguments of the ratio are
positive.

Targets (propositions, proved in other modules of the library):
* `TheoremU`: on every play with outcomes in `[-1, 1]`,
  `Regret_T ≤ 2 log(e² + (√T + 1)(3T + 2e^{-1/2})/√(2π))`, for every `T` (for `T = 0` the regret
  is `0` and the bound is positive);
* `TheoremULog`: for `T ≥ 1`, the second form
  `Regret_T ≤ 3 log T + 2 log(3/√(2π)) + 2/√T + 0.81/T + 12.35/T^{3/2}`.
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set

/-- The potential `Γ` of the paper: `Γ(r) = 2 ∫_1^∞ cosh(θ r) e^{-θ²/2} (1/θ + 2/θ³) dθ`. -/
noncomputable def Gam (r : ℝ) : ℝ :=
  2 * ∫ θ in Ioi 1, cosh (θ * r) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))

/-- The increment `β = 3`. -/
def beta : ℝ := 3

/-- The constant `C = (√T + 1)/√(2π)`. -/
noncomputable def Cst (T : ℕ) : ℝ := (√(T : ℝ) + 1) / √(2 * π)

/-- The initial level `λ₀ = e²/C`. -/
noncomputable def lam0 (T : ℕ) : ℝ := exp 2 / Cst T

/-- Clipping to `[-1, 1]`. -/
noncomputable def clip (z : ℝ) : ℝ := max (-1) (min 1 z)

/-- The prediction of the potential learner in round `t` (0-indexed) of a game of horizon `T`,
from `S = ∑_{i<t} x_i y_i`, `V = ∑_{i<t} x_i²` and the current feature `x`. -/
noncomputable def predU (T t : ℕ) (S V x : ℝ) : ℝ :=
  let lam := lam0 T + beta * ((T : ℝ) - t - 1)
  let ρ := if V = 0 then 0 else S / √V
  let s := if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)
  let ε : ℝ := if x < 0 then -1 else 1
  ε * clip (log ((lam + Gam (ρ * √(1 - s) + √s)) / (lam + Gam (ρ * √(1 - s) - √s))) / 2)

/-- The potential learner, for outcomes in `[-1, 1]`. -/
noncomputable def learnerU (T : ℕ) : Learner T where
  predict t xs ys := predU T t (∑ i : Fin t, xs (Fin.castSucc i) * ys i)
    (∑ i : Fin t, xs (Fin.castSucc i) ^ 2) (xs (Fin.last t))

/-- **The upper bound**, first form: on every play with outcomes in `[-1, 1]`,
`Regret_T ≤ 2 log(e² + (√T + 1)(3T + 2e^{-1/2})/√(2π))`, for every horizon `T`. -/
def TheoremU : Prop :=
  ∀ (T : ℕ) (x y : Fin T → ℝ), (∀ t, |y t| ≤ 1) →
    regret (learnerU T) x y ≤
      2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))

/-- **The upper bound**, second form, for `T ≥ 1`:
`Regret_T ≤ 3 log T + 2 log(3/√(2π)) + 2/√T + 0.81/T + 12.35/T^{3/2}`. -/
def TheoremULog : Prop :=
  ∀ (T : ℕ), 1 ≤ T → ∀ (x y : Fin T → ℝ), (∀ t, |y t| ≤ 1) →
    regret (learnerU T) x y ≤
      3 * log T + 2 * log (3 / √(2 * π)) + 2 / √(T : ℝ) + 0.81 / T + 12.35 / (T * √(T : ℝ))

end RegretKappa.UpperSharp
