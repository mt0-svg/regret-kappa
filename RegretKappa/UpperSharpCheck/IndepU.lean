import RegretKappa.Statement

open Real

namespace IndepU

/-- The potential function Gamma(r) = 2 ∫_{1}^{∞} cosh(θ r) e^{-θ²/2} (1/θ + 2/θ³) dθ.
    The integrand is integrable on (1, ∞) for every r. -/
noncomputable def Gamma (r : ℝ) : ℝ :=
  2 * ∫ θ in Set.Ioi (1 : ℝ), Real.cosh (θ * r) * Real.exp (-(θ ^ 2) / 2) * (1/θ + 2/(θ ^ 3))

/-- The clipping function clip_{[-1,1]}(z) = max(-1, min(1, z)). -/
noncomputable def clip (z : ℝ) : ℝ := max (-1) (min 1 z)

/-- The learner of Theorem U. In round t (0-indexed, corresponding to round t+1 in the text),
    it computes the prediction
    yhat_t = eps_t * clip( (1/2) log( (λ + Γ(ρ√(1-s) + √s)) / (λ + Γ(ρ√(1-s) - √s)) ) )
    with the parameters defined in the text (beta = 3, C = (√T + 1)/√(2π),
    λ₀ = e²/C, λ = λ₀ + 3(T - t - 1), ρ = S_{t-1}/√V_{t-1}, s = x_t²/V_t,
    ε_t = sign(x_t) with ε_t = 1 when x_t = 0). -/
noncomputable def learner (T : ℕ) : RegretKappa.Learner T where
  predict := λ t x y =>
    let S_prev := ∑ j : Fin t, x (Fin.castSucc j) * y j
    let V_prev := ∑ j : Fin t, (x (Fin.castSucc j)) ^ 2
    let xt := x (Fin.last t)
    let Vt := V_prev + xt ^ 2
    let rho := S_prev / Real.sqrt V_prev
    let s := xt ^ 2 / Vt
    let eps := if xt = 0 then 1 else Real.sign xt
    let beta : ℝ := 3
    let C := (Real.sqrt (T : ℝ) + 1) / Real.sqrt (2 * π)
    let lambda0 := Real.exp 2 / C
    let lambda := lambda0 + beta * ((T : ℝ) - (t : ℝ) - 1)
    let sqrt_term := Real.sqrt (1 - s)
    let num := lambda + Gamma (rho * sqrt_term + Real.sqrt s)
    let den := lambda + Gamma (rho * sqrt_term - Real.sqrt s)
    eps * clip ((1/2) * Real.log (num / den))

/-- Theorem U: for every horizon T and every play with outcomes in [-1, 1], the regret of
    `learner T` is at most
    2 log( e² + (√T + 1)(3T + 2e^{-1/2}) / √(2π) ). -/
def TheoremU : Prop :=
  ∀ (T : ℕ) (x y : Fin T → ℝ), (∀ t, |y t| ≤ 1) →
    RegretKappa.regret (learner T) x y ≤
      2 * Real.log (Real.exp 2 + ((Real.sqrt (T : ℝ) + 1) * (3 * (T : ℝ) + 2 * Real.exp (-1/2))) / Real.sqrt (2 * π))

/-- Theorem U (log version): for every T ≥ 1 and every play with outcomes in [-1, 1], the regret
    of `learner T` is at most
    3 log T + 2 log(3/√(2π)) + 2/√T + 0.81/T + 12.35/T^{3/2}. -/
def TheoremULog : Prop :=
  ∀ (T : ℕ), 1 ≤ T → ∀ (x y : Fin T → ℝ), (∀ t, |y t| ≤ 1) →
    RegretKappa.regret (learner T) x y ≤
      3 * Real.log (T : ℝ) + 2 * Real.log (3 / Real.sqrt (2 * π)) + 2 / Real.sqrt (T : ℝ) +
      0.81 / (T : ℝ) + 12.35 / ((T : ℝ) ^ (3/2 : ℝ))

end IndepU
