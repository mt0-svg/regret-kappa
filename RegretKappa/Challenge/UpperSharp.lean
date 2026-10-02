import RegretKappa.Challenge.Statement

/-! Challenge module for Comparator (config.json): the definitions of `RegretKappa/UpperSharp/Statement.lean`, copied in order
with their docstrings and the theorems left out, and the targets with `sorry`. Nothing outside the challenge imports it. -/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set

noncomputable def Gam (r : ℝ) : ℝ :=
  2 * ∫ θ in Ioi 1, cosh (θ * r) * (exp (-θ ^ 2 / 2) * (1 / θ + 2 / θ ^ 3))

def beta : ℝ := 3

noncomputable def Cst (T : ℕ) : ℝ := (√(T : ℝ) + 1) / √(2 * π)

noncomputable def lam0 (T : ℕ) : ℝ := exp 2 / Cst T

noncomputable def clip (z : ℝ) : ℝ := max (-1) (min 1 z)

noncomputable def predU (T t : ℕ) (S V x : ℝ) : ℝ :=
  let lam := lam0 T + beta * ((T : ℝ) - t - 1)
  let ρ := if V = 0 then 0 else S / √V
  let s := if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)
  let ε : ℝ := if x < 0 then -1 else 1
  ε * clip (log ((lam + Gam (ρ * √(1 - s) + √s)) / (lam + Gam (ρ * √(1 - s) - √s))) / 2)

noncomputable def learnerU (T : ℕ) : Learner T where
  predict t xs ys := predU T t (∑ i : Fin t, xs (Fin.castSucc i) * ys i)
    (∑ i : Fin t, xs (Fin.castSucc i) ^ 2) (xs (Fin.last t))

def TheoremU : Prop :=
  ∀ (T : ℕ) (x y : Fin T → ℝ), (∀ t, |y t| ≤ 1) →
    regret (learnerU T) x y ≤
      2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))

def TheoremULog : Prop :=
  ∀ (T : ℕ), 1 ≤ T → ∀ (x y : Fin T → ℝ), (∀ t, |y t| ≤ 1) →
    regret (learnerU T) x y ≤
      3 * log T + 2 * log (3 / √(2 * π)) + 2 / √(T : ℝ) + 0.81 / T + 12.35 / (T * √(T : ℝ))

theorem theoremU : TheoremU := sorry

theorem theoremULog : TheoremULog := sorry

end RegretKappa.UpperSharp
