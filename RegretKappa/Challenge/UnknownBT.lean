import RegretKappa.Challenge.Statement
import RegretKappa.Challenge.UpperSharp

/-! Challenge module for Comparator (config.json): the definitions of `RegretKappa/UnknownBT/Statement.lean`, copied in order
with their docstrings and the theorems left out, and the targets with `sorry`. Nothing outside the challenge imports it. -/

namespace RegretKappa.UnknownBT

open RegretKappa Filter Topology Real

structure AnytimeLearner where
    predict : (t : ℕ) → (Fin (t + 1) → ℝ) → (Fin t → ℝ) → ℝ

def AnytimeLearner.restrict (L : AnytimeLearner) (T : ℕ) : Learner T where
  predict t xs ys := L.predict t xs ys

set_option linter.dupNamespace false in
def UnknownBT : Prop :=
  ∃ L : AnytimeLearner, ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ B : ℝ, 0 < B →
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret (L.restrict T) x y ≤ (3 + ε) * B ^ 2 * log T

def UnknownBTEveryT : Prop :=
  ∃ L : AnytimeLearner, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ T : ℕ, 2 ≤ T → ∀ B : ℝ, 0 < B →
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret (L.restrict T) x y ≤ (3 + ε T) * B ^ 2 * log T

def UnknownT : Prop :=
  ∀ B : ℝ, 0 < B → ∃ L : AnytimeLearner, ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret (L.restrict T) x y ≤ (3 + ε) * B ^ 2 * log T

def UnknownB : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T, ∀ B : ℝ, 0 < B →
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ (3 + ε) * B ^ 2 * log T

def Optimality : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : AnytimeLearner,
    ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ (3 - ε) * B ^ 2 * log T ≤ regret (L.restrict T) x y

noncomputable def worstRatio (L : AnytimeLearner) (T : ℕ) : EReal :=
  ⨆ (B : ℝ) (_ : 0 < B) (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B),
    (regret (L.restrict T) x y : EReal) / ((B ^ 2 * log T : ℝ) : EReal)

noncomputable def bestConstant : EReal :=
  ⨅ L : AnytimeLearner, limsup (worstRatio L) atTop

def BestConstantThree : Prop :=
  (∃ L : AnytimeLearner, Tendsto (worstRatio L) atTop (𝓝 3)) ∧
    ∀ L : AnytimeLearner, (3 : EReal) ≤ liminf (worstRatio L) atTop

noncomputable def predLam (lam S V x : ℝ) : ℝ :=
  let ρ := if V = 0 then 0 else S / √V
  let s := if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)
  let ε : ℝ := if x < 0 then -1 else 1
  ε * UpperSharp.clip (log ((lam + UpperSharp.Gam (ρ * √(1 - s) + √s)) /
    (lam + UpperSharp.Gam (ρ * √(1 - s) - √s))) / 2)

noncomputable def lamB (t : ℕ) : ℝ := 3 * log (t + 2) / log ((t + 3) / (t + 2))

noncomputable def learnerB : AnytimeLearner where
  predict t xs ys := predLam (lamB t) (∑ i : Fin t, xs (Fin.castSucc i) * ys i)
    (∑ i : Fin t, xs (Fin.castSucc i) ^ 2) (xs (Fin.last t))

noncomputable def runMax {n : ℕ} (y : Fin n → ℝ) : ℝ := Finset.univ.fold max 0 fun i => |y i|

noncomputable def learnerBT : AnytimeLearner where
  predict t xs ys :=
    if runMax ys = 0 then 0 else runMax ys * learnerB.predict t xs fun i => ys i / runMax ys

noncomputable def constK : ℝ :=
  2 * log (3 / log 2 + 2 * exp (-1 / 2) * (1 / log 2 - 1 / log 3)) - log (2 * π)

def TheoremB : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ 1) →
    regret (learnerB.restrict T) x y ≤
      3 * log T + 4 * log (log (T + 2)) + constK + 2 * log (1 + 1 / √(T : ℝ)) + 2 * log (1 + 2 / T)

def TheoremBNum : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ 1) →
    regret (learnerB.restrict T) x y ≤
      3 * log T + 4 * log (log (T + 2)) + 1.3706 + 2 / √(T : ℝ) + 4 / T

def ScaleFreeBound (c : ℝ) : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ x y : Fin T → ℝ,
    regret (learnerBT.restrict T) x y ≤
      runMax y ^ 2 * (3 * log T + 4 * log (log (T + 2)) + c + 2 / √(T : ℝ) + 4 / T)

theorem theoremB : TheoremB := sorry

theorem optimality : Optimality := sorry

theorem UB.scaleFreeBound_twelve : ScaleFreeBound 12 := sorry

theorem UB.answer : UnknownBTEveryT ∧ UnknownBT ∧ UnknownT ∧ UnknownB ∧ BestConstantThree ∧ bestConstant = 3 := sorry

end RegretKappa.UnknownBT
