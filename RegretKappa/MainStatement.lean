import RegretKappa.LowerSharp.Statement
import RegretKappa.Corollaries.Statement

/-!
# The statement of the main theorem

The paper's main theorem (Theorem 1.1) in one proposition, on the model of
`RegretKappa/Statement.lean` (`Learner`, `regret`, `minimaxRegret`, `KappaEqThree`): features
in `ℝ` with no bound known in advance, no bound on the comparator, outcomes in `[-B, B]`. For
every `B > 0` and every `T ≥ 355713`,

`B² (3 log T - 2 log log T - 15.2) ≤ B² b(T) ≤ minimaxRegret T B ≤ B² U(T)`,

with `b(T)` of `RegretKappa/LowerSharp/Statement.lean` (the paper, Theorem 4.1) and
`U(T) = 2 log(e² + (√T + 1)(3T + 2e^{-1/2})/√(2π))` (the paper, Theorem 3.1, as in
`RegretKappa.UpperSharp.TheoremU`), and `minimaxRegret T B / (B² log T) → 3`.

The companion for the paper's Corollary 5.1, with the same constants: an adversary with features
in `[0, 1]` and outcomes in `{-B, 0, B}` that forces expected regret `B² b(T)` on every
randomized learner (`RegretKappa.Corollaries.advRegret`), and the same chain for the minimax
regrets over features in `[0, 1]` with outcomes in `{-B, 0, B}` (`minimaxRegretBF`) and in
`[-B, B]` (`minimaxRegretBFI`).
-/

namespace RegretKappa

open Real MeasureTheory

universe u

/-- The explicit upper bound `U(T) = 2 log(e² + (√T + 1)(3T + 2e^{-1/2})/√(2π))`. -/
noncomputable def boundU (T : ℕ) : ℝ :=
  2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))

/-- The simplified lower bound `3 log T - 2 log log T - 15.2`. -/
noncomputable def boundL (T : ℕ) : ℝ := 3 * log T - 2 * log (log T) - 15.2

/-- **The main theorem.** For every `B > 0` and `T ≥ 355713`,
`B² (3 log T - 2 log log T - 15.2) ≤ B² b(T) ≤ minimaxRegret T B ≤ B² U(T)`, in `EReal`; and
`minimaxRegret T B / (B² log T)` tends to `3`. -/
def MainTheorem : Prop :=
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, LowerSharp.T0 ≤ T →
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ∧
      ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ≤ minimaxRegret T B ∧
      minimaxRegret T B ≤ ((B ^ 2 * boundU T : ℝ) : EReal)) ∧
  KappaEqThree

/-- **The paper, Corollary 5.1, with the constants of the main theorem.** For every `B > 0` and
`T ≥ 355713`: there is an adversary that ignores the predictions and plays `(x i, y i)` with
probability `w i`, `i` in a finite type, every play with features in `[0, 1]` and outcomes in
`{-B, 0, B}`, against which every randomized learner has expected regret at least `B² b(T)`; and
`B² (3 log T - 2 log log T - 15.2) ≤ B² b(T) ≤ minimaxRegretBF T B ≤ minimaxRegretBFI T B ≤
B² U(T)`, in `EReal`. -/
def MainBoundedFeatures : Prop :=
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

end RegretKappa
