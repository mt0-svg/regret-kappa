import Mathlib
import RegretKappa.Statement

/-!
# Corollary 4.2 for randomized learners (independent pair lower bound)

Restricted to adversaries that play a fixed pair of sequences `(x, y)` (each such pair is an
adaptive adversary that ignores the predictions), in asymptotic form:
`B^2 b(T)` is replaced by `(3 - ε) B^2 log T`, and "for every `T ≥ T_0`" becomes
"for every `ε > 0`, for every large `T`".

We formalize the statement that the minimax expected regret of randomized learners is at least
`(3 - ε) B^2 log T` for every `B > 0` and `ε > 0` and sufficiently large `T`.
-/

namespace Indep42a

open Real
open MeasureTheory
open Set
open Filter

/-! ## Auxiliary definitions -/

/-- Discrete σ-algebra on `Learner T` so that every function from `Learner T` is measurable.
This is needed for the Lebesgue integral (`∫⁻`). -/
instance (T : ℕ) : MeasurableSpace (RegretKappa.Learner T) := ⊥

/-! ## Randomized learner -/

/-- A randomized learner for horizon `T`. It is a probability measure on the space of deterministic
learners (`RegretKappa.Learner T`). Conditionally on the randomness, the learner is deterministic:
each `ω` in the support of the measure picks out a deterministic learner. -/
structure RandLearner (T : ℕ) where
  /-- The probability measure on deterministic learners. -/
  μ : Measure (RegretKappa.Learner T)
  [hprob : IsProbabilityMeasure μ]

/-! ## Expected regret -/

/-- The expected regret of a randomized learner `L` on a play `(x, y)`.
Defined as `E[(L ω).regret x y]` where the expectation is over the learner's randomness `ω`.

Uses the decomposition into positive and negative parts with the Lebesgue integral
`∫⁻` (which returns `⊤` for non-integrable nonnegative functions), so that the expectation
is meaningful even when the positive part has infinite integral.  The subtraction is in
`EReal`, where `⊤ - finite = ⊤` and `finite - ⊤` would be `⊥`, but the negative part is
always bounded by the best linear loss (a finite real number), so the second integral is
finite and the subtraction is safe. -/
noncomputable def RandLearner.expectedRegret {T : ℕ} (L : RandLearner T) (x y : Fin T → ℝ) : EReal :=
  let f := fun (ω : RegretKappa.Learner T) => RegretKappa.regret ω x y
  (∫⁻ ω, ENNReal.ofReal (max (f ω) 0) ∂(L.μ) : EReal) -
  (∫⁻ ω, ENNReal.ofReal (max (-f ω) 0) ∂(L.μ) : EReal)

/-- The negative part of the regret is bounded above by the best linear loss, which is a finite
real number. Hence its Lebesgue integral is finite and the subtraction in `expectedRegret`
avoids the `∞ - ∞ = ⊥` degeneracy in `EReal`. -/
lemma negPart_le_bestLinearLoss {T : ℕ} (x y : Fin T → ℝ) (L' : RegretKappa.Learner T) :
    max (-RegretKappa.regret L' x y) 0 ≤ RegretKappa.bestLinearLoss x y := by
  -- regret = learnerLoss - bestLinearLoss
  -- -regret = bestLinearLoss - learnerLoss
  -- max(bestLinearLoss - learnerLoss, 0) ≤ bestLinearLoss because learnerLoss ≥ 0
  unfold RegretKappa.regret
  have h_nonneg_learnerLoss : 0 ≤ RegretKappa.learnerLoss L' x y := by
    unfold RegretKappa.learnerLoss
    positivity
  have h_best_nonneg : 0 ≤ RegretKappa.bestLinearLoss x y :=
    RegretKappa.le_bestLinearLoss x y fun θ => by
      unfold RegretKappa.linearLoss
      positivity
  have h_sub : -(RegretKappa.learnerLoss L' x y - RegretKappa.bestLinearLoss x y) ≤
      RegretKappa.bestLinearLoss x y := by
    linarith
  exact max_le h_sub h_best_nonneg

/-- The integral of the negative part is finite (bounded by the best linear loss). -/
lemma lintegral_negPart_finite {T : ℕ} (L : RandLearner T) (x y : Fin T → ℝ) :
    (∫⁻ ω, ENNReal.ofReal (max (-RegretKappa.regret ω x y) 0) ∂(L.μ) : EReal) < ⊤ := by
  have h_bound : ∀ ω, ENNReal.ofReal (max (-RegretKappa.regret ω x y) 0) ≤
      ENNReal.ofReal (RegretKappa.bestLinearLoss x y) := by
    intro ω
    refine ENNReal.ofReal_le_ofReal (negPart_le_bestLinearLoss x y ω)
  have h_int_ennreal : (∫⁻ ω, ENNReal.ofReal (max (-RegretKappa.regret ω x y) 0) ∂(L.μ)) ≤
      ENNReal.ofReal (RegretKappa.bestLinearLoss x y) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (max (-RegretKappa.regret ω x y) 0) ∂(L.μ)) ≤
          (∫⁻ ω, ENNReal.ofReal (RegretKappa.bestLinearLoss x y) ∂(L.μ)) :=
        lintegral_mono h_bound
      _ = ENNReal.ofReal (RegretKappa.bestLinearLoss x y) * L.μ Set.univ := by
        rw [lintegral_const]
      _ = ENNReal.ofReal (RegretKappa.bestLinearLoss x y) * 1 := by
        rw [L.hprob.measure_univ]
      _ = ENNReal.ofReal (RegretKappa.bestLinearLoss x y) := by simp
  have h_finite_ennreal : ENNReal.ofReal (RegretKappa.bestLinearLoss x y) < ⊤ :=
    ENNReal.ofReal_lt_top
  have h_lt_ennreal : (∫⁻ ω, ENNReal.ofReal (max (-RegretKappa.regret ω x y) 0) ∂(L.μ)) < ⊤ :=
    lt_of_le_of_lt h_int_ennreal h_finite_ennreal
  -- Now lift to EReal: the coercion ENNReal → EReal preserves < and ⊤
  revert h_lt_ennreal
  generalize h_int : (∫⁻ ω, ENNReal.ofReal (max (-RegretKappa.regret ω x y) 0) ∂(L.μ)) = a
  intro h_lt
  cases' a with x
  · exact (lt_irrefl _ h_lt).elim
  · simpa [ENNReal.toEReal] using EReal.coe_lt_top x

/-! ## Lower bound statement -/

/-- **Corollary 4.2 for randomized learners (independent pair lower bound).**

For every `B > 0` and `ε > 0`, for every sufficiently large horizon `T`, every randomized learner
has a play `(x, y)` with `|y t| ≤ B` for every `t` on which its expected regret is at least
`(3 - ε) B ^ 2 log T`.

This is the asymptotic form of the lower bound for the minimax expected regret of randomized
learners, restricted to fixed pairs of sequences (adaptive adversaries that ignore predictions). -/
def RandLowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ L : RandLearner T, ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧
      (3 - ε) * B ^ 2 * Real.log T ≤ L.expectedRegret x y

end Indep42a
