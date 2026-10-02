import RegretKappa.Statement

/-!
# Corollary 5.1 of PROBLEM.txt: the constant κ = 3

We formalize Corollary 5.1 in asymptotic form: for every `B > 0` and `ε > 0`, for
every large `T`, there is a randomized adversary with features in `[0, 1]` and outcomes
in `{-B, 0, B}` against which every learner, deterministic or randomized, has expected
regret at least `(3 - ε) B ^ 2 log T`.

We model a randomized learner as a probability space `(Ω, μ)` and a map
`L : Ω → Learner T`. The learner's randomness is independent of the adversary's
choices. The expected regret of a randomized learner `L` on a fixed play `(x, y)`
is the integral of `regret (L ω) x y` with respect to `μ`.

To avoid junk values from the Bochner integral (which returns `0` for non-integrable
functions), we define expectations using the `lintegral` of the positive and negative
parts in `EReal`. For bounded functions this coincides with the Bochner integral;
for unbounded functions it gives `∞` (resp. `-∞`) for the positive (resp. negative)
part, which is the correct extended-real expectation.

The adversary is a probability measure on plays `(x, y)` that ignores the learner's
predictions (a random play, independent of the learner's randomness).
By the footnote to Corollary 5.1, the restricted statement implies the stated one.
-/

namespace Indep51c

open Filter Topology MeasureTheory
open Set

/-- The expected regret of a deterministic learner `L` against a fixed adversary `ν`
(a probability measure on plays). We integrate the regret over `ν` using the `lintegral`
of positive and negative parts in `EReal` to avoid junk values. -/
noncomputable def expectedRegretSingle {T : ℕ} (L : RegretKappa.Learner T)
    (ν : Measure ((Fin T → ℝ) × (Fin T → ℝ))) : EReal :=
  let pos := ∫⁻ p, ENNReal.ofReal ((RegretKappa.regret L p.1 p.2)⁺) ∂ν
  let neg := ∫⁻ p, ENNReal.ofReal ((RegretKappa.regret L p.1 p.2)⁻) ∂ν
  (pos.toEReal) - (neg.toEReal)

/-- The expected regret of a randomized learner `L` against a fixed adversary `ν`.
This is the double integral: first over the adversary's play `ν`, then over the
learner's randomness `μ`. We use the `lintegral` of positive and negative parts in
`EReal` to avoid junk values. -/
noncomputable def expectedRegretAgainstAdversary {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : Ω → RegretKappa.Learner T)
    (ν : Measure ((Fin T → ℝ) × (Fin T → ℝ))) : EReal :=
  let pos := ∫⁻ ω, ((expectedRegretSingle (L ω) ν)⁺).toENNReal ∂μ
  let neg := ∫⁻ ω, ((expectedRegretSingle (L ω) ν)⁻).toENNReal ∂μ
  (pos.toEReal) - (neg.toEReal)

/-- The expected regret of a randomized learner `L` on a fixed play `(x, y)`.
We use the `lintegral` of the positive and negative parts in `EReal` to avoid the
junk value `0` that the Bochner integral assigns to non-integrable functions. -/
noncomputable def expectedRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (L : Ω → RegretKappa.Learner T) (x y : Fin T → ℝ) : EReal :=
  let pos := ∫⁻ ω, ENNReal.ofReal ((RegretKappa.regret (L ω) x y)⁺) ∂μ
  let neg := ∫⁻ ω, ENNReal.ofReal ((RegretKappa.regret (L ω) x y)⁻) ∂μ
  (pos.toEReal) - (neg.toEReal)

/-- The set of valid plays for horizon `T` with outcome bound `B`:
features in `[0, 1]` and outcomes in `{-B, 0, B}`. -/
def validPlays (T : ℕ) (B : ℝ) : Set ((Fin T → ℝ) × (Fin T → ℝ)) :=
  {p | (∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, p.2 t ∈ ({-B, 0, B} : Set ℝ))}

/-- **Corollary 5.1, first sentence.** For every `B > 0` and `ε > 0`, for every large `T`,
there is a randomized adversary with features in `[0, 1]` and outcomes in `{-B, 0, B}`
against which every learner, deterministic or randomized, has expected regret at least
`(3 - ε) B ^ 2 log T`.

The adversary is a probability measure on plays that ignores the learner's predictions
(a random play, independent of the learner's randomness). -/
def Adversary : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∃ (ν : Measure ((Fin T → ℝ) × (Fin T → ℝ))) (_ : IsProbabilityMeasure ν)
      (_ : ν (validPlays T B) = 1),
      (∀ (L : RegretKappa.Learner T),
        expectedRegretSingle L ν ≥ (3 - ε) * B ^ 2 * Real.log T) ∧
      (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (L : Ω → RegretKappa.Learner T),
        expectedRegretAgainstAdversary μ L ν ≥ (3 - ε) * B ^ 2 * Real.log T)

/-- **Corollary 5.1, consequence for deterministic learners.** For every `B > 0` and
`ε > 0`, for every large `T`, every deterministic learner has a play with features in
`[0, 1]` and outcomes in `{-B, 0, B}` on which its regret is at least
`(3 - ε) B ^ 2 log T`. -/
def DetPlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (L : RegretKappa.Learner T),
      ∃ (x y : Fin T → ℝ),
        (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (3 - ε) * B ^ 2 * Real.log T ≤ RegretKappa.regret L x y

/-- **Corollary 5.1, consequence for randomized learners.** For every `B > 0` and
`ε > 0`, for every large `T`, every randomized learner has a play with features in
`[0, 1]` and outcomes in `{-B, 0, B}` on which its expected regret is at least
`(3 - ε) B ^ 2 log T`. -/
def RandPlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (L : Ω → RegretKappa.Learner T),
      ∃ (x y : Fin T → ℝ),
        (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (3 - ε) * B ^ 2 * Real.log T ≤ expectedRegret μ L x y

end Indep51c
