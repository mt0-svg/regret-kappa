import RegretKappa.Statement

/-!
# Corollary 5.1 of PROBLEM.txt (asymptotic form)

We formalize Corollary 5.1 in asymptotic form: `B^2 b(T)` is replaced by
`(3 - ε) B^2 log T`, and `T ≥ T_0` is replaced by `∀ᶠ T : ℕ in atTop`.

The corollary has three parts:
1. There exists a randomized adversary (with features in [0,1] and outcomes in
   {-B, 0, B}) against which every learner has large expected regret.
2. The deterministic consequence: every deterministic learner has a play with
   features in [0,1] and outcomes in {-B, 0, B} achieving large regret.
3. The randomized consequence: every randomized learner has a play with
   features in [0,1] and outcomes in {-B, 0, B} achieving large expected regret.

We model a randomized learner as a probability measure on deterministic learners
(see `RandLearner`). Its expected regret against a fixed play is the integral of
`regret` over this measure.  The adversary is modeled as a probability measure on
plays `(x, y)` with the range constraints (see `Adversary`); the adversary's
randomness is independent of the learner's, so the expected regret against a
randomized adversary is the integral over the adversary's measure of the
(already integrated) learner expected regret.

We use `ENNReal` (`ℝ≥0∞`) for expectations so that they are always defined
(the Bochner integral of a non-integrable function is `0` in Mathlib, but the
`lintegral` is always defined).
-/

namespace Indep51a

open Set
open Filter
open MeasureTheory
open ENNReal

/-! ### Measurable space on learners -/

instance {T : ℕ} : MeasurableSpace (RegretKappa.Learner T) :=
  MeasurableSpace.comap RegretKappa.Learner.predict inferInstance

/-! ### Randomized learner and expected regret -/

/-- A randomized learner for horizon `T`: a probability measure on deterministic
learners.  Conditioned on the randomness, the learner is deterministic. -/
structure RandLearner (T : ℕ) where
  law : Measure (RegretKappa.Learner T)
  isProbabilityMeasure : IsProbabilityMeasure law

/-- Expected regret of a deterministic learner against a randomized adversary.
The expectation is over the adversary's randomness. -/
noncomputable def expRegretDet {T : ℕ} (L : RegretKappa.Learner T)
    (adv : Measure ((Fin T → ℝ) × (Fin T → ℝ))) : ℝ≥0∞ :=
  MeasureTheory.lintegral adv (fun p => ENNReal.ofReal (RegretKappa.regret L p.1 p.2))

/-- Expected regret of a randomized learner against a randomized adversary.
The expectation is over both the learner's and adversary's randomness.
Since they are independent, this is
`∫_L (∫_x,y regret(L, x, y) d(adv)) d(law)`. -/
noncomputable def expRegretRand {T : ℕ} (R : RandLearner T)
    (adv : Measure ((Fin T → ℝ) × (Fin T → ℝ))) : ℝ≥0∞ :=
  MeasureTheory.lintegral R.law (fun L => expRegretDet L adv)

/-! ### Randomized adversary -/

/-- A randomized adversary for horizon `T` with features in `[0,1]` and outcomes
in `{-B, 0, B}`.  The adversary's randomness is independent of the learner's.

"Such an adversary is one adaptive adversary, so the restricted statement
implies the stated one." -/
structure Adversary (T : ℕ) (B : ℝ) where
  law : Measure ((Fin T → ℝ) × (Fin T → ℝ))
  isProbabilityMeasure : IsProbabilityMeasure law
  features_range : ∀ᵐ p ∂law, ∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1
  outcomes_range : ∀ᵐ p ∂law, ∀ t, p.2 t ∈ ({-B, 0, B} : Set ℝ)

/-! ### The three corollaries -/

/-- **Corollary 5.1, first sentence (asymptotic form).**
For every `B > 0` and `ε > 0`, for every large `T`, there exists a randomized
adversary with features in `[0, 1]` and outcomes in `{-B, 0, B}` against which
every learner, deterministic or randomized, has expected regret at least
`(3 - ε) B^2 log T`. -/
def AdversaryProp : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∃ (adv : Adversary T B),
      (∀ (L : RegretKappa.Learner T),
        ENNReal.ofReal ((3 - ε) * B ^ 2 * Real.log T) ≤ expRegretDet L adv.law) ∧
      (∀ (R : RandLearner T),
        ENNReal.ofReal ((3 - ε) * B ^ 2 * Real.log T) ≤ expRegretRand R adv.law)

/-- **Corollary 5.1, second sentence (asymptotic form), consequence for
deterministic learners.**
For every `B > 0` and `ε > 0`, for every large `T`, every deterministic learner
has a play with features in `[0, 1]` and outcomes in `{-B, 0, B}` on which its
regret is at least `(3 - ε) B^2 log T`. -/
def DetPlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (L : RegretKappa.Learner T),
      ∃ (x y : Fin T → ℝ),
        (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (3 - ε) * B ^ 2 * Real.log T ≤ RegretKappa.regret L x y

/-- **Corollary 5.1, third sentence (asymptotic form), consequence for
randomized learners.**
For every `B > 0` and `ε > 0`, for every large `T`, every randomized learner
has a play with features in `[0, 1]` and outcomes in `{-B, 0, B}` on which its
expected regret is at least `(3 - ε) B^2 log T`. -/
def RandPlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (R : RandLearner T),
      ∃ (x y : Fin T → ℝ),
        (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        ENNReal.ofReal ((3 - ε) * B ^ 2 * Real.log T) ≤
          MeasureTheory.lintegral R.law (fun L => ENNReal.ofReal (RegretKappa.regret L x y))

/-! ### Lemmas showing definitions are meaningful -/

/-- The expected regret of a deterministic learner against any adversary is nonnegative. -/
theorem expRegretDet_nonneg {T : ℕ} (L : RegretKappa.Learner T)
    (adv : Measure ((Fin T → ℝ) × (Fin T → ℝ))) : 0 ≤ expRegretDet L adv := by
  unfold expRegretDet
  calc
    0 = MeasureTheory.lintegral adv (fun _ => (0 : ℝ≥0∞)) := by
      rw [MeasureTheory.lintegral_zero]
    _ ≤ MeasureTheory.lintegral adv (fun p => ENNReal.ofReal (RegretKappa.regret L p.1 p.2)) :=
      MeasureTheory.lintegral_mono (fun p => by simp [ENNReal.ofReal])

/-- The expected regret of a randomized learner against any adversary is nonnegative. -/
theorem expRegretRand_nonneg {T : ℕ} (R : RandLearner T)
    (adv : Measure ((Fin T → ℝ) × (Fin T → ℝ))) : 0 ≤ expRegretRand R adv := by
  unfold expRegretRand
  calc
    0 = MeasureTheory.lintegral R.law (fun _ => (0 : ℝ≥0∞)) := by
      rw [MeasureTheory.lintegral_zero]
    _ ≤ MeasureTheory.lintegral R.law (fun L => expRegretDet L adv) :=
      MeasureTheory.lintegral_mono (fun L => expRegretDet_nonneg L adv)

end Indep51a
