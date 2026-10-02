import RegretKappa.Statement

/-!
# Junk values of an expectation over the randomness of a learner

A degenerate probability space gives the junk value `0` to the Bochner integral of the regret of
a family of learners with no measurability condition.

* `BoolBot`, the type `Bool` with the trivial σ-algebra `⊥`, and `muBot`, the Dirac measure at
  `true`. Every nonempty set has outer measure `1` (`muBot_apply`), so a real function that is not
  constant is not almost everywhere equal to a measurable one: it is not integrable, and its
  Bochner integral is the junk value `0` (`integral_muBot_eq_zero`).

The learners `constLearner T 0` and `constLearner T 3` have different regrets on every play with at
least one round and outcomes in `[-1, 1]` (`regret_const_ne`), so the family `famBot T` on `BoolBot`
that takes them has, on every such play, a regret that is not constant in `ω`.
-/

namespace RegretKappa.CorollariesCheck

open MeasureTheory

/-- `Bool` with the trivial σ-algebra. -/
def BoolBot : Type := Bool

instance : MeasurableSpace BoolBot := ⊥

/-- The point `true` of `BoolBot`. -/
def tt : BoolBot := true

/-- The point `false` of `BoolBot`. -/
def ff : BoolBot := false

/-- The Dirac measure at `true` on `BoolBot`. -/
noncomputable def muBot : Measure BoolBot := Measure.dirac tt

instance : IsProbabilityMeasure muBot := by
  unfold muBot
  infer_instance

/-- Every nonempty subset of `BoolBot` has measure `1`: its only measurable superset is the whole
type. -/
theorem muBot_apply {s : Set BoolBot} (hs : s.Nonempty) : muBot s = 1 := by
  rw [← measure_toMeasurable s]
  rcases MeasurableSpace.measurableSet_bot_iff.1 (measurableSet_toMeasurable muBot s) with h | h
  · obtain ⟨a, ha⟩ := hs
    have := subset_toMeasurable muBot s ha
    rw [h] at this
    exact absurd this (Set.notMem_empty a)
  · rw [h, measure_univ]

/-- A function on `BoolBot` that is not constant is not integrable for `muBot`. -/
theorem not_integrable_muBot {f : BoolBot → ℝ} (hf : f tt ≠
    f ff) : ¬Integrable f muBot := by
  intro hi
  obtain ⟨g, hg, hfg⟩ := hi.aemeasurable
  have hc : ∀ b, g b = g tt := fun b => by
    have hm : MeasurableSet (g ⁻¹' {g tt}) :=
      hg (measurableSet_singleton _)
    rcases MeasurableSpace.measurableSet_bot_iff.1 hm with h | h
    · have h1 : tt ∈ g ⁻¹' {g tt} := rfl
      rw [h] at h1
      exact absurd h1 (Set.notMem_empty _)
    · have h1 : b ∈ g ⁻¹' {g tt} := h ▸ Set.mem_univ b
      exact h1
  have hne : {b | ¬f b = g b}.Nonempty := by
    by_cases h1 : f tt = g tt
    · refine ⟨ff, fun h2 => hf ?_⟩
      rw [h1, h2, hc ff]
    · exact ⟨_, h1⟩
  have h0 : muBot {b | ¬f b = g b} = 0 := ae_iff.1 hfg
  rw [muBot_apply hne] at h0
  exact one_ne_zero h0

/-- The Bochner integral of a function on `BoolBot` that is not constant is the junk value `0`. -/
theorem integral_muBot_eq_zero {f : BoolBot → ℝ}
    (hf : f tt ≠ f ff) : ∫ b, f b ∂muBot = 0 :=
  integral_undef (not_integrable_muBot hf)

/-- The learner that always predicts `c`. -/
def constLearner (T : ℕ) (c : ℝ) : Learner T := ⟨fun _ _ _ => c⟩

/-- On every play with at least one round and outcomes in `[-1, 1]`, the learners predicting `3`
and `0` have different regrets: the difference is `∑ (9 - 6 y_t) ≥ 3 T`. -/
theorem regret_const_ne {T : ℕ} (hT : 1 ≤ T) (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) :
    regret (constLearner T 0) x y ≠ regret (constLearner T 3) x y := by
  have hd : regret (constLearner T 3) x y - regret (constLearner T 0) x y =
      ∑ t, (9 - 6 * y t) := by
    unfold regret learnerLoss Learner.prediction constLearner
    rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hs : ∑ _t : Fin T, (3 : ℝ) ≤ ∑ t, (9 - 6 * y t) :=
    Finset.sum_le_sum fun t _ => by linarith [(abs_le.1 (hy t)).2]
  have h3 : (0 : ℝ) < ∑ _t : Fin T, (3 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  intro h
  linarith

/-- The family on `BoolBot` of the learners predicting `0` (at `true`) and `3` (at `false`). -/
def famBot (T : ℕ) (b : BoolBot) : Learner T :=
  cond (show Bool from b) (constLearner T 0) (constLearner T 3)

/-- On every play with at least one round and outcomes in `[-1, 1]`, the regret of `famBot T` is
not constant in `ω`, so its Bochner integral for `muBot` is `0`. -/
theorem integral_famBot {T : ℕ} (hT : 1 ≤ T) (x y : Fin T → ℝ) (hy : ∀ t, |y t| ≤ 1) :
    ∫ b, regret (famBot T b) x y ∂muBot = 0 :=
  integral_muBot_eq_zero (regret_const_ne hT x y hy)

/-- `(3 - 1) 1 ^ 2 log T > 0` for `T ≥ 2`. -/
theorem bound_pos {T : ℕ} (hT : 2 ≤ T) : 0 < (3 - 1) * (1 : ℝ) ^ 2 * Real.log T := by
  have : 1 < (T : ℝ) := by exact_mod_cast (show 1 < T by omega)
  have := Real.log_pos this
  positivity

end RegretKappa.CorollariesCheck
