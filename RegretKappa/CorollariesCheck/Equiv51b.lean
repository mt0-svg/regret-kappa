import RegretKappa.CorollariesCheck.Junk
import RegretKappa.CorollariesCheck.Indep51b
import RegretKappa.Corollaries.Statement

/-!
# The second separate formalization of Corollary 5.1: compared

`Indep51b.DetPlay` is `BoundedFeatures` (`detPlay_iff`). `Indep51b.RandPlay` takes the expected
regret as the Bochner integral of the regret, for a family of learners with no measurability
condition: it is false (`not_randPlay`), refuted by the family `famBot T` on `BoolBot` as
`Indep42b`. Its comment claims that the regret is bounded by `T B ^ 2` on plays with outcomes
bounded by `B`; this is wrong, since the predictions are not bounded.

`Indep51b.Adversary` takes the expected regret against an adversary as an iterated Bochner integral,
again with no measurability in `ω`: it is false as well (`not_adversary_51b`). On `BoolBot` the
constant family at the learner predicting `0` forces the integral `g 0` of its regret over the
adversary to be positive, hence integrable. The families taking the learners predicting `0` and `c`
have a constant outer integrand only if `g c = g 0`; otherwise the outer integral is the junk value
`0`. For `c = 3` and `c = 6` this gives `E (9 T - 6 S) = 0` and `E (36 T - 12 S) = 0` for the sum `S`
of the outcomes, a contradiction since `T > 0`.
-/

namespace RegretKappa.CorollariesCheck.V51b

open MeasureTheory Filter

theorem detPlay_iff : Indep51b.DetPlay ↔ Corollaries.BoundedFeatures := Iff.rfl

theorem not_randPlay : ¬Indep51b.RandPlay.{0} := by
  intro h
  obtain ⟨T, hT, hT2⟩ := ((h 1 one_pos 1 one_pos).and (eventually_ge_atTop 2)).exists
  obtain ⟨x, y, -, hy, hc⟩ := hT BoolBot muBot ⟨famBot T⟩
  have hy1 : ∀ t, |y t| ≤ 1 := fun t => by
    rcases hy t with h1 | h1 | h1 <;> rw [h1] <;> norm_num
  have h0 : ∫ ω, regret (famBot T ω) x y ∂muBot = 0 := integral_famBot (by omega) x y hy1
  rw [h0] at hc
  exact absurd hc (not_le.2 (bound_pos hT2))

theorem not_adversary_51b : ¬Indep51b.Adversary.{0} := by
  intro h
  have hB : 0 < (1 : ℝ) := by norm_num
  have hε : 0 < (1 : ℝ) := by norm_num
  have h_adv := h 1 hB 1 hε
  -- Use Filter.eventually_atTop to get a concrete T₀ such that for all T ≥ T₀ the property holds
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp h_adv
  -- Also get that eventually T ≥ 2
  have h_ge : ∀ᶠ T : ℕ in atTop, 2 ≤ T := eventually_ge_atTop 2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_ge
  -- Take T = max T₀ N 2, which satisfies all three conditions
  let T := max (max T₀ N) 2
  have hT_ge : 2 ≤ T := by
    dsimp [T]
    exact le_max_right _ _
  have hT_T₀ : T₀ ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  -- Get the adversary A for this T
  obtain ⟨A, hA⟩ := hT₀ T hT_T₀
  -- hA : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (L : RandLearner T Ω), ...
  let ν := A.measure
  have : IsProbabilityMeasure ν := A.isProbabilityMeasure
  have h_bound_pos : 0 < (3 - 1) * (1 : ℝ) ^ 2 * Real.log T :=
    bound_pos hT_ge
  -- Define g c = ∫ p, regret (constLearner T c) p.1 p.2 ∂ν
  set g := fun (c : ℝ) => ∫ p : (Fin T → ℝ) × (Fin T → ℝ),
    RegretKappa.regret (constLearner T c) p.1 p.2 ∂ν with hg
  -- The constant learner as a randomized learner on BoolBot
  let L0 : Indep51b.RandLearner T BoolBot := ⟨fun _ => constLearner T 0⟩
  have h_bound0 : (3 - 1) * (1 : ℝ) ^ 2 * Real.log T ≤
      ∫ ω, ∫ p, RegretKappa.regret ((L0.learner ω)) p.1 p.2 ∂ν ∂muBot :=
    hA BoolBot muBot L0
  -- Simplify: L0.learner ω = constLearner T 0, and muBot is Dirac at tt
  have h_double_int : ∫ ω, ∫ p, RegretKappa.regret ((L0.learner ω)) p.1 p.2 ∂ν ∂muBot = g 0 := by
    dsimp [L0, g]
    have : (fun (_ : BoolBot) => ∫ p, RegretKappa.regret (constLearner T 0) p.1 p.2 ∂ν) =
           fun _ => (∫ p, RegretKappa.regret (constLearner T 0) p.1 p.2 ∂ν) := by
      ext ω; rfl
    rw [this]
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  rw [h_double_int] at h_bound0
  have hg0_pos : 0 < g 0 := by linarith
  -- Therefore regret(constLearner T 0) is integrable w.r.t. ν
  have h_int0 : Integrable (fun p : (Fin T → ℝ) × (Fin T → ℝ) =>
      RegretKappa.regret (constLearner T 0) p.1 p.2) ν := by
    by_contra h_not_int
    have h_zero : g 0 = 0 := by
      rw [hg]
      exact MeasureTheory.integral_undef h_not_int
    rw [h_zero] at hg0_pos
    linarith
  -- Now define L3: BoolBot-valued learner that is constLearner T 0 at tt and constLearner T 3 at ff
  let L3 : Indep51b.RandLearner T BoolBot :=
    ⟨fun b => cond b (constLearner T 0) (constLearner T 3)⟩
  -- The outer integrand at tt is g 0, at ff is g 3
  have h_outer_tt : (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L3.learner ω) p.1 p.2 ∂ν) tt = g 0 := by
    dsimp [L3, g]
    unfold tt
    simp
  have h_outer_ff : (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L3.learner ω) p.1 p.2 ∂ν) ff = g 3 := by
    dsimp [L3, g]
    unfold ff
    simp
  -- If g 3 ≠ g 0, then the outer integrand is not constant, so integral_muBot_eq_zero gives 0
  by_cases h_g3_eq_g0 : g 3 = g 0
  · -- g 3 = g 0, continue
    -- Similarly for g 6
    let L6 : Indep51b.RandLearner T BoolBot :=
      ⟨fun b => cond b (constLearner T 0) (constLearner T 6)⟩
    have h_outer_tt6 : (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L6.learner ω) p.1 p.2 ∂ν) tt = g 0 := by
      dsimp [L6, g]
      unfold tt
      simp
    have h_outer_ff6 : (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L6.learner ω) p.1 p.2 ∂ν) ff = g 6 := by
      dsimp [L6, g]
      unfold ff
      simp
    by_cases h_g6_eq_g0 : g 6 = g 0
    · -- Both equal, now derive contradiction
      -- Pointwise identity: regret(constLearner T c) - regret(constLearner T 0) = c^2*T - 2*c*∑ y
      have h_diff (c : ℝ) (x y : Fin T → ℝ) :
          RegretKappa.regret (constLearner T c) x y - RegretKappa.regret (constLearner T 0) x y =
          c ^ 2 * (T : ℝ) - 2 * c * (∑ t, y t) := by
        unfold RegretKappa.regret RegretKappa.learnerLoss RegretKappa.Learner.prediction constLearner
        calc
          ((∑ t : Fin T, (c - y t) ^ 2) - bestLinearLoss x y) - ((∑ t : Fin T, (0 - y t) ^ 2) - bestLinearLoss x y)
              = (∑ t : Fin T, (c - y t) ^ 2) - (∑ t : Fin T, (0 - y t) ^ 2) := by ring
          _ = (∑ t : Fin T, ((c - y t) ^ 2 - (0 - y t) ^ 2)) := by rw [Finset.sum_sub_distrib]
          _ = ∑ t : Fin T, (c ^ 2 - 2 * c * y t) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            ring
          _ = (∑ t : Fin T, c ^ 2) - (∑ t : Fin T, 2 * c * y t) := by rw [Finset.sum_sub_distrib]
          _ = (T : ℝ) * c ^ 2 - 2 * c * (∑ t : Fin T, y t) := by
            simp [Finset.mul_sum]
          _ = c ^ 2 * (T : ℝ) - 2 * c * (∑ t : Fin T, y t) := by ring
      -- Now g 3 = g 0, so the integral of the difference is 0
      have h_int3 : Integrable (fun p : (Fin T → ℝ) × (Fin T → ℝ) =>
          RegretKappa.regret (constLearner T 3) p.1 p.2) ν := by
        by_contra h_not_int
        have h_zero : g 3 = 0 := by
          rw [hg]
          exact MeasureTheory.integral_undef h_not_int
        have hg3_pos : 0 < g 3 := by
          rw [h_g3_eq_g0]
          exact hg0_pos
        rw [h_zero] at hg3_pos
        linarith
      have h_int_diff3 : ∫ p, (RegretKappa.regret (constLearner T 3) p.1 p.2 -
          RegretKappa.regret (constLearner T 0) p.1 p.2) ∂ν = 0 := by
        rw [MeasureTheory.integral_sub h_int3 h_int0]
        have h1 : (∫ a, RegretKappa.regret (constLearner T 3) a.1 a.2 ∂ν) = g 3 := by rw [hg]
        have h2 : (∫ a, RegretKappa.regret (constLearner T 0) a.1 a.2 ∂ν) = g 0 := by rw [hg]
        rw [h1, h2, h_g3_eq_g0, sub_self]
      -- Similarly for g 6
      have h_int6 : Integrable (fun p : (Fin T → ℝ) × (Fin T → ℝ) =>
          RegretKappa.regret (constLearner T 6) p.1 p.2) ν := by
        by_contra h_not_int
        have h_zero : g 6 = 0 := by
          rw [hg]
          exact MeasureTheory.integral_undef h_not_int
        have hg6_pos : 0 < g 6 := by
          rw [h_g6_eq_g0]
          exact hg0_pos
        rw [h_zero] at hg6_pos
        linarith
      have h_int_diff6 : ∫ p, (RegretKappa.regret (constLearner T 6) p.1 p.2 -
          RegretKappa.regret (constLearner T 0) p.1 p.2) ∂ν = 0 := by
        rw [MeasureTheory.integral_sub h_int6 h_int0]
        have h1 : (∫ a, RegretKappa.regret (constLearner T 6) a.1 a.2 ∂ν) = g 6 := by rw [hg]
        have h2 : (∫ a, RegretKappa.regret (constLearner T 0) a.1 a.2 ∂ν) = g 0 := by rw [hg]
        rw [h1, h2, h_g6_eq_g0, sub_self]
      -- Now use the pointwise identity
      set q := fun (p : (Fin T → ℝ) × (Fin T → ℝ)) => ∑ t, p.2 t with hq
      have h_diff3_pointwise : ∀ p, RegretKappa.regret (constLearner T 3) p.1 p.2 -
          RegretKappa.regret (constLearner T 0) p.1 p.2 = 9 * (T : ℝ) - 6 * q p := by
        intro p
        rw [h_diff 3 p.1 p.2, hq]
        ring
      have h_diff6_pointwise : ∀ p, RegretKappa.regret (constLearner T 6) p.1 p.2 -
          RegretKappa.regret (constLearner T 0) p.1 p.2 = 36 * (T : ℝ) - 12 * q p := by
        intro p
        rw [h_diff 6 p.1 p.2, hq]
        ring
      -- Rewrite the integrals using the pointwise identity
      have h_int_9T_minus_6q_fun : Integrable (fun p => 9 * (T : ℝ) - 6 * q p) ν := by
        have : (fun p => 9 * (T : ℝ) - 6 * q p) =
               (fun p => RegretKappa.regret (constLearner T 3) p.1 p.2 -
                         RegretKappa.regret (constLearner T 0) p.1 p.2) := by
          ext p; exact (h_diff3_pointwise p).symm
        rw [this]
        exact h_int3.sub h_int0
      have h_int_36T_minus_12q_fun : Integrable (fun p => 36 * (T : ℝ) - 12 * q p) ν := by
        have : (fun p => 36 * (T : ℝ) - 12 * q p) =
               (fun p => RegretKappa.regret (constLearner T 6) p.1 p.2 -
                         RegretKappa.regret (constLearner T 0) p.1 p.2) := by
          ext p; exact (h_diff6_pointwise p).symm
        rw [this]
        exact h_int6.sub h_int0
      have h_int_9T_minus_6q : ∫ p, (9 * (T : ℝ) - 6 * q p) ∂ν = 0 := by
        rw [← h_int_diff3]
        refine integral_congr_ae ?_
        filter_upwards with p
        rw [h_diff3_pointwise p]
      have h_int_36T_minus_12q : ∫ p, (36 * (T : ℝ) - 12 * q p) ∂ν = 0 := by
        rw [← h_int_diff6]
        refine integral_congr_ae ?_
        filter_upwards with p
        rw [h_diff6_pointwise p]
      have h_int_18T : ∫ p, (18 * (T : ℝ)) ∂ν = 18 * (T : ℝ) := by
        rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      -- Compute the same integral in two ways
      have h_eq : ∫ p, (18 * (T : ℝ)) ∂ν = 0 := by
        calc
          ∫ p, (18 * (T : ℝ)) ∂ν
              = ∫ p, ((36 * (T : ℝ) - 12 * q p) - 2 * (9 * (T : ℝ) - 6 * q p)) ∂ν := by
                refine integral_congr_ae ?_
                filter_upwards with p
                ring
          _ = (∫ p, (36 * (T : ℝ) - 12 * q p) ∂ν) -
              (∫ p, 2 * (9 * (T : ℝ) - 6 * q p) ∂ν) := by
                rw [MeasureTheory.integral_sub h_int_36T_minus_12q_fun
                  (h_int_9T_minus_6q_fun.const_mul 2)]
          _ = 0 - 2 * (∫ p, (9 * (T : ℝ) - 6 * q p) ∂ν) := by
                rw [h_int_36T_minus_12q, MeasureTheory.integral_const_mul]
          _ = 0 - 2 * 0 := by rw [h_int_9T_minus_6q]
          _ = 0 := by ring
      rw [h_int_18T] at h_eq
      have hT_real : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT_ge
      nlinarith
    · -- g 6 ≠ g 0, contradiction via integral_muBot_eq_zero
      have h_not_const : (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L6.learner ω) p.1 p.2 ∂ν) tt ≠
          (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L6.learner ω) p.1 p.2 ∂ν) ff := by
        rw [h_outer_tt6, h_outer_ff6]
        exact Ne.symm h_g6_eq_g0
      have h_int_zero : ∫ ω, (∫ p, RegretKappa.regret (L6.learner ω) p.1 p.2 ∂ν) ∂muBot = 0 :=
        integral_muBot_eq_zero h_not_const
      have h_bound6 : (3 - 1) * (1 : ℝ) ^ 2 * Real.log T ≤
          ∫ ω, ∫ p, RegretKappa.regret (L6.learner ω) p.1 p.2 ∂ν ∂muBot :=
        hA BoolBot muBot L6
      rw [h_int_zero] at h_bound6
      linarith
  · -- g 3 ≠ g 0, contradiction via integral_muBot_eq_zero
    have h_not_const : (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L3.learner ω) p.1 p.2 ∂ν) tt ≠
        (fun (ω : BoolBot) => ∫ p, RegretKappa.regret (L3.learner ω) p.1 p.2 ∂ν) ff := by
      rw [h_outer_tt, h_outer_ff]
      exact Ne.symm h_g3_eq_g0
    have h_int_zero : ∫ ω, (∫ p, RegretKappa.regret (L3.learner ω) p.1 p.2 ∂ν) ∂muBot = 0 :=
      integral_muBot_eq_zero h_not_const
    have h_bound3 : (3 - 1) * (1 : ℝ) ^ 2 * Real.log T ≤
        ∫ ω, ∫ p, RegretKappa.regret (L3.learner ω) p.1 p.2 ∂ν ∂muBot :=
      hA BoolBot muBot L3
    rw [h_int_zero] at h_bound3
    linarith

end RegretKappa.CorollariesCheck.V51b
