import RegretKappa.CorollariesCheck.Indep51a
import RegretKappa.Corollaries.Expectation

/-!
# The first separate formalization of Corollary 5.1: compared

`Indep51a.DetPlay` is `BoundedFeatures` (`detPlay_iff`). `Indep51a` models a randomized learner as
a probability measure on `Learner T`, with the σ-algebra induced by `Learner.predict`, and an
adversary as a probability measure on the plays; it takes every expectation as the lintegral of the
positive part `Reg⁺` of the regret. Since `E (Reg⁺) ≥ (E Reg)⁺`, its statements are weaker than
ours, and they follow from them.

* `Indep51a.RandPlay` follows from `BoundedFeaturesRand` (`randPlay_of_rand`): the identity family
  on `Learner T` is a randomized learner (`measurable_comap_predict_iff`), and a lower bound on its
  expected regret bounds `E (Reg⁺)` (`ofReal_le_lintegral_ofReal`).
* `Indep51a.AdversaryProp` follows from `BoundedFeaturesAdv` (`adversaryProp_of_adv`): the
  adversary is the finite sum of Dirac measures at the plays, weighted by their probabilities, and
  `ofReal_le_lintegral_adv` bounds `E (Reg⁺)` for deterministic learners (a constant family on
  `Unit`) and for randomized ones.

Ours are the stronger readings: the truncation `Reg⁺` drops the negative part of the regret, and
the adversaries of `Indep51a` need not have finitely many plays.
-/

namespace RegretKappa.CorollariesCheck.V51a

open MeasureTheory Filter RegretKappa.Corollaries

theorem detPlay_iff : Indep51a.DetPlay ↔ Corollaries.BoundedFeatures := Iff.rfl

theorem randPlay_of_rand (h : BoundedFeaturesRand.{0}) : Indep51a.RandPlay := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  intro R
  have : IsProbabilityMeasure R.law := R.isProbabilityMeasure
  have h_isRand : IsRandLearner R.law (fun (l : Learner T) => l) := by
    refine ⟨inferInstance, ?_⟩
    exact ((measurable_comap_predict_iff (fun (l : Learner T) => l)).1 measurable_id)
  obtain ⟨x, y, hx, hy, hc⟩ := hT (Learner T) R.law (fun (l : Learner T) => l) h_isRand
  refine ⟨x, y, hx, hy, ?_⟩
  exact ofReal_le_lintegral_ofReal R.law (fun (l : Learner T) => l) x y hc

theorem adversaryProp_of_adv (h : BoundedFeaturesAdv.{0}) : Indep51a.AdversaryProp := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  obtain ⟨ι, _, w, x, y, hw, hs, hx, hy, hadv⟩ := hT
  let ν : Measure ((Fin T → ℝ) × (Fin T → ℝ)) :=
    ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i)
  have h_prob : IsProbabilityMeasure ν :=
    isProbabilityMeasure_sum_dirac w hw hs (fun i => (x i, y i))
  have h_features : ∀ᵐ p ∂ν, ∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1 :=
    ae_sum_dirac (fun i => ENNReal.ofReal (w i)) (fun i => (x i, y i))
      (fun p => ∀ t, p.1 t ∈ Set.Icc (0 : ℝ) 1) (fun i => hx i)
  have h_outcomes : ∀ᵐ p ∂ν, ∀ t, p.2 t ∈ ({-B, 0, B} : Set ℝ) :=
    ae_sum_dirac (fun i => ENNReal.ofReal (w i)) (fun i => (x i, y i))
      (fun p => ∀ t, p.2 t ∈ ({-B, 0, B} : Set ℝ)) (fun i => hy i)
  let adv : Indep51a.Adversary T B :=
    { law := ν
      isProbabilityMeasure := h_prob
      features_range := h_features
      outcomes_range := h_outcomes }
  refine ⟨adv, ?_, ?_⟩
  · intro L
    set c := (3 - ε) * B ^ 2 * Real.log T with hc_def
    have h_adv := hadv Unit (Measure.dirac ()) (fun _ => L) (isRandLearner_const _ L)
    have h_lintegral : ENNReal.ofReal c ≤
        ∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret ((fun _ => L) ω) (x i) (y i)) ∂(Measure.dirac ()) :=
      ofReal_le_lintegral_adv (Measure.dirac ()) (fun _ => L) w hw x y h_adv
    have h_lintegral_dirac : ∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret ((fun _ => L) ω) (x i) (y i)) ∂(Measure.dirac ()) =
        ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret L (x i) (y i)) := by
      simp
    rw [h_lintegral_dirac] at h_lintegral
    have h_expRegretDet : Indep51a.expRegretDet L ν = ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret L (x i) (y i)) := by
      unfold Indep51a.expRegretDet
      rw [lintegral_sum_dirac (fun i => ENNReal.ofReal (w i)) (fun i => (x i, y i))
        (fun p => ENNReal.ofReal (regret L p.1 p.2))]
    rw [h_expRegretDet]
    exact h_lintegral
  · intro R
    set c := (3 - ε) * B ^ 2 * Real.log T with hc_def
    have := R.isProbabilityMeasure
    have h_rand_learner : IsRandLearner R.law (fun (l : RegretKappa.Learner T) => l) := by
      refine ⟨R.isProbabilityMeasure, ?_⟩
      intro t xs ys
      exact (measurable_comap_predict_iff (fun (l : RegretKappa.Learner T) => l)).1 measurable_id t xs ys
    have h_adv := hadv (RegretKappa.Learner T) R.law (fun (l : RegretKappa.Learner T) => l) h_rand_learner
    have h_lintegral : ENNReal.ofReal c ≤
        MeasureTheory.lintegral R.law (fun (ω : RegretKappa.Learner T) =>
          ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret ω (x i) (y i))) :=
      ofReal_le_lintegral_adv R.law (fun (l : RegretKappa.Learner T) => l) w hw x y h_adv
    have h_expRegretRand : Indep51a.expRegretRand R ν =
        MeasureTheory.lintegral R.law (fun (ω : RegretKappa.Learner T) =>
          ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret ω (x i) (y i))) := by
      unfold Indep51a.expRegretRand
      refine lintegral_congr (fun L' => ?_)
      unfold Indep51a.expRegretDet
      rw [lintegral_sum_dirac (fun i => ENNReal.ofReal (w i)) (fun i => (x i, y i))
        (fun p => ENNReal.ofReal (regret L' p.1 p.2))]
    rw [h_expRegretRand]
    exact h_lintegral

end RegretKappa.CorollariesCheck.V51a
