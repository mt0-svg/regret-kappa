import RegretKappa.CorollariesCheck.Junk
import RegretKappa.CorollariesCheck.Indep51c
import RegretKappa.Corollaries.Expectation

/-!
# The third separate formalization of Corollary 5.1: compared

Written after the four pitfalls of the first round had been pointed out. `Indep51c.DetPlay` is
`BoundedFeatures` (`detPlay_iff`). `Indep51c` takes every expectation as `E (Reg⁺) - E (Reg⁻)`
with two lintegrals in `EReal`, and imposes no measurability on the family of learners (its comment
says that the lintegral is the lower integral, defined for every function). With the trivial
σ-algebra on the learners themselves the lower integral of a function is its infimum, and both
parts vanish on every play (`lintegral_learnerBot_pos`, `lintegral_learnerBot_neg`): every
randomized learner of this kind has expected regret `0`, so `Indep51c.RandPlay` is false
(`not_randPlay`).

`Indep51c.Adversary` follows from `BoundedFeaturesAdv` (`adversary_of_adv`). The adversary is the
finite sum of Dirac measures at the plays, weighted by their probabilities; against a deterministic
learner its expected regret is the weighted sum of the regrets (`expectedRegretSingle_sum_dirac`).
The randomized clause of `Indep51c.Adversary` follows from the deterministic one with no
measurability, by monotonicity of the lintegral (`le_againstAdversary`). Ours is the stronger
reading: the adversaries of `Indep51c` need not have finitely many plays.
-/

namespace RegretKappa.CorollariesCheck.V51c

open MeasureTheory Filter RegretKappa.Corollaries

theorem detPlay_iff : Indep51c.DetPlay ↔ Corollaries.BoundedFeatures := Iff.rfl

theorem expectedRegret_learnerBot {T : ℕ} (μ : Measure (LearnerBot T)) (x y : Fin T → ℝ) :
    Indep51c.expectedRegret μ (fun l : LearnerBot T => (l : Learner T)) x y = 0 := by
  have h1 : ∫⁻ l, ENNReal.ofReal ((regret (show Learner T from l) x y)⁺) ∂μ = 0 :=
    lintegral_bot_eq_zero (a := show LearnerBot T from perfect y) (by
      rw [posPart_eq_zero.2 (regret_perfect_nonpos x y), ENNReal.ofReal_zero])
  have h2 : ∫⁻ l, ENNReal.ofReal ((regret (show Learner T from l) x y)⁻) ∂μ = 0 :=
    lintegral_bot_eq_zero (a := show LearnerBot T from double y) (by
      rw [negPart_eq_zero.2 (regret_double_nonneg x y), ENNReal.ofReal_zero])
  unfold Indep51c.expectedRegret
  simp only [h1, h2, EReal.coe_ennreal_zero, sub_zero]

theorem not_randPlay : ¬Indep51c.RandPlay.{0} := by
  intro h
  obtain ⟨T, hT, hT2⟩ := ((h 1 one_pos 1 one_pos).and (eventually_ge_atTop 2)).exists
  obtain ⟨x, y, -, -, hc⟩ := hT (LearnerBot T)
    (Measure.dirac (show LearnerBot T from constLearner T 0)) inferInstance
    (fun l : LearnerBot T => (l : Learner T))
  have e : (3 - ((1 : ℝ) : EReal)) * ((1 : ℝ) : EReal) ^ 2 * ((Real.log T : ℝ) : EReal) =
      (((3 - 1) * 1 ^ 2 * Real.log T : ℝ) : EReal) := by
    rw [← coe_three, ← EReal.coe_sub, ← EReal.coe_pow, ← EReal.coe_mul, ← EReal.coe_mul]
  rw [e, expectedRegret_learnerBot] at hc
  exact absurd (EReal.coe_nonpos.1 hc) (not_le.2 (bound_pos hT2))

theorem expectedRegretSingle_sum_dirac {T : ℕ} (L : Learner T) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x y : ι → Fin T → ℝ) :
    Indep51c.expectedRegretSingle L (∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i)) =
      ((∑ i, w i * regret L (x i) (y i) : ℝ) : EReal) := by
  simp only [Indep51c.expectedRegretSingle]
  set ν := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i) with hν
  have hpos_int : (∫⁻ p, ENNReal.ofReal ((regret L p.1 p.2)⁺) ∂ν) =
      ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i))⁺) := by
    rw [hν]
    calc
      (∫⁻ p, ENNReal.ofReal ((regret L p.1 p.2)⁺) ∂(∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i)))
          = ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal ((regret L (x i, y i).1 (x i, y i).2)⁺) := by
        rw [lintegral_sum_dirac]
      _ = ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal ((regret L (x i) (y i))⁺) := by simp
      _ = ∑ i, ENNReal.ofReal (w i * (regret L (x i) (y i))⁺) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ENNReal.ofReal_mul (hw i)]
      _ = ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i))⁺) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        have hwi := hw i
        have hpos := posPart_nonneg (regret L (x i) (y i))
        nlinarith
  have hneg_int : (∫⁻ p, ENNReal.ofReal ((regret L p.1 p.2)⁻) ∂ν) =
      ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i))⁻) := by
    rw [hν]
    calc
      (∫⁻ p, ENNReal.ofReal ((regret L p.1 p.2)⁻) ∂(∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i)))
          = ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal ((regret L (x i, y i).1 (x i, y i).2)⁻) := by
        rw [lintegral_sum_dirac]
      _ = ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal ((regret L (x i) (y i))⁻) := by simp
      _ = ∑ i, ENNReal.ofReal (w i * (regret L (x i) (y i))⁻) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ENNReal.ofReal_mul (hw i)]
      _ = ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i))⁻) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        have hwi := hw i
        have hneg := negPart_nonneg (regret L (x i) (y i))
        nlinarith
  rw [hpos_int, hneg_int]
  have hpos_sum_nonneg : 0 ≤ ∑ i, w i * (regret L (x i) (y i))⁺ := by
    refine Finset.sum_nonneg fun i hi => ?_
    have hwi := hw i
    have hpos := posPart_nonneg (regret L (x i) (y i))
    nlinarith
  have hneg_sum_nonneg : 0 ≤ ∑ i, w i * (regret L (x i) (y i))⁻ := by
    refine Finset.sum_nonneg fun i hi => ?_
    have hwi := hw i
    have hneg := negPart_nonneg (regret L (x i) (y i))
    nlinarith
  have hpos_ereal : ((ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i))⁺) : ENNReal) : EReal) =
      ((∑ i, w i * (regret L (x i) (y i))⁺ : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hpos_sum_nonneg]
  have hneg_ereal : ((ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i))⁻) : ENNReal) : EReal) =
      ((∑ i, w i * (regret L (x i) (y i))⁻ : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hneg_sum_nonneg]
  rw [hpos_ereal, hneg_ereal]
  rw [← EReal.coe_sub]
  congr 1
  calc
    (∑ i, w i * (regret L (x i) (y i))⁺) - (∑ i, w i * (regret L (x i) (y i))⁻)
        = ∑ i, (w i * (regret L (x i) (y i))⁺ - w i * (regret L (x i) (y i))⁻) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ i, w i * ((regret L (x i) (y i))⁺ - (regret L (x i) (y i))⁻) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_sub]
    _ = ∑ i, w i * regret L (x i) (y i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [posPart_sub_negPart]

universe u

theorem le_againstAdversary {T : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (L : Ω → Learner T) (ν : Measure ((Fin T → ℝ) × (Fin T → ℝ)))
    (c : ℝ) (hc : ∀ ω, (c : EReal) ≤ Indep51c.expectedRegretSingle (L ω) ν) :
    (c : EReal) ≤ Indep51c.expectedRegretAgainstAdversary μ L ν := by
  set E := fun ω : Ω => Indep51c.expectedRegretSingle (L ω) ν with hE
  have hEpos_nonneg : ∀ ω, 0 ≤ (E ω)⁺ := fun ω => posPart_nonneg _
  have hEneg_nonneg : ∀ ω, 0 ≤ (E ω)⁻ := fun ω => negPart_nonneg _
  unfold Indep51c.expectedRegretAgainstAdversary
  by_cases hc_nonneg : 0 ≤ c
  · -- case 0 ≤ c
    have hE_nonneg : ∀ ω, 0 ≤ E ω := by
      intro ω
      have hc_nonneg_ereal : (0 : EReal) ≤ (c : EReal) := by exact_mod_cast hc_nonneg
      exact le_trans hc_nonneg_ereal (hc ω)
    have hE_neg_zero : ∀ ω, (E ω)⁻ = (0 : EReal) := by
      intro ω
      have h := hE_nonneg ω
      have h' : -E ω ≤ (0 : EReal) := by
        have : 0 ≤ -(-E ω) := by simpa using h
        exact ((EReal.neg_nonneg (a := -E ω)).mp this)
      rw [show (E ω)⁻ = (-E ω) ⊔ (0 : EReal) from rfl]
      rw [sup_eq_right.mpr h']
    have hE_pos_eq : ∀ ω, (E ω)⁺ = E ω := by
      intro ω
      have h := hE_nonneg ω
      rw [show (E ω)⁺ = (E ω) ⊔ (0 : EReal) from rfl]
      rw [sup_eq_left.mpr h]
    -- negative lintegral is zero
    have h_neg_lintegral : (∫⁻ ω, ((E ω)⁻).toENNReal ∂μ).toEReal = (0 : EReal) := by
      simp [hE_neg_zero]
    -- pointwise inequality for the positive part
    have h_pos_pointwise : ∀ ω, ENNReal.ofReal c ≤ (E ω).toENNReal := by
      intro ω
      have h := hc ω
      have h_toENNReal := EReal.toENNReal_le_toENNReal h
      simpa [EReal.real_coe_toENNReal] using h_toENNReal
    have h_pos_pointwise' : ∀ ω, ENNReal.ofReal c ≤ ((E ω)⁺).toENNReal := by
      intro ω
      simpa [hE_pos_eq ω] using h_pos_pointwise ω
    -- integrate
    have h_pos_lintegral : ENNReal.ofReal c ≤ ∫⁻ ω, ((E ω)⁺).toENNReal ∂μ := by
      calc
        ENNReal.ofReal c = ∫⁻ ω, ENNReal.ofReal c ∂μ := by
          simp [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
        _ ≤ ∫⁻ ω, ((E ω)⁺).toENNReal ∂μ := MeasureTheory.lintegral_mono h_pos_pointwise'
    -- convert to EReal
    have h_pos_eReal : (c : EReal) ≤ (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal := by
      have h_coe : (ENNReal.ofReal c : EReal) = (max c 0 : EReal) := EReal.coe_ennreal_ofReal
      have h_max : (max c 0 : ℝ) = c := max_eq_left hc_nonneg
      have h_eq : (ENNReal.ofReal c : EReal) = (c : EReal) := by
        exact coe_ofReal_of_nonneg hc_nonneg
      have h_le : (ENNReal.ofReal c : EReal) ≤ (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal :=
        (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_pos_lintegral)
      simpa [h_eq] using h_le
    -- assemble the result
    calc
      (c : EReal) ≤ (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal := h_pos_eReal
      _ = (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal - (0 : EReal) := by simp
      _ = (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal -
          (∫⁻ ω, ((E ω)⁻).toENNReal ∂μ).toEReal := by rw [h_neg_lintegral]
  · -- case c < 0
    have hc_neg : c < 0 := by linarith
    have hE_neg_le_neg_c : ∀ ω, (E ω)⁻ ≤ (-c : EReal) := by
      intro ω
      by_cases hE_nonneg : 0 ≤ E ω
      · -- E ω ≥ 0, so (E ω)⁻ = 0 ≤ -c (since c < 0)
        have h_neg_zero : (E ω)⁻ = (0 : EReal) := by
          have h' : -E ω ≤ (0 : EReal) := by
            have : 0 ≤ -(-E ω) := by simpa using hE_nonneg
            exact ((EReal.neg_nonneg (a := -E ω)).mp this)
          rw [show (E ω)⁻ = (-E ω) ⊔ (0 : EReal) from rfl]
          rw [sup_eq_right.mpr h']
        rw [h_neg_zero]
        have h_neg_c_nonneg : (0 : EReal) ≤ (-c : EReal) := by
          have : 0 ≤ -c := by linarith
          exact_mod_cast this
        exact h_neg_c_nonneg
      · -- E ω < 0, so (E ω)⁻ = -E ω
        have hE_nonpos : E ω ≤ (0 : EReal) := le_of_not_ge hE_nonneg
        have h_neg_eq : (E ω)⁻ = -E ω := by
          have h' : (0 : EReal) ≤ -E ω := (EReal.neg_nonneg.mpr hE_nonpos)
          rw [show (E ω)⁻ = (-E ω) ⊔ (0 : EReal) from rfl]
          rw [sup_eq_left.mpr h']
        rw [h_neg_eq]
        -- from hc ω : c ≤ E ω, we get -E ω ≤ -c
        have h_neg_le : -E ω ≤ (-c : EReal) := by
          have h_ereal : (c : EReal) ≤ E ω := hc ω
          exact (EReal.neg_le_neg_iff.mpr h_ereal)
        exact h_neg_le
    -- pointwise inequality for the negative part
    have h_neg_pointwise : ∀ ω, ((E ω)⁻).toENNReal ≤ ENNReal.ofReal (-c) := by
      intro ω
      have h_le_ereal := hE_neg_le_neg_c ω
      have h_toENNReal := EReal.toENNReal_le_toENNReal h_le_ereal
      simpa [EReal.real_coe_toENNReal] using h_toENNReal
    -- integrate the negative part
    have h_neg_lintegral : (∫⁻ ω, ((E ω)⁻).toENNReal ∂μ).toEReal ≤ (-c : EReal) := by
      calc
        (∫⁻ ω, ((E ω)⁻).toENNReal ∂μ).toEReal ≤ (∫⁻ ω, ENNReal.ofReal (-c) ∂μ).toEReal :=
          (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (MeasureTheory.lintegral_mono h_neg_pointwise))
        _ = (ENNReal.ofReal (-c) * μ Set.univ).toEReal := by rw [MeasureTheory.lintegral_const]
        _ = (ENNReal.ofReal (-c) * 1).toEReal := by
          rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
        _ = (ENNReal.ofReal (-c)).toEReal := by simp
        _ = (max (-c) 0 : EReal) := EReal.coe_ennreal_ofReal
        _ = (-c : EReal) := by
          have h_nonneg : 0 ≤ -c := by linarith
          have h_nonneg_ereal : (0 : EReal) ≤ (-c : EReal) := by exact_mod_cast h_nonneg
          exact max_eq_left h_nonneg_ereal
    -- the positive part is ≥ 0
    have h_pos_lintegral_nonneg : (0 : EReal) ≤ (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal := by
      have h_nonneg_ennreal : 0 ≤ ∫⁻ ω, ((E ω)⁺).toENNReal ∂μ :=
        zero_le (a := ∫⁻ ω, ((E ω)⁺).toENNReal ∂μ)
      exact (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_nonneg_ennreal)
    -- combine using sub_le_sub
    calc
      (c : EReal) = (0 : EReal) - (-c : EReal) := by
        simp
      _ ≤ (∫⁻ ω, ((E ω)⁺).toENNReal ∂μ).toEReal -
          (∫⁻ ω, ((E ω)⁻).toENNReal ∂μ).toEReal :=
        EReal.sub_le_sub h_pos_lintegral_nonneg h_neg_lintegral

theorem adversary_of_adv (h : BoundedFeaturesAdv.{0}) : Indep51c.Adversary.{u} := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  obtain ⟨ι, _, w, x, y, hw, hs, hx, hy, hadv⟩ := hT
  have hdet : ∀ l : Learner T, (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤
      Indep51c.expectedRegretSingle l (∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i)) := by
    intro l
    have h1 := hadv Unit (Measure.dirac ()) (fun _ => l) (isRandLearner_const _ l)
    rw [advRegret_const _ l hw] at h1
    rwa [expectedRegretSingle_sum_dirac l w hw x y]
  refine ⟨∑ i, ENNReal.ofReal (w i) • Measure.dirac (x i, y i),
    isProbabilityMeasure_sum_dirac w hw hs _,
    sum_dirac_apply_of_mem w hw hs _ _ fun i => ⟨hx i, hy i⟩, fun l => ?_,
    fun Ω _ μ hμ L => ?_⟩
  · rw [ge_iff_le, coe_bound]
    exact hdet l
  · rw [ge_iff_le, coe_bound]
    exact le_againstAdversary μ L _ _ fun ω => hdet (L ω)

end RegretKappa.CorollariesCheck.V51c
