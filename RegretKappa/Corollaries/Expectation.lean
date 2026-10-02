import RegretKappa.Corollaries.Statement

/-!
# Expectations over the randomness of a learner

* `measurable_regret`: for a family of learners whose predictions are measurable in `ω` for each
  fixed history, the regret on a fixed play is measurable in `ω`: the history seen in each round is
  fixed by the play, and the best linear loss does not depend on `ω`.
* `measurable_comap_predict_iff`: such a family is a measurable map into `Learner T` for the
  σ-algebra induced by `Learner.predict`, and conversely.
* `ofReal_le_lintegral_ofReal`, `ofReal_le_lintegral_adv`: a lower bound `c` on the expected regret
  on a play, or against a finite mixture of plays, bounds the lintegral of the positive part of the
  regret by `c⁺`.
* Finite sums of Dirac measures: their lintegrals (`lintegral_sum_dirac`), the probability measures
  among them (`isProbabilityMeasure_sum_dirac`), their almost everywhere properties
  (`ae_sum_dirac`), and the sets of full measure (`sum_dirac_apply_of_mem`).
-/

namespace RegretKappa.Corollaries

open MeasureTheory

theorem measurable_regret {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} {L : Ω → Learner T}
    (hL : ∀ (t : Fin T) (xs : Fin (t + 1) → ℝ) (ys : Fin t → ℝ),
      Measurable fun ω => (L ω).predict t xs ys)
    (x y : Fin T → ℝ) : Measurable fun ω => regret (L ω) x y := by
  unfold regret learnerLoss Learner.prediction
  refine Measurable.sub_const ?_ _
  exact Finset.measurable_sum _ fun t _ => ((hL t _ _).sub_const _).pow_const 2

theorem measurable_comap_predict_iff {Ω : Type*} [MeasurableSpace Ω] {T : ℕ} (L : Ω → Learner T) :
    @Measurable _ _ _ (MeasurableSpace.comap Learner.predict inferInstance) L ↔
      ∀ (t : Fin T) (xs : Fin (t + 1) → ℝ) (ys : Fin t → ℝ),
        Measurable fun ω => (L ω).predict t xs ys := by
  rw [measurable_comap_iff]
  simp only [measurable_pi_iff]
  rfl

theorem expRegret_eq_pos_sub_neg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ℕ} (L : Ω → Learner T) (x y : Fin T → ℝ)
    (hm : Measurable fun ω => regret (L ω) x y) :
    expRegret μ L x y =
      ((∫⁻ ω, ENNReal.ofReal (regret (L ω) x y) ∂μ : ENNReal) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-regret (L ω) x y) ∂μ : ENNReal) : EReal) := by
  set f := fun ω => regret (L ω) x y with hf
  set Y := ∑ t, y t ^ 2 with hY
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have h_nonneg : ∀ ω, f ω + Y ≥ 0 := by
    intro ω
    have h := neg_sum_sq_le_regret (L ω) x y
    dsimp [f, Y] at *
    linarith
  have h_neg_le : ∀ ω, -f ω ≤ Y := by
    intro ω
    have h := neg_sum_sq_le_regret (L ω) x y
    dsimp [f, Y] at *
    linarith
  have h_meas_f : Measurable f := hm
  have h_meas_ofReal_f : Measurable fun ω => ENNReal.ofReal (f ω) :=
    (ENNReal.measurable_ofReal.comp h_meas_f)
  have h_meas_ofReal_f_add_Y : Measurable fun ω => ENNReal.ofReal (f ω + Y) :=
    (ENNReal.measurable_ofReal.comp (h_meas_f.add measurable_const))
  have h_meas_ofReal_Y : Measurable fun (_ : Ω) => ENNReal.ofReal Y := measurable_const
  have h_pointwise : ∀ ω, ENNReal.ofReal (f ω + Y) + ENNReal.ofReal (-f ω) =
      ENNReal.ofReal (f ω) + ENNReal.ofReal Y := by
    intro ω
    by_cases hpos : 0 ≤ f ω
    · have hneg : -f ω ≤ 0 := by linarith
      have hpos_sum : 0 ≤ f ω + Y := by linarith [h_nonneg ω]
      rw [ENNReal.ofReal_of_nonpos hneg, add_zero]
      rw [ENNReal.ofReal_add hpos hY_nonneg]
    · have hneg : f ω ≤ 0 := by linarith
      have hpos_neg : 0 ≤ -f ω := by linarith
      have hpos_sum : 0 ≤ f ω + Y := by linarith [h_nonneg ω]
      rw [ENNReal.ofReal_of_nonpos hneg, zero_add]
      rw [← ENNReal.ofReal_add hpos_sum hpos_neg]
      congr 1
      ring
  set P := ∫⁻ ω, ENNReal.ofReal (f ω + Y) ∂μ with hP
  set S := ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ with hS
  set N := ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ with hN
  have h_int_ennreal : P + N = S + ENNReal.ofReal Y := by
    calc
      P + N = (∫⁻ ω, ENNReal.ofReal (f ω + Y) ∂μ) + (∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ) := by
        simp [hP, hN]
      _ = ∫⁻ ω, ENNReal.ofReal (f ω + Y) + ENNReal.ofReal (-f ω) ∂μ := by
        rw [lintegral_add_left h_meas_ofReal_f_add_Y]
      _ = ∫⁻ ω, ENNReal.ofReal (f ω) + ENNReal.ofReal Y ∂μ := by
        rw [lintegral_congr h_pointwise]
      _ = (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) + (∫⁻ ω, ENNReal.ofReal Y ∂μ) := by
        rw [lintegral_add_right (fun ω => ENNReal.ofReal (f ω)) h_meas_ofReal_Y]
      _ = S + ENNReal.ofReal Y * μ Set.univ := by simp [hS, lintegral_const]
      _ = S + ENNReal.ofReal Y * 1 := by rw [measure_univ]
      _ = S + ENNReal.ofReal Y := by ring
  by_cases hP_top : P = ⊤
  · -- P = ⊤ case: then both sides are ⊤
    have hS_top : S = ⊤ := by
      rw [hP_top] at h_int_ennreal
      have h_top_add : (⊤ : ENNReal) + N = ⊤ := by simp
      rw [h_top_add] at h_int_ennreal
      -- Now h_int_ennreal: ⊤ = S + ENNReal.ofReal Y
      have h_add_top : S + ENNReal.ofReal Y = ⊤ := h_int_ennreal.symm
      rcases (ENNReal.add_eq_top.mp h_add_top) with hS_top' | hY_top
      · exact hS_top'
      · exact (ENNReal.ofReal_ne_top hY_top).elim
    have hN_le : N ≤ ENNReal.ofReal Y := by
      dsimp [N]
      calc
        ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal Y ∂μ :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (h_neg_le ω))
        _ = ENNReal.ofReal Y * μ Set.univ := lintegral_const _
        _ = ENNReal.ofReal Y := by simp
    have hN_lt_top : (N : EReal) ≠ ⊤ := by
      intro hNtop
      have hNtop' : (N : ENNReal) = ⊤ := by
        by_contra hNntop
        have hN_fin : N ≠ ⊤ := hNntop
        have hN_toReal : (N : EReal) = ((N.toReal : ℝ) : EReal) := by
          rw [EReal.coe_ennreal_toReal hN_fin]
        rw [hN_toReal] at hNtop
        simp at hNtop
      rw [hNtop', top_le_iff] at hN_le
      exact ENNReal.ofReal_ne_top hN_le
    have hP_top' : (P : EReal) = ⊤ := by
      rw [hP_top]
      simp
    have hS_top' : (S : EReal) = ⊤ := by
      rw [hS_top]
      simp
    unfold expRegret
    -- Goal: (P : EReal) - (Y : EReal) = (S : EReal) - (N : EReal)
    -- With P = ⊤, S = ⊤
    rw [hP_top', hS_top']
    -- Goal: ⊤ - (Y : EReal) = ⊤ - (N : EReal)
    -- Y : ℝ, so EReal.top_sub_coe applies
    rw [EReal.top_sub_coe Y]
    -- Goal: ⊤ = ⊤ - (N : EReal)
    -- N is finite (hN_lt_top), so convert to ℝ
    have hN_ne_top_ennreal : N ≠ (⊤ : ENNReal) := by
      intro hNtop
      apply hN_lt_top
      -- Need (N : EReal) = ⊤ from N = ⊤
      have hNtop' : (N : EReal) = ⊤ := by
        rw [hNtop]
        simp
      exact hNtop'
    have hN_fin : (N : EReal) = ((N.toReal : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_toReal hN_ne_top_ennreal]
    rw [hN_fin]
    rw [EReal.top_sub_coe]
  · -- finite case: P ≠ ⊤, so S, N are also finite
    have hP_ne_top : P ≠ ⊤ := hP_top
    have hS_ne_top : S ≠ ⊤ := by
      have hS_le_P : S ≤ P := by
        dsimp [S, P]
        refine lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal ?_)
        linarith [hY_nonneg]
      intro hStop
      rw [hStop, top_le_iff] at hS_le_P
      exact hP_ne_top hS_le_P
    have hN_ne_top : N ≠ ⊤ := by
      have hN_le : N ≤ ENNReal.ofReal Y := by
        dsimp [N]
        calc
          ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal Y ∂μ :=
            lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (h_neg_le ω))
          _ = ENNReal.ofReal Y * μ Set.univ := lintegral_const _
          _ = ENNReal.ofReal Y := by simp
      intro hNtop
      rw [hNtop, top_le_iff] at hN_le
      exact ENNReal.ofReal_ne_top hN_le
    have h_ofReal_Y_ne_top : ENNReal.ofReal Y ≠ ⊤ := ENNReal.ofReal_ne_top
    -- Convert to ℝ using toReal
    have h_int_real : P.toReal + N.toReal = S.toReal + Y := by
      calc
        P.toReal + N.toReal = (P + N).toReal := by
          rw [ENNReal.toReal_add hP_ne_top hN_ne_top]
        _ = (S + ENNReal.ofReal Y).toReal := by rw [h_int_ennreal]
        _ = S.toReal + (ENNReal.ofReal Y).toReal := by
          rw [ENNReal.toReal_add hS_ne_top h_ofReal_Y_ne_top]
        _ = S.toReal + Y := by
          rw [ENNReal.toReal_ofReal hY_nonneg]
    -- Convert back to EReal using coe_ennreal_toReal
    have h_eq_ereal : (P : EReal) + (N : EReal) = (S : EReal) + (Y : EReal) := by
      calc
        (P : EReal) + (N : EReal) = ((P.toReal : ℝ) : EReal) + ((N.toReal : ℝ) : EReal) := by
          simp [EReal.coe_ennreal_toReal hP_ne_top, EReal.coe_ennreal_toReal hN_ne_top]
        _ = ((P.toReal + N.toReal : ℝ) : EReal) := by simp
        _ = ((S.toReal + Y : ℝ) : EReal) := by rw [h_int_real]
        _ = ((S.toReal : ℝ) : EReal) + ((Y : ℝ) : EReal) := by simp
        _ = (S : EReal) + (Y : EReal) := by simp [EReal.coe_ennreal_toReal hS_ne_top]
    -- Now deduce the goal
    unfold expRegret
    dsimp [P, S, f, Y]
    -- Goal: ((∫⁻ ω, ENNReal.ofReal (regret (L ω) x y + ∑ t, y t ^ 2) ∂μ : ENNReal) : EReal) -
    --   ((∑ t, y t ^ 2 : ℝ) : EReal) =
    --   ((∫⁻ ω, ENNReal.ofReal (regret (L ω) x y) ∂μ : ENNReal) : EReal) -
    --     ((∫⁻ ω, ENNReal.ofReal (-regret (L ω) x y) ∂μ : ENNReal) : EReal)
    -- i.e., (P : EReal) - (Y : EReal) = (S : EReal) - (N : EReal)
    -- From h_eq_ereal: (P : EReal) + (N : EReal) = (S : EReal) + (Y : EReal)
    -- Since all values are finite (coerced from ℝ), we can use EReal.coe_sub and linarith
    have hP_real : (P : EReal) = ((P.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hP_ne_top).symm
    have hN_real : (N : EReal) = ((N.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hN_ne_top).symm
    have hS_real : (S : EReal) = ((S.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hS_ne_top).symm
    have hY_real : (Y : EReal) = ((Y : ℝ) : EReal) := rfl
    rw [hP_real, hN_real, hS_real, hY_real]
    rw [← EReal.coe_sub, ← EReal.coe_sub]
    -- Goal: ↑(P.toReal - Y) = ↑(S.toReal - N.toReal)
    -- Use exact_mod_cast to reduce to ℝ
    exact_mod_cast by
      -- Goal: P.toReal - Y = S.toReal - N.toReal
      linarith

theorem ofReal_le_lintegral_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ℕ} (L : Ω → Learner T) (x y : Fin T → ℝ) {c : ℝ}
    (hc : (c : EReal) ≤ expRegret μ L x y) :
    ENNReal.ofReal c ≤ ∫⁻ ω, ENNReal.ofReal (regret (L ω) x y) ∂μ := by
  set Y := ∑ t, y t ^ 2 with hY_def
  have hY_nonneg : 0 ≤ Y := by
    unfold Y
    positivity
  set A := ∫⁻ ω, ENNReal.ofReal (regret (L ω) x y) ∂μ with hA_def
  set B := ∫⁻ ω, ENNReal.ofReal (regret (L ω) x y + Y) ∂μ with hB_def
  have h_expRegret : expRegret μ L x y = ((B : ENNReal) : EReal) - ((Y : ℝ) : EReal) := by
    unfold expRegret B Y
    rfl
  have h_pointwise (ω : Ω) : ENNReal.ofReal (regret (L ω) x y + Y) ≤
      ENNReal.ofReal (regret (L ω) x y) + ENNReal.ofReal Y :=
    ENNReal.ofReal_add_le
  have hB_le_A_plus_ofReal_Y : B ≤ A + ENNReal.ofReal Y := by
    unfold B A
    calc
      ∫⁻ ω, ENNReal.ofReal (regret (L ω) x y + Y) ∂μ ≤
          ∫⁻ ω, (ENNReal.ofReal (regret (L ω) x y) + ENNReal.ofReal Y) ∂μ :=
        lintegral_mono h_pointwise
      _ = (∫⁻ ω, ENNReal.ofReal (regret (L ω) x y) ∂μ) +
          (∫⁻ ω, ENNReal.ofReal Y ∂μ) := lintegral_add_right _ measurable_const
      _ = (∫⁻ ω, ENNReal.ofReal (regret (L ω) x y) ∂μ) + ENNReal.ofReal Y := by
        rw [lintegral_const, measure_univ, mul_one]
  have hB_ereal_le_A_ereal_plus_Y : (B : EReal) ≤ (A : EReal) + ((Y : ℝ) : EReal) := by
    calc
      (B : EReal) ≤ ((A + ENNReal.ofReal Y : ENNReal) : EReal) := by
        exact_mod_cast hB_le_A_plus_ofReal_Y
      _ = (A : EReal) + ((ENNReal.ofReal Y : ENNReal) : EReal) := by
        rw [EReal.coe_ennreal_add]
      _ = (A : EReal) + ((Y : ℝ) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left hY_nonneg]
  have hc_ereal_plus_Y_le_B : (c : EReal) + ((Y : ℝ) : EReal) ≤ (B : EReal) := by
    rw [h_expRegret] at hc
    exact EReal.add_le_of_le_sub hc
  have hc_ereal_le_A_ereal : (c : EReal) ≤ (A : EReal) := by
    have h_sum : (c : EReal) + ((Y : ℝ) : EReal) ≤ (A : EReal) + ((Y : ℝ) : EReal) :=
      le_trans hc_ereal_plus_Y_le_B hB_ereal_le_A_ereal_plus_Y
    have h_sub := EReal.sub_le_sub h_sum (le_refl ((Y : ℝ) : EReal))
    -- h_sub : ((c : EReal) + (Y : EReal)) - (Y : EReal) ≤ ((A : EReal) + (Y : EReal)) - (Y : EReal)
    -- simplify both sides using EReal.add_sub_cancel_right
    simpa [EReal.add_sub_cancel_right] using h_sub
  by_cases hc_nonpos : c ≤ 0
  · -- If c ≤ 0, then ENNReal.ofReal c = 0, and the goal is 0 ≤ A
    rw [ENNReal.ofReal_eq_zero.mpr hc_nonpos]
    exact bot_le
  · -- If c > 0, then (c : EReal) = ((ENNReal.ofReal c : ENNReal) : EReal)
    have hc_pos : 0 < c := by linarith
    have h_coe : (c : EReal) = ((ENNReal.ofReal c : ENNReal) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (by linarith [hc_pos])]
    rw [h_coe] at hc_ereal_le_A_ereal
    exact (EReal.coe_ennreal_le_coe_ennreal_iff.mp hc_ereal_le_A_ereal)

theorem ofReal_le_lintegral_adv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ℕ} (L : Ω → Learner T) {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (x y : ι → Fin T → ℝ) {c : ℝ} (hc : (c : EReal) ≤ advRegret μ L w x y) :
    ENNReal.ofReal c ≤
      ∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i)) ∂μ := by
  have hW_nonneg : 0 ≤ ∑ i, w i * ∑ t : Fin T, y i t ^ 2 := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hy_sq_nonneg : 0 ≤ ∑ t : Fin T, y i t ^ 2 :=
      Finset.sum_nonneg fun t _ => sq_nonneg _
    exact mul_nonneg (hw i) hy_sq_nonneg
  have h_pointwise : ∀ ω, (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t : Fin T, y i t ^ 2)) ≤
      (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i))) + ENNReal.ofReal (∑ i, w i * ∑ t : Fin T, y i t ^ 2) := by
    intro ω
    have hsum : (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (∑ t : Fin T, y i t ^ 2)) =
        ENNReal.ofReal (∑ i, w i * ∑ t : Fin T, y i t ^ 2) := by
      calc
        (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (∑ t : Fin T, y i t ^ 2))
            = (∑ i, ENNReal.ofReal (w i * ∑ t : Fin T, y i t ^ 2)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (hw i)]
        _ = ENNReal.ofReal (∑ i, w i * ∑ t : Fin T, y i t ^ 2) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => ?_]
          have hy_sq_nonneg : 0 ≤ ∑ t : Fin T, y i t ^ 2 :=
            Finset.sum_nonneg fun t _ => sq_nonneg _
          exact mul_nonneg (hw i) hy_sq_nonneg
    calc
      (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t : Fin T, y i t ^ 2))
          ≤ (∑ i, ENNReal.ofReal (w i) * (ENNReal.ofReal (regret (L ω) (x i) (y i)) + ENNReal.ofReal (∑ t : Fin T, y i t ^ 2))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        exact ENNReal.ofReal_add_le
      _ = (∑ i, (ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i)) + ENNReal.ofReal (w i) * ENNReal.ofReal (∑ t : Fin T, y i t ^ 2))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add]
      _ = (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i))) + (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (∑ t : Fin T, y i t ^ 2)) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i))) + ENNReal.ofReal (∑ i, w i * ∑ t : Fin T, y i t ^ 2) := by
        rw [hsum]
  set A := fun ω : Ω => ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i)) with hA
  set B := fun ω : Ω => ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t : Fin T, y i t ^ 2) with hB
  set W := ∑ i, w i * ∑ t : Fin T, y i t ^ 2 with hW
  have h_lintegral : (∫⁻ ω, B ω ∂μ) ≤ (∫⁻ ω, A ω ∂μ) + ENNReal.ofReal W := by
    calc
      (∫⁻ ω, B ω ∂μ) ≤ (∫⁻ ω, (A ω + ENNReal.ofReal W) ∂μ) := lintegral_mono h_pointwise
      _ = (∫⁻ ω, A ω ∂μ) + (∫⁻ ω, ENNReal.ofReal W ∂μ) := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const]
      _ = (∫⁻ ω, A ω ∂μ) + ENNReal.ofReal W * (μ Set.univ) := by rw [lintegral_const]
      _ = (∫⁻ ω, A ω ∂μ) + ENNReal.ofReal W := by rw [measure_univ, mul_one]
  have h_advRegret_eq : advRegret μ L w x y = ((∫⁻ ω, B ω ∂μ : ENNReal) : EReal) - ((W : ℝ) : EReal) := by
    rfl
  rw [h_advRegret_eq] at hc
  have h_ineq : (c : EReal) ≤ ((∫⁻ ω, A ω ∂μ : ENNReal) : EReal) := by
    have hJ_le : ((∫⁻ ω, B ω ∂μ : ENNReal) : EReal) ≤ (((∫⁻ ω, A ω ∂μ : ENNReal) + ENNReal.ofReal W : ENNReal) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.2 h_lintegral
    calc
      (c : EReal) ≤ ((∫⁻ ω, B ω ∂μ : ENNReal) : EReal) - ((W : ℝ) : EReal) := hc
      _ ≤ (((∫⁻ ω, A ω ∂μ : ENNReal) + ENNReal.ofReal W : ENNReal) : EReal) - ((W : ℝ) : EReal) :=
        EReal.sub_le_sub hJ_le (le_refl _)
      _ = (((∫⁻ ω, A ω ∂μ : ENNReal) : EReal) + ((ENNReal.ofReal W : ENNReal) : EReal)) - ((W : ℝ) : EReal) := by
        rw [EReal.coe_ennreal_add]
      _ = (((∫⁻ ω, A ω ∂μ : ENNReal) : EReal) + (W : EReal)) - ((W : ℝ) : EReal) := by
        rw [coe_ofReal_of_nonneg hW_nonneg]
      _ = ((∫⁻ ω, A ω ∂μ : ENNReal) : EReal) := by
        rw [EReal.add_sub_cancel_right]
  by_cases hc_nonpos : c ≤ 0
  · rw [ENNReal.ofReal_eq_zero.mpr hc_nonpos]
    apply zero_le
  · have hc_pos : 0 ≤ c := by linarith
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, ENNReal.ofReal_eq_coe_nnreal hc_pos]
    exact h_ineq

theorem lintegral_sum_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {ι : Type*} [Fintype ι] (w : ι → ENNReal) (p : ι → α) (f : α → ENNReal) :
    ∫⁻ a, f a ∂(∑ i, w i • Measure.dirac (p i)) = ∑ i, w i * f (p i) := by
  calc
    ∫⁻ a, f a ∂(∑ i, w i • Measure.dirac (p i)) = ∑ i, ∫⁻ a, f a ∂(w i • Measure.dirac (p i)) := by
      exact lintegral_finsetSum_measure Finset.univ f fun i => w i • Measure.dirac (p i)
    _ = ∑ i, w i * ∫⁻ a, f a ∂(Measure.dirac (p i)) := by
      simp [lintegral_smul_measure]
    _ = ∑ i, w i * f (p i) := by
      simp [lintegral_dirac]

theorem isProbabilityMeasure_sum_dirac {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (p : ι → α) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (w i) • Measure.dirac (p i)) := by
  refine ⟨?h⟩
  calc
    (∑ i, ENNReal.ofReal (w i) • Measure.dirac (p i)) Set.univ
        = (∑ i ∈ Finset.univ, (ENNReal.ofReal (w i) • Measure.dirac (p i))) Set.univ := by simp
    _ = ∑ i ∈ Finset.univ, ((ENNReal.ofReal (w i) • Measure.dirac (p i)) Set.univ) := by
      rw [Measure.finsetSum_apply]
    _ = ∑ i ∈ Finset.univ, (ENNReal.ofReal (w i) * (Measure.dirac (p i)) Set.univ) := by
      simp [Measure.smul_apply]
    _ = ∑ i ∈ Finset.univ, (ENNReal.ofReal (w i) * 1) := by simp
    _ = ∑ i ∈ Finset.univ, ENNReal.ofReal (w i) := by simp
    _ = ENNReal.ofReal (∑ i ∈ Finset.univ, w i) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact hw i
    _ = ENNReal.ofReal (∑ i, w i) := by simp
    _ = ENNReal.ofReal 1 := by rw [hs]
    _ = 1 := by simp

theorem ae_sum_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {ι : Type*}
    [Fintype ι] (w : ι → ENNReal) (p : ι → α) (P : α → Prop) (hP : ∀ i, P (p i)) :
    ∀ᵐ a ∂(∑ i, w i • Measure.dirac (p i)), P a := by
  simp [ae_iff, Measure.dirac_apply, hP]

theorem sum_dirac_apply_of_mem {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (p : ι → α) (s : Set α)
    (hp : ∀ i, p i ∈ s) :
    (∑ i, ENNReal.ofReal (w i) • Measure.dirac (p i)) s = 1 := by
  calc
    (∑ i, ENNReal.ofReal (w i) • Measure.dirac (p i)) s
        = ∑ i, (ENNReal.ofReal (w i) • Measure.dirac (p i)) s := by
      rw [Measure.finsetSum_apply]
    _ = ∑ i, ENNReal.ofReal (w i) • (Measure.dirac (p i)) s := by
      simp_rw [Measure.smul_apply]
    _ = ∑ i, ENNReal.ofReal (w i) • (1 : ENNReal) := by
      simp_rw [Measure.dirac_apply_of_mem (hp _)]
    _ = ∑ i, ENNReal.ofReal (w i) := by simp
    _ = ENNReal.ofReal (∑ i, w i) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact hw i
    _ = ENNReal.ofReal 1 := by rw [hs]
    _ = 1 := by simp

/-- A lower bound `b` on the weighted regret of every learner of the family bounds the expected
regret against the adversary below, with no measurability condition. -/
theorem le_advRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (L : Ω → Learner T) {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x y : ι → Fin T → ℝ) (b : ℝ) (h : ∀ ω, b ≤ ∑ i, w i * regret (L ω) (x i) (y i)) :
    (b : EReal) ≤ advRegret μ L w x y := by
  set S := ∑ i, w i * ∑ t, y i t ^ 2 with hS
  have hS_nonneg : 0 ≤ S := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hy_sq_nonneg : 0 ≤ ∑ t, y i t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
    exact mul_nonneg (hw i) hy_sq_nonneg
  set R := fun (i : ι) (ω : Ω) => regret (L ω) (x i) (y i) with hR
  have hR_nonneg_add : ∀ i ω, 0 ≤ R i ω + ∑ t, y i t ^ 2 := by
    intro i ω
    have hreg := neg_sum_sq_le_regret (L ω) (x i) (y i)
    unfold R
    linarith
  have h_pointwise_eq : ∀ ω,
      ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) =
      ENNReal.ofReal (∑ i, w i * (R i ω + ∑ t, y i t ^ 2)) := by
    intro ω
    calc
      ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2)
          = ∑ i, ENNReal.ofReal (w i * (R i ω + ∑ t, y i t ^ 2)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (hw i)]
      _ = ENNReal.ofReal (∑ i, w i * (R i ω + ∑ t, y i t ^ 2)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hw i) (hR_nonneg_add i ω)]
  have h_pointwise_ineq : ∀ ω,
      ENNReal.ofReal (b + S) ≤ ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) := by
    intro ω
    rw [h_pointwise_eq ω]
    refine ENNReal.ofReal_le_ofReal ?_
    calc
      b + S ≤ (∑ i, w i * regret (L ω) (x i) (y i)) + S := by gcongr; exact h ω
      _ = (∑ i, w i * R i ω) + S := by simp [hR]
      _ = ∑ i, w i * (R i ω + ∑ t, y i t ^ 2) := by
        simp [Finset.sum_add_distrib, mul_add, hS]
  have h_lintegral : ENNReal.ofReal (b + S) ≤
      (∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ) := by
    calc
      ENNReal.ofReal (b + S) = (∫⁻ ω, ENNReal.ofReal (b + S) ∂μ) := by
        rw [lintegral_const, measure_univ, mul_one]
      _ ≤ (∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ) :=
        lintegral_mono h_pointwise_ineq
  have h_advRegret_eq : advRegret μ L w x y =
      ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) -
      ((S : ℝ) : EReal) := by
    simp [advRegret, hR, hS]
  rw [h_advRegret_eq]
  by_cases h_sum_nonneg : 0 ≤ b + S
  · have h_coe : ((ENNReal.ofReal (b + S) : ENNReal) : EReal) = (b + S : ℝ) :=
      coe_ofReal_of_nonneg h_sum_nonneg
    have h_lintegral' : ((ENNReal.ofReal (b + S) : ENNReal) : EReal) ≤
        ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) :=
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 h_lintegral)
    rw [h_coe] at h_lintegral'
    calc
      (b : EReal) = ((b + S : ℝ) : EReal) - ((S : ℝ) : EReal) := by
        calc
          (b : EReal) = ((b + S - S : ℝ) : EReal) := by simp
          _ = ((b + S : ℝ) : EReal) - ((S : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) -
          ((S : ℝ) : EReal) :=
        EReal.sub_le_sub h_lintegral' (le_refl _)
  · have h_sum_neg : b + S < 0 := by linarith
    have h_ofReal_zero : ENNReal.ofReal (b + S) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
    have h_zero_le_lintegral : (0 : ENNReal) ≤
        (∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ) := by
      rw [← h_ofReal_zero]
      exact h_lintegral
    have h_zero_le_lintegral' : (0 : EReal) ≤
        ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) :=
      EReal.coe_ennreal_nonneg _
    have hb_le_negS : (b : EReal) ≤ (-(S : ℝ) : EReal) := by
      have hb_le_negS_real : b ≤ -S := by linarith
      exact (EReal.coe_le_coe_iff.2 hb_le_negS_real)
    calc
      (b : EReal) ≤ (-(S : ℝ) : EReal) := hb_le_negS
      _ = (0 : EReal) - ((S : ℝ) : EReal) := by
        simp
      _ ≤ ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (R i ω + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) -
          ((S : ℝ) : EReal) :=
        EReal.sub_le_sub h_zero_le_lintegral' (le_refl _)

/-- For a randomized learner, the expected regret against the adversary is the weighted sum of the
expectations on its plays. -/
theorem advRegret_eq_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    {L : Ω → Learner T}
    (hL : ∀ (t : Fin T) (xs : Fin (t + 1) → ℝ) (ys : Fin t → ℝ),
      Measurable fun ω => (L ω).predict t xs ys)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (x y : ι → Fin T → ℝ) :
    advRegret μ L w x y =
      ((∑ i, ENNReal.ofReal (w i) *
          ∫⁻ ω, ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) -
        ((∑ i, w i * ∑ t, y i t ^ 2 : ℝ) : EReal) := by
  unfold advRegret
  have hsum : (∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) =
      (∑ i, ENNReal.ofReal (w i) * ∫⁻ ω, ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) := by
    calc
      (∫⁻ ω, ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal)
          = (∑ i, ∫⁻ ω, ENNReal.ofReal (w i) * ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) := by
        rw [MeasureTheory.lintegral_finsetSum Finset.univ]
        intro i hi
        have hmeas : Measurable fun ω => regret (L ω) (x i) (y i) :=
          measurable_regret hL (x i) (y i)
        have hmeas' : Measurable fun ω => ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) :=
          (hmeas.add_const _).ennreal_ofReal
        exact (hmeas'.const_mul (ENNReal.ofReal (w i)))
      _ = (∑ i, ENNReal.ofReal (w i) * ∫⁻ ω, ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hmeas : Measurable fun ω => regret (L ω) (x i) (y i) :=
          measurable_regret hL (x i) (y i)
        have hmeas' : Measurable fun ω => ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) :=
          (hmeas.add_const _).ennreal_ofReal
        rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (w i)) hmeas']
  simp [hsum]

/-- If `c ≤ ∑ w_i A_i - ∑ w_i S_i` for probability weights `w`, then `c ≤ A_i - S_i` for some
`i`. -/
theorem exists_le_of_le_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (A : ι → ENNReal) (S : ι → ℝ) (c : ℝ)
    (h : (c : EReal) ≤
      ((∑ i, ENNReal.ofReal (w i) * A i : ENNReal) : EReal) - ((∑ i, w i * S i : ℝ) : EReal)) :
    ∃ i, (c : EReal) ≤ (A i : EReal) - (S i : EReal) := by
  by_contra! hc
  -- hc : ∀ i, (A i : EReal) - (S i : EReal) < (c : EReal)
  -- For each i, A i ≠ ⊤ (otherwise the subtraction would be ⊤ which can't be < c)
  have hA_ne_top : ∀ i, A i ≠ ⊤ := by
    intro i
    by_contra! htop
    have hsub_eq_top : (A i : EReal) - (S i : EReal) = (⊤ : EReal) := by
      simp [htop]
    have htop_lt : (⊤ : EReal) < (c : EReal) := by
      simpa [hsub_eq_top] using hc i
    exact not_top_lt htop_lt
  -- For each i, set a_i := (A i).toReal, which is ≥ 0
  have ha_nonneg : ∀ i, 0 ≤ (A i).toReal := by
    intro i
    exact ENNReal.toReal_nonneg
  -- From hc i, using EReal.coe_ennreal_toReal and EReal.coe_sub, we get a_i - S i < c in ℝ
  have h_lt_real : ∀ i, (A i).toReal - S i < c := by
    intro i
    have h_lt_ereal : ((A i).toReal : EReal) - (S i : EReal) < (c : EReal) := by
      simpa [EReal.coe_ennreal_toReal (hA_ne_top i)] using hc i
    have h_temp : ((A i).toReal - S i : EReal) < (c : EReal) := by
      simpa [EReal.coe_sub] using h_lt_ereal
    exact (EReal.coe_lt_coe_iff.mp h_temp)
  -- Now we work with the sums
  -- First, rewrite the ENNReal sum using A i = ENNReal.ofReal ((A i).toReal)
  have h_sum_ennreal : (∑ i : ι, ENNReal.ofReal (w i) * A i : ENNReal) =
      ENNReal.ofReal (∑ i : ι, w i * (A i).toReal) := by
    calc
      (∑ i : ι, ENNReal.ofReal (w i) * A i : ENNReal) =
          (∑ i : ι, ENNReal.ofReal (w i) * ENNReal.ofReal ((A i).toReal)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_toReal (hA_ne_top i)]
      _ = (∑ i : ι, ENNReal.ofReal (w i * (A i).toReal)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (hw i)]
      _ = ENNReal.ofReal (∑ i : ι, w i * (A i).toReal) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        have hw_nonneg := hw i
        have ha_nonneg_i := ha_nonneg i
        nlinarith
  -- Now the EReal coercion of the first sum simplifies
  have h_sum_ereal : ((∑ i : ι, ENNReal.ofReal (w i) * A i : ENNReal) : EReal) =
      (∑ i : ι, w i * (A i).toReal : ℝ) := by
    rw [h_sum_ennreal]
    -- EReal.coe_ennreal_ofReal gives ↑(ENNReal.ofReal x) = ↑(max x 0)
    -- Since the sum is ≥ 0, max ... 0 = ...
    rw [EReal.coe_ennreal_ofReal]
    have h_sum_nonneg : 0 ≤ ∑ i : ι, w i * (A i).toReal := by
      refine Finset.sum_nonneg fun i _ => ?_
      have hw_nonneg := hw i
      have ha_nonneg_i := ha_nonneg i
      nlinarith
    rw [max_eq_left h_sum_nonneg]
  -- Now rewrite h using this simplification
  rw [h_sum_ereal] at h
  -- h : (c : EReal) ≤ (∑ i, w i * (A i).toReal : ℝ) - (∑ i, w i * S i : ℝ)
  -- The RHS simplifies: (∑ w_i * a_i) - (∑ w_i * S_i) = ∑ w_i * (a_i - S_i)
  -- First, use EReal.coe_sub to push the subtraction inside the coercion
  have h_sub_ereal : ((∑ i : ι, w i * (A i).toReal : ℝ) : EReal) - ((∑ i : ι, w i * S i : ℝ) : EReal) =
      ((∑ i : ι, w i * (A i).toReal) - (∑ i : ι, w i * S i) : ℝ) := by
    exact (EReal.coe_sub _ _).symm
  rw [h_sub_ereal] at h
  have h_diff : ((∑ i : ι, w i * (A i).toReal : ℝ) - (∑ i : ι, w i * S i : ℝ)) =
      (∑ i : ι, w i * ((A i).toReal - S i) : ℝ) := by
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [h_diff] at h
  -- h : (c : EReal) ≤ (∑ i, w i * ((A i).toReal - S i) : ℝ)
  -- Now we have: ∀ i, (A i).toReal - S i < c, and w i ≥ 0
  -- Also, since ∑ w i = 1 ≠ 0, there exists j with w j > 0
  have h_exists_pos : ∃ i : ι, 0 < w i := by
    by_contra! h_all_zero
    -- h_all_zero : ∀ i, ¬ 0 < w i, i.e., w i ≤ 0 for all i
    -- Combined with hw i : 0 ≤ w i, we get w i = 0 for all i
    have h_all_zero' : ∀ i, w i = 0 := by
      intro i
      have hle := h_all_zero i
      have hge := hw i
      linarith
    -- Then ∑ w i = 0, contradicting hs : ∑ w i = 1
    have hsum_zero : (∑ i : ι, w i) = 0 := by
      simp [h_all_zero']
    rw [hs] at hsum_zero
    linarith
  rcases h_exists_pos with ⟨j, hj_pos⟩
  -- Now we have:
  -- ∀ i, w i * ((A i).toReal - S i) ≤ w i * c  (by mul_le_mul_of_nonneg_left, since (A i).toReal - S i < c)
  -- and at j: w j * ((A j).toReal - S j) < w j * c  (by mul_lt_mul_of_pos_left)
  have h_le : ∀ i, w i * ((A i).toReal - S i) ≤ w i * c := by
    intro i
    have h_lt_i := h_lt_real i
    exact mul_le_mul_of_nonneg_left (by linarith) (hw i)
  have h_lt_j : w j * ((A j).toReal - S j) < w j * c :=
    mul_lt_mul_of_pos_left (h_lt_real j) hj_pos
  -- Now apply Finset.sum_lt_sum
  have h_sum_lt : (∑ i : ι, w i * ((A i).toReal - S i)) < (∑ i : ι, w i * c) :=
    Finset.sum_lt_sum (fun i _ => h_le i) ⟨j, Finset.mem_univ j, h_lt_j⟩
  -- The RHS simplifies: ∑ w i * c = (∑ w i) * c = 1 * c = c
  have h_rhs : (∑ i : ι, w i * c) = c := by
    rw [← Finset.sum_mul, hs, one_mul]
  rw [h_rhs] at h_sum_lt
  -- Now h says (c : EReal) ≤ (∑ ... : ℝ) and h_sum_lt says (∑ ... : ℝ) < c
  -- So we have (c : EReal) ≤ x and x < (c : EReal) for x = ∑ ... in ℝ
  -- This is a contradiction
  have h_contra : ((∑ i : ι, w i * ((A i).toReal - S i) : ℝ) : EReal) < (c : EReal) := by
    simpa using h_sum_lt
  -- But h says (c : EReal) ≤ (∑ ... : ℝ)
  have : ((∑ i : ι, w i * ((A i).toReal - S i) : ℝ) : EReal) < ((∑ i : ι, w i * ((A i).toReal - S i) : ℝ) : EReal) :=
    lt_of_lt_of_le h_contra h
  exact lt_irrefl _ this

end RegretKappa.Corollaries
