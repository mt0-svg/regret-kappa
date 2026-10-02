import Mathlib

/-!
# Asymptotic and `EReal` lemmas for the bridges of the statement

`eventually_le`: `3 log T + 4 log log(T + 2) + c + 2/√T + 4/T ≤ (3 + ε) log T` for all large `T`.
The worst ratio `worstOf R T` of a regret function `R` (the shape of `worstRatio`), its eventual
bounds from an upper and a lower regret bound (`worst_le`, `worst_ge`), and the `EReal` limit
lemmas `tendsto_three`, `le_liminf`, `iInf_limsup`.
-/

namespace RegretKappa.UnknownBT

open Real Filter Topology

theorem eventually_le (c ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      3 * Real.log T + 4 * Real.log (Real.log ((T : ℝ) + 2)) + c + 2 / √(T : ℝ) + 4 / T ≤
        (3 + ε) * Real.log T := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε16 : 0 < ε / 16 := by linarith
  -- log T → ∞ along ℕ
  have h_log_tendsto : Filter.Tendsto (fun (n : ℕ) => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- log(log n) = o(log n) along ℕ (without the +2 shift)
  have h_loglog_o_log : (fun (n : ℕ) => Real.log (Real.log (n : ℝ))) =o[Filter.atTop] (fun (n : ℕ) => Real.log (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto h_log_tendsto
  -- eventually, |log(log n)| ≤ (ε/16) * |log n|
  have h_loglog_abs : ∀ᶠ (T : ℕ) in Filter.atTop, |Real.log (Real.log (T : ℝ))| ≤ (ε / 16) * |Real.log (T : ℝ)| :=
    h_loglog_o_log.bound hε16
  -- eventually, log n ≥ 1 (so both are nonnegative)
  have h_log_ge_one : ∀ᶠ (T : ℕ) in Filter.atTop, (1 : ℝ) ≤ Real.log (T : ℝ) :=
    h_log_tendsto.eventually_ge_atTop (1 : ℝ)
  -- from the above, eventually log(log n) ≤ (ε/16) * log n
  have h_loglog_bound : ∀ᶠ (T : ℕ) in Filter.atTop, Real.log (Real.log (T : ℝ)) ≤ (ε / 16) * Real.log (T : ℝ) := by
    filter_upwards [h_loglog_abs, h_log_ge_one] with T h_abs h_ge
    have h_nonneg : 0 ≤ Real.log (T : ℝ) := by linarith
    have h_loglog_nonneg : 0 ≤ Real.log (Real.log (T : ℝ)) := Real.log_nonneg h_ge
    rw [abs_of_nonneg h_loglog_nonneg, abs_of_nonneg h_nonneg] at h_abs
    exact h_abs
  -- eventually, log 2 ≤ (ε/16) * log T
  have h_log2_bound : ∀ᶠ (T : ℕ) in Filter.atTop, Real.log 2 ≤ (ε / 16) * Real.log (T : ℝ) := by
    have h_event : ∀ᶠ (T : ℕ) in Filter.atTop, (16 * Real.log 2 / ε) ≤ Real.log (T : ℝ) :=
      h_log_tendsto.eventually_ge_atTop (16 * Real.log 2 / ε)
    filter_upwards [h_event] with T hT
    calc
      Real.log 2 = (16 * Real.log 2 / ε) * (ε / 16) := by field_simp [hε.ne.symm]
      _ ≤ Real.log (T : ℝ) * (ε / 16) := mul_le_mul_of_nonneg_right hT (by linarith)
      _ = (ε / 16) * Real.log (T : ℝ) := by ring
  -- for T ≥ 2: T+2 ≤ T^2, so log(T+2) ≤ 2*log T
  -- then log(log(T+2)) ≤ log(2*log T) = log 2 + log(log T)
  have h_shift_bound : ∀ᶠ (T : ℕ) in Filter.atTop, Real.log (Real.log ((T : ℝ) + 2)) ≤ Real.log 2 + Real.log (Real.log (T : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with T hT
    have hT' : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have h_sq : (T : ℝ) + 2 ≤ (T : ℝ) ^ 2 := by
      nlinarith
    have h_log_sq : Real.log ((T : ℝ) + 2) ≤ Real.log ((T : ℝ) ^ 2) :=
      Real.log_le_log (by linarith : 0 < (T : ℝ) + 2) h_sq
    have h_log_pow : Real.log ((T : ℝ) ^ 2) = 2 * Real.log (T : ℝ) :=
      Real.log_pow (T : ℝ) 2
    rw [h_log_pow] at h_log_sq
    -- Now: log(T+2) ≤ 2*log T
    -- Need: log(log(T+2)) ≤ log(2*log T) = log 2 + log(log T)
    have h_log_T_pos : 0 < Real.log (T : ℝ) :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < T from by omega) : (1 : ℝ) < (T : ℝ))
    have h_log_sum_pos : 0 < Real.log ((T : ℝ) + 2) :=
      Real.log_pos (by linarith : (1 : ℝ) < (T : ℝ) + 2)
    have h_log_le : Real.log (Real.log ((T : ℝ) + 2)) ≤ Real.log (2 * Real.log (T : ℝ)) :=
      Real.log_le_log h_log_sum_pos (by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : Real.log (T : ℝ) ≠ 0)] at h_log_le
    exact h_log_le
  -- combine: log(log(T+2)) ≤ log 2 + log(log T) ≤ (ε/16 + ε/16)*log T = (ε/8)*log T
  have h_loglog_final : ∀ᶠ (T : ℕ) in Filter.atTop, Real.log (Real.log ((T : ℝ) + 2)) ≤ (ε / 8) * Real.log (T : ℝ) := by
    filter_upwards [h_shift_bound, h_log2_bound, h_loglog_bound] with T hshift hlog2 hloglog
    linarith
  -- handle the small terms: c + 2/√T + 4/T ≤ (ε/2)*log T
  have h_small_terms : ∀ᶠ (T : ℕ) in Filter.atTop, c + 2 / √(T : ℝ) + 4 / (T : ℝ) ≤ (ε / 2) * Real.log (T : ℝ) := by
    -- first, bound c + 2/√T + 4/T by |c| + 6 for T ≥ 1
    have h_bound_simple : ∀ᶠ (T : ℕ) in Filter.atTop, c + 2 / √(T : ℝ) + 4 / (T : ℝ) ≤ |c| + 6 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with T hT
      have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      have hposT : 0 < (T : ℝ) := by linarith
      have h_sqrt : 2 / √(T : ℝ) ≤ 2 := by
        have h_sqrt_ge_one : (1 : ℝ) ≤ √(T : ℝ) := by
          calc
            (1 : ℝ) = √(1 : ℝ) := by norm_num
            _ ≤ √(T : ℝ) := Real.sqrt_le_sqrt hT'
        have hpos_sqrt : 0 < √(T : ℝ) := Real.sqrt_pos.mpr hposT
        have h_one_div : 1 / √(T : ℝ) ≤ 1 := by
          have h := ((one_div_le_one_div hpos_sqrt (by norm_num : 0 < (1 : ℝ))).mpr h_sqrt_ge_one)
          simpa using h
        calc
          2 / √(T : ℝ) = 2 * (1 / √(T : ℝ)) := by ring
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h_one_div (by norm_num : 0 ≤ (2 : ℝ))
          _ = 2 := by norm_num
      have h_T : 4 / (T : ℝ) ≤ 4 := by
        have h_one_div : 1 / (T : ℝ) ≤ 1 := by
          have h := ((one_div_le_one_div hposT (by norm_num : 0 < (1 : ℝ))).mpr hT')
          simpa using h
        calc
          4 / (T : ℝ) = 4 * (1 / (T : ℝ)) := by ring
          _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left h_one_div (by norm_num : 0 ≤ (4 : ℝ))
          _ = 4 := by norm_num
      -- Now: c + 2/√T + 4/T ≤ |c| + 2 + 4 = |c| + 6
      -- Since c ≤ |c|
      have hc : c ≤ |c| := le_abs_self c
      linarith
    -- second, |c| + 6 ≤ (ε/2)*log T eventually
    have h_target : ∀ᶠ (T : ℕ) in Filter.atTop, |c| + 6 ≤ (ε / 2) * Real.log (T : ℝ) := by
      have h_event : ∀ᶠ (T : ℕ) in Filter.atTop, (2 * (|c| + 6) / ε) ≤ Real.log (T : ℝ) :=
        h_log_tendsto.eventually_ge_atTop (2 * (|c| + 6) / ε)
      filter_upwards [h_event] with T hT
      calc
        |c| + 6 = (2 * (|c| + 6) / ε) * (ε / 2) := by field_simp [hε.ne.symm]
        _ ≤ Real.log (T : ℝ) * (ε / 2) := mul_le_mul_of_nonneg_right hT (by linarith)
        _ = (ε / 2) * Real.log (T : ℝ) := by ring
    filter_upwards [h_bound_simple, h_target] with T hb ht
    linarith
  -- combine all bounds
  filter_upwards [h_loglog_final, h_small_terms] with T hlog hsmall
  -- hlog: log(log(T+2)) ≤ (ε/8)*log T
  -- hsmall: c + 2/√T + 4/T ≤ (ε/2)*log T
  -- Goal: 3*log T + 4*log(log(T+2)) + c + 2/√T + 4/T ≤ (3+ε)*log T
  -- 4*log(log(T+2)) ≤ 4*(ε/8)*log T = (ε/2)*log T
  -- Sum: 3*log T + (ε/2)*log T + (ε/2)*log T = (3+ε)*log T
  nlinarith


/-- The worst ratio at the horizon `T` of a regret function `R`: the supremum over `B > 0` and the
plays with `|y t| ≤ B` of `R T x y / (B² log T)`, in `EReal`. -/
noncomputable def worstOf (R : (T : ℕ) → (Fin T → ℝ) → (Fin T → ℝ) → ℝ) (T : ℕ) : EReal :=
  ⨆ (B : ℝ) (_ : 0 < B) (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B),
    (R T x y : EReal) / ((B ^ 2 * Real.log T : ℝ) : EReal)

theorem worst_le (R : (T : ℕ) → (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (hU : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ B : ℝ, 0 < B →
      ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → R T x y ≤ (3 + ε) * B ^ 2 * Real.log T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, worstOf R T ≤ ((3 + ε : ℝ) : EReal) := by
  have h_event := hU ε hε
  have h_ge_two : ∀ᶠ T : ℕ in atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  filter_upwards [h_event, h_ge_two] with T hT hTge
  have h_log_pos : 0 < Real.log (T : ℝ) := by
    have h_one_lt_T : 1 < (T : ℝ) := by
      have : 2 ≤ T := hTge
      have h' : (1 : ℕ) < T := Nat.one_lt_two.trans_le this
      exact_mod_cast h'
    exact Real.log_pos h_one_lt_T
  unfold worstOf
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun x => iSup_le fun y => iSup_le fun hy => ?_
  have hD_pos : 0 < B ^ 2 * Real.log (T : ℝ) := by
    have hB_sq_pos : 0 < B ^ 2 := pow_pos hB 2
    exact mul_pos hB_sq_pos h_log_pos
  calc
    (R T x y : EReal) / ((B ^ 2 * Real.log (T : ℝ) : ℝ) : EReal)
        = ((R T x y / (B ^ 2 * Real.log (T : ℝ)) : ℝ) : EReal) := by
      simp [EReal.coe_div]
    _ ≤ ((3 + ε : ℝ) : EReal) := by
      rw [EReal.coe_le_coe_iff]
      rw [div_le_iff₀ hD_pos]
      have hineq := hT B hB x y hy
      simpa [mul_assoc] using hineq


theorem worst_ge (R : (T : ℕ) → (Fin T → ℝ) → (Fin T → ℝ) → ℝ)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
      ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ 1) ∧ (3 - ε) * Real.log T ≤ R T x y)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, ((3 - ε : ℝ) : EReal) ≤ worstOf R T := by
  filter_upwards [hL ε hε, Filter.eventually_ge_atTop 2] with T hL_event hT
  rcases hL_event with ⟨x, y, hy_bound, hR⟩
  have hT_real : 1 < (T : ℝ) := by
    have : 2 ≤ T := hT
    have h2 : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast this
    linarith
  have hlog_pos : 0 < Real.log T := Real.log_pos hT_real
  have hDpos : 0 < ((1 : ℝ) ^ 2 * Real.log T : ℝ) := by
    have : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [this, one_mul]
    exact hlog_pos
  have hDposE : (0 : EReal) < ((1 : ℝ) ^ 2 * Real.log T : ℝ) := by
    rw [EReal.coe_pos]
    exact hDpos
  have hDne_top : (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hineq1 : ((3 - ε : ℝ) : EReal) ≤ (R T x y : EReal) / (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) := by
    rw [EReal.le_div_iff_mul_le hDposE hDne_top]
    rw [← EReal.coe_mul]
    rw [EReal.coe_le_coe_iff]
    have : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [this, one_mul]
    exact hR
  have hBpos : 0 < (1 : ℝ) := by norm_num
  calc
    ((3 - ε : ℝ) : EReal) ≤ (R T x y : EReal) / (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) := hineq1
    _ ≤ ⨆ (_ : ∀ t, |y t| ≤ (1 : ℝ)), (R T x y : EReal) / (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) :=
      le_iSup_of_le hy_bound (le_refl _)
    _ ≤ ⨆ (y_1 : Fin T → ℝ), ⨆ (_ : ∀ t, |y_1 t| ≤ (1 : ℝ)),
        (R T x y_1 : EReal) / (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) :=
      le_iSup_of_le y (le_refl _)
    _ ≤ ⨆ (x_1 : Fin T → ℝ), ⨆ (y_1 : Fin T → ℝ), ⨆ (_ : ∀ t, |y_1 t| ≤ (1 : ℝ)),
        (R T x_1 y_1 : EReal) / (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) :=
      le_iSup_of_le x (le_refl _)
    _ ≤ ⨆ (_ : 0 < (1 : ℝ)), ⨆ (x_1 : Fin T → ℝ), ⨆ (y_1 : Fin T → ℝ), ⨆ (_ : ∀ t, |y_1 t| ≤ (1 : ℝ)),
        (R T x_1 y_1 : EReal) / (((1 : ℝ) ^ 2 * Real.log T : ℝ) : EReal) :=
      le_iSup_of_le hBpos (le_refl _)
    _ ≤ worstOf R T := le_iSup_of_le (1 : ℝ) (le_refl _)


theorem tendsto_three (f : ℕ → EReal)
    (h1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, f T ≤ ((3 + ε : ℝ) : EReal))
    (h2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ((3 - ε : ℝ) : EReal) ≤ f T) :
    Tendsto f atTop (𝓝 3) := by
  rw [tendsto_order]
  constructor
  · intro a' ha'
    rcases EReal.lt_iff_exists_real_btwn.mp ha' with ⟨r, hr1, hr2⟩
    have hr_lt_three : (r : ℝ) < 3 := by
      exact (EReal.coe_lt_coe_iff.mp hr2)
    set ε := 3 - r with hε
    have hε_pos : 0 < ε := sub_pos.mpr hr_lt_three
    have h_eps_event : ∀ᶠ T : ℕ in atTop, ((3 - ε : ℝ) : EReal) ≤ f T := h2 ε hε_pos
    have h_sub : (3 : ℝ) - ε = r := by
      dsimp [ε]
      ring
    have h_event : ∀ᶠ T : ℕ in atTop, a' < f T :=
      Filter.Eventually.mono h_eps_event fun T hT => by
        rw [h_sub] at hT
        exact lt_of_lt_of_le hr1 hT
    exact h_event
  · intro a' ha'
    rcases EReal.lt_iff_exists_real_btwn.mp ha' with ⟨r, hr1, hr2⟩
    have h_three_lt_r : (3 : ℝ) < r := by
      exact (EReal.coe_lt_coe_iff.mp hr1)
    set ε := r - 3 with hε
    have hε_pos : 0 < ε := sub_pos.mpr h_three_lt_r
    have h_eps_event : ∀ᶠ T : ℕ in atTop, f T ≤ ((3 + ε : ℝ) : EReal) := h1 ε hε_pos
    have h_add : (3 : ℝ) + ε = r := by
      dsimp [ε]
      ring
    have h_event : ∀ᶠ T : ℕ in atTop, f T < a' :=
      Filter.Eventually.mono h_eps_event fun T hT => by
        rw [h_add] at hT
        exact lt_of_le_of_lt hT hr2
    exact h_event


theorem le_liminf (f : ℕ → EReal)
    (h2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ((3 - ε : ℝ) : EReal) ≤ f T) :
    (3 : EReal) ≤ liminf f atTop := by
  refine (EReal.le_of_forall_lt_iff_le.mp ?_)
  intro z hz
  by_contra! hlt
  rcases EReal.lt_iff_exists_real_btwn.mp hz with ⟨r, hr_liminf, hr_z⟩
  have hr_lt_3 : (r : EReal) < (3 : EReal) := lt_trans hr_z hlt
  have hr_lt_3_real : r < (3 : ℝ) := by
    have := EReal.coe_lt_coe_iff.mp hr_lt_3
    simpa using this
  set ε := (3 : ℝ) - r with hε_def
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have h_event := h2 ε hε_pos
  have h_sub : ((3 : ℝ) - ε) = r := by
    dsimp [ε]
    ring
  have h_event' : ∀ᶠ T : ℕ in atTop, (r : EReal) ≤ f T := by
    simpa [h_sub] using h_event
  have h_le : (r : EReal) ≤ liminf f atTop :=
    Filter.le_liminf_of_le (h := h_event')
  exact lt_irrefl _ (lt_of_lt_of_le hr_liminf h_le)


theorem iInf_limsup {ι : Type*} (f : ι → ℕ → EReal)
    (h1 : ∃ L : ι, Tendsto (f L) atTop (𝓝 3)) (h2 : ∀ L : ι, (3 : EReal) ≤ liminf (f L) atTop) :
    ⨅ L : ι, limsup (f L) atTop = 3 := by
  rcases h1 with ⟨L, hL⟩
  have hlimsup : limsup (f L) atTop = (3 : EReal) := hL.limsup_eq
  have hle : ∀ L : ι, (3 : EReal) ≤ limsup (f L) atTop := by
    intro L
    exact le_trans (h2 L) (liminf_le_limsup (u := f L) (f := atTop))
  apply le_antisymm
  · calc
      ⨅ L : ι, limsup (f L) atTop ≤ limsup (f L) atTop := iInf_le (fun L => limsup (f L) atTop) L
      _ = 3 := hlimsup
  · exact le_iInf hle

end RegretKappa.UnknownBT
