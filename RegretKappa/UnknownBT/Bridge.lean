import RegretKappa.UnknownBT.Statement
import RegretKappa.UnknownBT.Asymptotics
import RegretKappa.Corollaries.Transfer

/-!
# The bridges between the targets of the statement

* `unknownT_of_unknownBT`, `unknownB_of_unknownBT`, `unknownBT_of_everyT`: the learner that knows
  neither `B` nor `T` serves when one of them is known; the literal form implies the eventual form.
* `optimality_of_lowerBound`: the lower bound of regret-kappa (every learner of horizon `T`) gives
  `Optimality` (every anytime learner, through its restriction).
* `bestConstantThree_of_bounds`, `bestConstant_eq_three`: the answer in `EReal` from the two halves.
* `everyT_of_scaleFreeBound`: the explicit scale-free bound, with any constant `c`, gives the
  literal form `UnknownBTEveryT`.
* `unknownT_of_theoremBNum`: `TheoremBNum` and the scaling of the outcomes
  (`RegretKappa.Corollaries.regret_rescale_inv`) give `UnknownT`.
-/

namespace RegretKappa.UnknownBT

open RegretKappa Filter Topology Real

theorem unknownT_of_unknownBT (h : UnknownBT) : UnknownT := by
  obtain ⟨L, hL⟩ := h
  exact fun B hB => ⟨L, fun ε hε => (hL ε hε).mono fun T hT x y hy => hT B hB x y hy⟩

theorem unknownB_of_unknownBT (h : UnknownBT) : UnknownB := by
  obtain ⟨L, hL⟩ := h
  exact fun ε hε => (hL ε hε).mono fun T hT => ⟨L.restrict T, hT⟩

theorem unknownBT_of_everyT (h : UnknownBTEveryT) : UnknownBT := by
  obtain ⟨L, eps, heps, hL⟩ := h
  refine ⟨L, fun ε hε => ?_⟩
  filter_upwards [(tendsto_order.1 heps).2 ε hε, eventually_ge_atTop 2] with T h1 h2 B hB x y hy
  have hlog : 0 ≤ log T := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  have hD : 0 ≤ B ^ 2 * log T := by positivity
  calc regret (L.restrict T) x y ≤ (3 + eps T) * B ^ 2 * log T := hL T h2 B hB x y hy
    _ = (3 + eps T) * (B ^ 2 * log T) := by ring
    _ ≤ (3 + ε) * (B ^ 2 * log T) := mul_le_mul_of_nonneg_right (by linarith) hD
    _ = (3 + ε) * B ^ 2 * log T := by ring

theorem optimality_of_lowerBound (h : LowerBound) : Optimality :=
  fun B hB ε hε => (h B hB ε hε).mono fun T hT L => hT (L.restrict T)

/-- The worst ratio is `worstOf` of the regret of the restrictions. -/
theorem worstRatio_eq (L : AnytimeLearner) :
    worstRatio L = worstOf fun T x y => regret (L.restrict T) x y := rfl

theorem worstRatio_ge (hO : Optimality) (L : AnytimeLearner) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, ((3 - ε : ℝ) : EReal) ≤ worstRatio L T := by
  rw [worstRatio_eq]
  refine worst_ge _ (fun ε hε => ?_) ε hε
  filter_upwards [hO 1 one_pos ε hε] with T hT
  obtain ⟨x, y, hy, h⟩ := hT L
  exact ⟨x, y, hy, by simpa using h⟩

/-- **The answer from the two halves.** -/
theorem bestConstantThree_of_bounds (hU : UnknownBT) (hO : Optimality) : BestConstantThree := by
  obtain ⟨L, hL⟩ := hU
  refine ⟨⟨L, ?_⟩, fun L' => le_liminf _ (worstRatio_ge hO L')⟩
  refine tendsto_three _ ?_ (worstRatio_ge hO L)
  rw [worstRatio_eq]
  exact worst_le _ hL

theorem bestConstant_eq_three (h : BestConstantThree) : bestConstant = 3 :=
  iInf_limsup (fun L => worstRatio L) h.1 h.2

/-! ## The running maximum -/

theorem runMax_nonneg {n : ℕ} (y : Fin n → ℝ) : 0 ≤ runMax y :=
  Finset.le_fold_max _ |>.2 (Or.inl le_rfl)

theorem runMax_le {n : ℕ} {y : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B) (hy : ∀ t, |y t| ≤ B) :
    runMax y ≤ B :=
  Finset.fold_max_le _ |>.2 ⟨hB, fun t _ => hy t⟩

theorem le_runMax {n : ℕ} (y : Fin n → ℝ) (t : Fin n) : |y t| ≤ runMax y :=
  Finset.le_fold_max _ |>.2 (Or.inr ⟨t, Finset.mem_univ t, le_rfl⟩)

/-- **The explicit scale-free bound gives the literal target.** -/
theorem everyT_of_scaleFreeBound {c : ℝ} (h : ScaleFreeBound c) : UnknownBTEveryT := by
  set f : ℕ → ℝ :=
    fun T => (4 * log (log (T + 2)) + c + 2 / √(T : ℝ) + 4 / T) / log T with hf
  refine ⟨learnerBT, fun T => max 0 (f T), ?_, fun T hT B hB x y hy => ?_⟩
  · refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun T => ha.trans_le
      (le_max_left _ _), fun b hb => ?_⟩
    filter_upwards [eventually_le c (b / 2) (by linarith), eventually_ge_atTop 2] with T h1 h2
    have hlog : 0 < log T := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
    have : f T ≤ b / 2 := by
      rw [hf, div_le_iff₀ hlog]
      linarith
    exact lt_of_le_of_lt (max_le (by linarith) this) (by linarith)
  · have hlog : 0 < log T := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
    have hreg := h T (by omega) x y
    set Q := 3 * log T + 4 * log (log (T + 2)) + c + 2 / √(T : ℝ) + 4 / T with hQ
    have hQf : Q = (3 + f T) * log T := by
      rw [hf, hQ]
      field_simp
      ring
    have hM0 := runMax_nonneg y
    have hMB := runMax_le hB.le hy
    have hM2 : runMax y ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hM0 hMB 2
    have hm : max Q 0 ≤ (3 + max 0 (f T)) * log T := by
      refine max_le ?_ ?_
      · rw [hQf]
        exact mul_le_mul_of_nonneg_right (by linarith [le_max_right 0 (f T)]) hlog.le
      · exact mul_nonneg (by linarith [le_max_left 0 (f T)]) hlog.le
    calc regret (learnerBT.restrict T) x y ≤ runMax y ^ 2 * Q := hreg
      _ ≤ runMax y ^ 2 * max Q 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
      _ ≤ B ^ 2 * max Q 0 := mul_le_mul_of_nonneg_right hM2 (le_max_right _ _)
      _ ≤ B ^ 2 * ((3 + max 0 (f T)) * log T) := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = (3 + max 0 (f T)) * B ^ 2 * log T := by ring

/-! ## Scaling an anytime learner -/

/-- The anytime learner `L` run on the outcomes divided by `B`, its predictions multiplied by `B`
(the scaling of the outcomes). -/
noncomputable def AnytimeLearner.scale (L : AnytimeLearner) (B : ℝ) : AnytimeLearner where
  predict t xs ys := B * L.predict t xs fun i => ys i / B

theorem scale_restrict (L : AnytimeLearner) (B : ℝ) (T : ℕ) :
    (L.scale B).restrict T = Lower.rescale (L.restrict T) B⁻¹ := by
  unfold AnytimeLearner.scale AnytimeLearner.restrict Lower.rescale
  congr 1
  funext t xs ys
  show B * L.predict t xs (fun i => ys i / B) = L.predict t xs (fun s => B⁻¹ * ys s) / B⁻¹
  rw [div_inv_eq_mul, mul_comm]
  congr 2
  funext i
  rw [div_eq_inv_mul]

theorem regret_scale (L : AnytimeLearner) {B : ℝ} (hB : B ≠ 0) {T : ℕ} (x y : Fin T → ℝ) :
    regret ((L.scale B).restrict T) x y = B ^ 2 * regret (L.restrict T) x fun t => y t / B := by
  rw [scale_restrict L B T, Corollaries.regret_rescale_inv _ hB]

/-- **`B` known, `T` unknown**: `TheoremBNum` gives `UnknownT`. -/
theorem unknownT_of_theoremBNum (h : TheoremBNum) : UnknownT := by
  intro B hB
  refine ⟨learnerB.scale B, fun ε hε => ?_⟩
  filter_upwards [eventually_le 1.3706 ε hε, eventually_ge_atTop 1] with T h1 h2 x y hy
  rw [regret_scale _ hB.ne']
  have hy' : ∀ t, |y t / B| ≤ 1 := fun t => by
    rw [abs_div, abs_of_pos hB, div_le_one hB]
    exact hy t
  have h3 := h T h2 x _ hy'
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  calc B ^ 2 * regret (learnerB.restrict T) x (fun t => y t / B)
      ≤ B ^ 2 * (3 * log T + 4 * log (log (T + 2)) + 1.3706 + 2 / √(T : ℝ) + 4 / T) :=
        mul_le_mul_of_nonneg_left h3 hB2
    _ ≤ B ^ 2 * ((3 + ε) * log T) := mul_le_mul_of_nonneg_left h1 hB2
    _ = (3 + ε) * B ^ 2 * log T := by ring

end RegretKappa.UnknownBT
