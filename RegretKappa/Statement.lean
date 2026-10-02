import Mathlib

/-!
# The statement

Online linear regression in dimension one with features revealed one at a time (Section 2 of the
paper). The horizon `T` and the bound `B > 0` on the outcomes are known to the learner. In round
`t` the adversary reveals a feature `x t : ℝ` (no bound), the learner predicts, then the adversary
reveals an outcome `y t` with `|y t| ≤ B`. Rounds are indexed by `Fin T`: round `t` here is round
`t + 1` of the paper.

A learner is deterministic and causal by construction: its prediction in round `t` is a function of
`x 0, ..., x t` and `y 0, ..., y (t - 1)`. Against a deterministic learner an adaptive adversary is
no stronger than the worst fixed pair of sequences `(x, y)` (Section 2.1 of the paper), so the
minimax regret quantifies over pairs. Randomized learners are defined in
`RegretKappa/Corollaries/Statement.lean`.

The regret compares with the best fixed linear predictor `θ * x`, with `θ : ℝ` unbounded. The set
under the infimum is bounded below by `0` (`bddBelow_linearLoss`), so the infimum is the true one
(`bestLinearLoss_le`, `le_bestLinearLoss`). The minimax regret lives in `EReal`, a complete
lattice, and is finite for `B ≥ 0` (`minimaxRegret_nonneg`, `minimaxRegret_le`).

* `UpperBound`: for every `B > 0` and `ε > 0`, for every large `T` some learner has regret at most
  `(3 + ε) B ^ 2 log T` on every play with outcomes bounded by `B`;
* `LowerBound`: for every `B > 0` and `ε > 0`, for every large `T` every learner has regret at
  least `(3 - ε) B ^ 2 log T` on some play with outcomes bounded by `B`;
* `KappaEqThree`: for every `B > 0`, `minimaxRegret T B / (B ^ 2 log T)` tends to `3` in `EReal`,
  the limit of Theorem 1.1 of the paper.

`kappaEqThree_iff` proves `KappaEqThree ↔ UpperBound ∧ LowerBound`. The modules
`RegretKappa.StatementCheck.*` compare this file with two formalizations written separately
(Section 7.2 of the paper).
-/

namespace RegretKappa

open Filter Topology

/-- A deterministic learner for horizon `T`. In round `t` it sees the features `x 0, ..., x t`
and the outcomes `y 0, ..., y (t - 1)`, and predicts a real number. -/
structure Learner (T : ℕ) where
  /-- The prediction in round `t`, from the features up to round `t` and the earlier outcomes. -/
  predict : (t : Fin T) → (Fin (t + 1) → ℝ) → (Fin t → ℝ) → ℝ

/-- The prediction of `L` in round `t` on the play with features `x` and outcomes `y`: `L` is
given the first `t + 1` features and the first `t` outcomes. -/
def Learner.prediction {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) (t : Fin T) : ℝ :=
  L.predict t (fun s => x (Fin.castLE t.isLt s)) (fun s => y (Fin.castLE t.isLt.le s))

/-- The cumulative square loss of the learner on the play `(x, y)`. -/
def learnerLoss {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) : ℝ :=
  ∑ t, (L.prediction x y t - y t) ^ 2

/-- The cumulative square loss of the fixed linear predictor `θ * x` on the play `(x, y)`. -/
def linearLoss {T : ℕ} (θ : ℝ) (x y : Fin T → ℝ) : ℝ :=
  ∑ t, (θ * x t - y t) ^ 2

/-- The losses of the linear predictors are bounded below (by `0`), so their infimum in `ℝ` is
not the junk value of an unbounded set. -/
theorem bddBelow_linearLoss {T : ℕ} (x y : Fin T → ℝ) :
    BddBelow (Set.range fun θ : ℝ => linearLoss θ x y) :=
  ⟨0, by rintro _ ⟨θ, rfl⟩; unfold linearLoss; positivity⟩

/-- The loss of the best fixed linear predictor in hindsight, `θ : ℝ` unbounded. -/
noncomputable def bestLinearLoss {T : ℕ} (x y : Fin T → ℝ) : ℝ :=
  ⨅ θ : ℝ, linearLoss θ x y

/-- `bestLinearLoss` is a lower bound of the losses of the linear predictors. -/
theorem bestLinearLoss_le {T : ℕ} (x y : Fin T → ℝ) (θ : ℝ) :
    bestLinearLoss x y ≤ linearLoss θ x y :=
  ciInf_le (bddBelow_linearLoss x y) θ

/-- `bestLinearLoss` is the greatest lower bound of the losses of the linear predictors. -/
theorem le_bestLinearLoss {T : ℕ} (x y : Fin T → ℝ) {c : ℝ} (h : ∀ θ : ℝ, c ≤ linearLoss θ x y) :
    c ≤ bestLinearLoss x y :=
  le_ciInf h

/-- The regret of `L` on the play `(x, y)`. -/
noncomputable def regret {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) : ℝ :=
  learnerLoss L x y - bestLinearLoss x y

/-- The minimax regret at horizon `T` with outcomes bounded by `B`: the infimum over learners of
the supremum over plays with `|y t| ≤ B` of the regret, in `EReal`. -/
noncomputable def minimaxRegret (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B), (regret L x y : EReal)

/-- The minimax regret is nonnegative (the play `x = 0`, `y = 0`). -/
theorem minimaxRegret_nonneg (T : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ minimaxRegret T B := by
  refine le_iInf fun L =>
    le_iSup_of_le 0 (le_iSup_of_le 0 (le_iSup_of_le (fun _ => by simpa using hB) ?_))
  have h0 : bestLinearLoss (0 : Fin T → ℝ) 0 ≤ 0 := by
    simpa [linearLoss] using bestLinearLoss_le (0 : Fin T → ℝ) 0 0
  have h1 : 0 ≤ learnerLoss L 0 0 := by unfold learnerLoss; positivity
  exact EReal.coe_nonneg.2 (by unfold regret; linarith)

/-- The minimax regret is at most `T B ^ 2` (the learner that always predicts `0`). -/
theorem minimaxRegret_le (T : ℕ) (B : ℝ) : minimaxRegret T B ≤ ((T * B ^ 2 : ℝ) : EReal) := by
  refine iInf_le_of_le ⟨fun _ _ _ => 0⟩ (iSup₂_le fun x y => iSup_le fun hy => ?_)
  refine EReal.coe_le_coe_iff.2 ?_
  have h0 := le_bestLinearLoss x y fun θ => by unfold linearLoss; positivity
  have h1 : learnerLoss ⟨fun _ _ _ => 0⟩ x y ≤ T * B ^ 2 := by
    unfold learnerLoss Learner.prediction
    calc ∑ t, ((0 : ℝ) - y t) ^ 2 ≤ ∑ _t : Fin T, B ^ 2 :=
          Finset.sum_le_sum fun t _ => by
            rw [zero_sub, neg_sq, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hy t) 2
      _ = T * B ^ 2 := by simp
  unfold regret
  linarith

/-- **Upper bound (target).** For every `B > 0` and `ε > 0`, for every large horizon `T`
there is a learner whose regret is at most `(3 + ε) B ^ 2 log T` on every play with `|y t| ≤ B`. -/
def UpperBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T,
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ (3 + ε) * B ^ 2 * Real.log T

/-- **Lower bound (target).** For every `B > 0` and `ε > 0`, for every large horizon `T`
and every learner there is a play with `|y t| ≤ B` on which its regret is at least
`(3 - ε) B ^ 2 log T`. -/
def LowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ (3 - ε) * B ^ 2 * Real.log T ≤ regret L x y

/-- **kappa = 3 (target).** For every `B > 0`, `minimaxRegret T B / (B ^ 2 log T)` tends
to `3` as `T → ∞`, in `EReal`. The denominator is positive for `T ≥ 2`. -/
def KappaEqThree : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxRegret T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop (𝓝 3)

/-- `B ^ 2 log T > 0` for `B > 0` and `T ≥ 2`. -/
theorem scale_pos {B : ℝ} (hB : 0 < B) {T : ℕ} (hT : 2 ≤ T) : 0 < B ^ 2 * Real.log T :=
  mul_pos (pow_pos hB 2) (Real.log_pos (by exact_mod_cast (by omega : 1 < T)))

/-- The real `3` in `EReal` is the numeral `3`. -/
theorem coe_three : ((3 : ℝ) : EReal) = 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, EReal.coe_natCast, Nat.cast_ofNat]

/-- A learner with regret at most `c` on every play bounds the minimax regret by `c`. -/
theorem minimaxRegret_le_of_learner {T : ℕ} {B c : ℝ} (L : Learner T)
    (h : ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ c) :
    minimaxRegret T B ≤ (c : EReal) :=
  iInf_le_of_le L (iSup₂_le fun x y => iSup_le fun hy => EReal.coe_le_coe_iff.2 (h x y hy))

/-- If every learner has regret at least `c` on some play, the minimax regret is at least `c`. -/
theorem le_minimaxRegret {T : ℕ} {B c : ℝ}
    (h : ∀ L : Learner T, ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ c ≤ regret L x y) :
    (c : EReal) ≤ minimaxRegret T B :=
  le_iInf fun L => by
    obtain ⟨x, y, hy, hc⟩ := h L
    exact le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hy (EReal.coe_le_coe_iff.2 hc)))

/-- A minimax regret below `c` is achieved within `c` by some learner. -/
theorem exists_learner_of_minimaxRegret_lt {T : ℕ} {B c : ℝ} (h : minimaxRegret T B < c) :
    ∃ L : Learner T, ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ c := by
  obtain ⟨L, hL⟩ := iInf_lt_iff.1 h
  refine ⟨L, fun x y hy => ?_⟩
  have hle : (regret L x y : EReal) ≤
      ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B), (regret L x y : EReal) :=
    le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hy le_rfl))
  exact (EReal.coe_lt_coe_iff.1 (hle.trans_lt hL)).le

/-- A minimax regret above `c` forces regret at least `c` on some play against every learner. -/
theorem exists_play_of_lt_minimaxRegret {T : ℕ} {B c : ℝ} (h : (c : EReal) < minimaxRegret T B)
    (L : Learner T) : ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ c ≤ regret L x y := by
  obtain ⟨x, hx⟩ := lt_iSup_iff.1 (h.trans_le (iInf_le _ L))
  obtain ⟨y, hy⟩ := lt_iSup_iff.1 hx
  obtain ⟨hb, hc⟩ := lt_iSup_iff.1 hy
  exact ⟨x, y, hb, (EReal.coe_lt_coe_iff.1 hc).le⟩

/-- **Bridge.** The limit statement is equivalent to the two bounds. -/
theorem kappaEqThree_iff : KappaEqThree ↔ UpperBound ∧ LowerBound := by
  constructor
  · intro h
    constructor
    · intro B hB ε hε
      have h1 := (tendsto_order.1 (h B hB)).2 ((3 + ε : ℝ) : EReal)
        (by rw [← coe_three]; exact EReal.coe_lt_coe_iff.2 (by linarith))
      filter_upwards [h1, eventually_ge_atTop 2] with T hT hT2
      have hD := scale_pos hB hT2
      rw [EReal.div_lt_iff (EReal.coe_pos.2 hD) (EReal.coe_ne_top _), ← EReal.coe_mul] at hT
      obtain ⟨L, hL⟩ := exists_learner_of_minimaxRegret_lt hT
      exact ⟨L, fun x y hy => (hL x y hy).trans_eq (by ring)⟩
    · intro B hB ε hε
      have h1 := (tendsto_order.1 (h B hB)).1 ((3 - ε : ℝ) : EReal)
        (by rw [← coe_three]; exact EReal.coe_lt_coe_iff.2 (by linarith))
      filter_upwards [h1, eventually_ge_atTop 2] with T hT hT2
      have hD := scale_pos hB hT2
      rw [EReal.lt_div_iff (EReal.coe_pos.2 hD) (EReal.coe_ne_top _), ← EReal.coe_mul] at hT
      intro L
      obtain ⟨x, y, hy, hc⟩ := exists_play_of_lt_minimaxRegret hT L
      exact ⟨x, y, hy, le_of_eq_of_le (by ring) hc⟩
  · rintro ⟨hU, hL⟩ B hB
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨r, har, hr3⟩ := EReal.lt_iff_exists_real_btwn.1 ha
      have hr3' : r < 3 := by rw [← coe_three] at hr3; exact EReal.coe_lt_coe_iff.1 hr3
      filter_upwards [hL B hB (3 - r) (by linarith), eventually_ge_atTop 2] with T hT hT2
      have hD := scale_pos hB hT2
      refine har.trans_le ?_
      rw [EReal.le_div_iff_mul_le (EReal.coe_pos.2 hD) (EReal.coe_ne_top _), ← EReal.coe_mul]
      have hm := le_minimaxRegret hT
      refine le_of_eq_of_le ?_ hm
      congr 1
      ring
    · obtain ⟨r, h3r, hra⟩ := EReal.lt_iff_exists_real_btwn.1 ha
      have h3r' : 3 < r := by rw [← coe_three] at h3r; exact EReal.coe_lt_coe_iff.1 h3r
      filter_upwards [hU B hB (r - 3) (by linarith), eventually_ge_atTop 2] with T hT hT2
      have hD := scale_pos hB hT2
      refine lt_of_le_of_lt ?_ hra
      rw [EReal.div_le_iff_le_mul (EReal.coe_pos.2 hD) (EReal.coe_ne_top _), ← EReal.coe_mul]
      obtain ⟨L, hL⟩ := hT
      refine (minimaxRegret_le_of_learner L hL).trans_eq ?_
      congr 1
      ring

/-- The two bounds imply kappa = 3. -/
theorem kappaEqThree_of_bounds (hU : UpperBound) (hL : LowerBound) : KappaEqThree :=
  kappaEqThree_iff.2 ⟨hU, hL⟩

end RegretKappa
