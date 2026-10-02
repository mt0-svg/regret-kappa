import RegretKappa.Statement
import RegretKappa.StatementCheck.Equiv
import RegretKappa.StatementCheck.Indep2

/-!
# The target statement against a second formalization written separately

`RegretKappa.StatementCheck.Indep2` (namespace `Indep2`) is a second formalization of the target,
written separately from the text of the problem after a supremum over plays in `ℝ` had collapsed
the first version. It differs from the target statement in three places:
* the loss of the best linear predictor is the closed form `∑ y ^ 2 - (∑ x y) ^ 2 / ∑ x ^ 2`
  (`∑ y ^ 2` when `∑ x ^ 2 = 0`) instead of an infimum over `θ`;
* the minimax regret `Indep2.RegStar` is the real `sInf` of the guaranteed levels, the `v` such
  that some learner has regret at most `v` on every play;
* the limit is taken in `ℝ`.

Here `bestLinearLoss_eq` proves the closed form (the paper, Lemma 2.2), `coe_RegStar`
proves `Indep2.RegStar T B = minimaxRegret T B` for `B ≥ 0`, and `Indep2.kappaThree_iff`,
`Indep2.upperBound_iff`, `Indep2.lowerBound_iff` prove that the three statements of `Indep2` are
equivalent to `KappaEqThree`, `UpperBound`, `LowerBound`.
-/

open Filter Topology Set

namespace RegretKappa.StatementCheck

/-! ### The loss of the best linear predictor in closed form -/

theorem linearLoss_eq {T : ℕ} (θ : ℝ) (x y : Fin T → ℝ) :
    linearLoss θ x y = θ ^ 2 * ∑ t, x t ^ 2 - 2 * θ * ∑ t, x t * y t + ∑ t, y t ^ 2 := by
  unfold linearLoss
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- The paper, Lemma 2.2: the infimum over `θ` in closed form. -/
theorem bestLinearLoss_eq {T : ℕ} (x y : Fin T → ℝ) :
    bestLinearLoss x y =
      if ∑ t, x t ^ 2 = 0 then ∑ t, y t ^ 2
      else ∑ t, y t ^ 2 - (∑ t, x t * y t) ^ 2 / ∑ t, x t ^ 2 := by
  split_ifs with h
  · have hx : ∀ t, x t = 0 := fun t =>
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i)).1 h t (Finset.mem_univ t))
    have hc : ∀ θ : ℝ, linearLoss θ x y = ∑ t, y t ^ 2 := fun θ => by
      unfold linearLoss
      simp [hx]
    unfold bestLinearLoss
    simp_rw [hc]
    exact ciInf_const
  · have hV : 0 < ∑ t, x t ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun t _ => sq_nonneg _) (Ne.symm h)
    refine le_antisymm ?_ (le_bestLinearLoss x y fun θ => ?_)
    · refine (bestLinearLoss_le x y ((∑ t, x t * y t) / ∑ t, x t ^ 2)).trans_eq ?_
      rw [linearLoss_eq]
      field_simp
      ring
    · rw [linearLoss_eq]
      have hsq : θ ^ 2 * ∑ t, x t ^ 2 - 2 * θ * ∑ t, x t * y t + ∑ t, y t ^ 2 -
          (∑ t, y t ^ 2 - (∑ t, x t * y t) ^ 2 / ∑ t, x t ^ 2) =
          (∑ t, x t ^ 2) * (θ - (∑ t, x t * y t) / ∑ t, x t ^ 2) ^ 2 := by
        field_simp
        ring
      nlinarith [mul_nonneg hV.le (sq_nonneg (θ - (∑ t, x t * y t) / ∑ t, x t ^ 2))]

/-! ### The minimax regret as a real infimum of guaranteed levels -/

/-- The levels `v` that some learner guarantees: its regret is at most `v` on every play. -/
def guaranteed (T : ℕ) (B : ℝ) : Set ℝ :=
  {v | ∃ L : Learner T, ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ v}

/-- For `B ≥ 0` the real infimum of the guaranteed levels is the minimax regret. -/
theorem coe_sInf_guaranteed (T : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ((sInf (guaranteed T B) : ℝ) : EReal) = minimaxRegret T B := by
  have hle := minimaxRegret_le T B
  have hne : (guaranteed T B).Nonempty :=
    ⟨T * B ^ 2 + 1, exists_learner_of_minimaxRegret_lt
      (hle.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)))⟩
  have hbdd : BddBelow (guaranteed T B) := by
    refine ⟨0, ?_⟩
    rintro v ⟨L, hL⟩
    exact (regret_nonneg_zero L).trans (hL 0 0 fun t => by simpa using hB)
  have hm : ((minimaxRegret T B).toReal : EReal) = minimaxRegret T B :=
    EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hle)
      (ne_bot_of_le_ne_bot EReal.zero_ne_bot (minimaxRegret_nonneg T hB))
  rw [← hm, EReal.coe_eq_coe_iff]
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => csInf_le hbdd ?_
    exact exists_learner_of_minimaxRegret_lt (by rw [← hm]; exact EReal.coe_lt_coe_iff.2 hc)
  · refine le_csInf hne ?_
    rintro v ⟨L, hL⟩
    have h := minimaxRegret_le_of_learner L hL
    rw [← hm] at h
    exact EReal.coe_le_coe_iff.1 h

/-! ### The learners and the regret of `Indep2` -/

/-- A learner of `Indep2` as a learner of the target statement. -/
def ofL2 {T : ℕ} (f : Indep2.Learner T) : Learner T := ⟨f.predict⟩

/-- A learner of the target statement as a learner of `Indep2`. -/
def toL2 {T : ℕ} (L : Learner T) : Indep2.Learner T := ⟨L.predict⟩

theorem ofL2_toL2 {T : ℕ} (L : Learner T) : ofL2 (toL2 L) = L := rfl

theorem prediction_ofL2 {T : ℕ} (f : Indep2.Learner T) (x y : Fin T → ℝ) (t : Fin T) :
    (ofL2 f).prediction x y t = f.predict t (Indep2.prefixX x t) (Indep2.prefixY y t) := rfl

/-- The regret of `Indep2` is the target regret. -/
theorem regret2_eq {T : ℕ} (f : Indep2.Learner T) (x y : Fin T → ℝ) :
    Indep2.regret T f x y = regret (ofL2 f) x y := by
  show (∑ t : Fin T, (y t - f.predict t (Indep2.prefixX x t) (Indep2.prefixY y t)) ^ 2) -
      (if ∑ t : Fin T, x t ^ 2 = 0 then ∑ t : Fin T, y t ^ 2
        else ∑ t : Fin T, y t ^ 2 - (∑ t : Fin T, x t * y t) ^ 2 / ∑ t : Fin T, x t ^ 2) =
      regret (ofL2 f) x y
  unfold regret learnerLoss
  rw [bestLinearLoss_eq]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [prediction_ofL2]
  ring

theorem RegStar_eq (T : ℕ) (B : ℝ) : Indep2.RegStar T B = sInf (guaranteed T B) := by
  unfold Indep2.RegStar guaranteed
  congr 1
  ext v
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨ofL2 f, fun x y hy => regret2_eq f x y ▸ hf x y hy⟩
  · rintro ⟨L, hL⟩
    exact ⟨toL2 L, fun x y hy => by rw [regret2_eq, ofL2_toL2]; exact hL x y hy⟩

/-- `Indep2.RegStar` is the target minimax regret. -/
theorem coe_RegStar (T : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (Indep2.RegStar T B : EReal) = minimaxRegret T B := by
  rw [RegStar_eq, coe_sInf_guaranteed T hB]

end RegretKappa.StatementCheck

namespace Indep2

open RegretKappa RegretKappa.StatementCheck

theorem kappaThree_iff : KappaThree ↔ RegretKappa.KappaEqThree := by
  have key : ∀ B : ℝ, 0 < B →
      ((fun T : ℕ => minimaxRegret T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) =
        fun T : ℕ => ((RegStar T B / (B ^ 2 * Real.log T) : ℝ) : EReal)) := fun B hB =>
    funext fun T => by rw [← coe_RegStar T hB.le, EReal.coe_div]
  constructor
  · intro h B hB
    rw [key B hB, ← coe_three, EReal.tendsto_coe]
    exact h B hB
  · intro h B hB
    have h1 := h B hB
    rw [key B hB, ← coe_three, EReal.tendsto_coe] at h1
    exact h1

theorem upperBound_iff : UpperBound ↔ RegretKappa.UpperBound := by
  constructor
  · intro h B hB ε hε
    filter_upwards [h B hB (ε / 2) (by linarith), eventually_ge_atTop 2] with T hT hT2
    have hD := scale_pos hB hT2
    have hlt : (3 + ε / 2) * B ^ 2 * Real.log T < (3 + ε) * B ^ 2 * Real.log T := by nlinarith
    refine exists_learner_of_minimaxRegret_lt ?_
    rw [← coe_RegStar T hB.le]
    exact EReal.coe_lt_coe_iff.2 (hT.trans_lt hlt)
  · intro h B hB ε hε
    filter_upwards [h B hB ε hε] with T ⟨L, hL⟩
    have h1 := minimaxRegret_le_of_learner L hL
    rw [← coe_RegStar T hB.le] at h1
    exact EReal.coe_le_coe_iff.1 h1

theorem lowerBound_iff : LowerBound ↔ RegretKappa.LowerBound := by
  constructor
  · intro h B hB ε hε
    filter_upwards [h B hB (ε / 2) (by linarith), eventually_ge_atTop 2] with T hT hT2
    have hD := scale_pos hB hT2
    have hlt : (3 - ε) * B ^ 2 * Real.log T < (3 - ε / 2) * B ^ 2 * Real.log T := by nlinarith
    refine exists_play_of_lt_minimaxRegret ?_
    rw [← coe_RegStar T hB.le]
    exact EReal.coe_lt_coe_iff.2 (hlt.trans_le hT)
  · intro h B hB ε hε
    filter_upwards [h B hB ε hε] with T hT
    have h1 := le_minimaxRegret hT
    rw [← coe_RegStar T hB.le] at h1
    exact EReal.coe_le_coe_iff.1 h1

end Indep2
