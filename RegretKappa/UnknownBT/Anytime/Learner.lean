import RegretKappa.UnknownBT.Statement
import RegretKappa.UpperSharp.Assembly

/-!
# The potential learner with a free level

`learnerLam lam` predicts in round `t` the prediction `predLam` of the statement at the level
`lam t`; `learnerB` is `learnerLam lamB`. With a free level, the statements of regret-kappa about
the known-horizon learner hold as they are: the prediction is `Upper.pred (λ/2)` (`predLam_eq`, the
proof of `UpperSharp.predU_eq`), one round is the one-round inequality at the level `λ`
(`stepLam`, from `UpperSharp.step_sharp`), and the regret is the sum of the costs `ŷ² - 2ŷy`
plus `ρ_T²` (`regret_eqLam`, the regret identity).
-/

namespace RegretKappa.UnknownBT

open RegretKappa RegretKappa.UpperSharp Real Finset

/-- The potential learner with the level `lam t` in round `t`. -/
noncomputable def learnerLam (lam : ℕ → ℝ) : AnytimeLearner where
  predict t xs ys := predLam (lam t) (∑ i : Fin t, xs (Fin.castSucc i) * ys i)
    (∑ i : Fin t, xs (Fin.castSucc i) ^ 2) (xs (Fin.last t))

theorem learnerB_eq : learnerB = learnerLam lamB := rfl

/-- At the level `λ₀ + 3 (T - t - 1)`, `predLam` is the prediction of the known-horizon learner. -/
theorem predU_eq_predLam (T t : ℕ) (S V x : ℝ) : predU T t S V x = predLam (lamU T t) S V x := rfl

/-- The prediction `predLam` at the level `λ` is `Upper.pred (λ/2)` on a state with `V = 0 → S = 0`. -/
theorem predLam_eq (lam : ℝ) {S V x : ℝ} (hV : 0 ≤ V) (hSV : V = 0 → S = 0) :
    predLam lam S V x = Upper.pred (lam / 2) S V x := by
  unfold predLam Upper.pred
  dsimp only
  rw [a_eq hV hSV, eta_Gam, ← b_eq (x := x) hV]
  generalize √(if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)) = w
  split_ifs with hx
  · rw [neg_one_mul, neg_one_mul, eta_neg]
  · rw [one_mul, one_mul]

/-- **The one-round inequality at the level `λ > 0`**, in the units of the statement. -/
theorem stepLam {lam S V x y : ℝ} (hlam : 0 < lam) (hV : 0 ≤ V) (hSV : V = 0 → S = 0)
    (hy : |y| ≤ 1) :
    predLam lam S V x ^ 2 - 2 * predLam lam S V x * y +
        2 * log (lam + Gam ((S + x * y) / √(V + x ^ 2))) ≤
      2 * log (lam + 3 + Gam (S / √V)) := by
  rw [predLam_eq lam hV hSV]
  have h := step_sharp (lam := lam / 2) (x := x) (half_pos hlam) hV hSV hy
  have e1 : lam + Gam ((S + x * y) / √(V + x ^ 2)) =
      2 * (lam / 2 + Upper.G ((S + x * y) / √(V + x ^ 2))) := by
    rw [Gam_eq]; ring
  have e2 : lam + 3 + Gam (S / √V) = 2 * (lam / 2 + 3 / 2 + Upper.G (S / √V)) := by
    rw [Gam_eq]; ring
  have p1 : 0 < lam / 2 + Upper.G ((S + x * y) / √(V + x ^ 2)) :=
    add_pos_of_pos_of_nonneg (half_pos hlam) (Upper.G_nonneg _)
  have p2 : 0 < lam / 2 + 3 / 2 + Upper.G (S / √V) := by
    have := Upper.G_nonneg (S / √V)
    have := half_pos hlam
    linarith
  rw [e1, e2, Real.log_mul two_ne_zero p1.ne', Real.log_mul two_ne_zero p2.ne']
  linarith

/-- The prediction of `learnerLam lam` in round `n`, from the state. -/
noncomputable def yhatLam (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ :=
  predLam (lam n) (Upper.Ssum x y n) (Upper.Vsum x n) (Upper.ext x n)

theorem predictionLam_eq (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) (t : Fin T) :
    ((learnerLam lam).restrict T).prediction x y t = yhatLam lam x y t := by
  have hX : ∀ i : Fin t, x (Fin.castLE t.isLt (Fin.castSucc i)) = Upper.ext x i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [Upper.ext, hi, ↓reduceDIte]
    rfl
  have hY : ∀ i : Fin t, y (Fin.castLE t.isLt.le i) = Upper.ext y i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [Upper.ext, hi, ↓reduceDIte]
    rfl
  have hL : x (Fin.castLE t.isLt (Fin.last t)) = Upper.ext x t := by
    simp only [Upper.ext, t.isLt, ↓reduceDIte]
    rfl
  unfold Learner.prediction AnytimeLearner.restrict learnerLam yhatLam Upper.Ssum Upper.Vsum
  simp only [hX, hY, hL]
  rw [Fin.sum_univ_eq_sum_range (fun i => Upper.ext x i * Upper.ext y i) t,
    Fin.sum_univ_eq_sum_range (fun i => Upper.ext x i ^ 2) t]

/-- **The regret identity** for `learnerLam lam`: the regret is the sum of the costs plus
`ρ_T²`. -/
theorem regret_eqLam (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) :
    regret ((learnerLam lam).restrict T) x y =
      ∑ i ∈ range T, (yhatLam lam x y i ^ 2 - 2 * yhatLam lam x y i * Upper.ext y i) +
        (Upper.Ssum x y T / √(Upper.Vsum x T)) ^ 2 := by
  unfold regret learnerLoss
  have e1 : ∑ t, (((learnerLam lam).restrict T).prediction x y t - y t) ^ 2 =
      ∑ t : Fin T, (yhatLam lam x y t ^ 2 - 2 * yhatLam lam x y t * Upper.ext y t) +
        ∑ t, y t ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [predictionLam_eq, Upper.ext_val]
    ring
  rw [e1, add_sub_assoc, Upper.sum_sq_sub_bestLinearLoss, Upper.Ssum_univ, Upper.Vsum_univ,
    Fin.sum_univ_eq_sum_range
      (fun i => yhatLam lam x y i ^ 2 - 2 * yhatLam lam x y i * Upper.ext y i) T]

/-- On a play with outcomes in `[-1, 1]`, the state satisfies `V = 0 → S = 0`. -/
theorem Ssum_eq_zero_of_Vsum {T : ℕ} (x : Fin T → ℝ) {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1)
    (n : ℕ) : Upper.Vsum x n = 0 → Upper.Ssum x y n = 0 := fun h => by
  have := Upper.Ssum_sq_le x hy n
  rw [h, mul_zero] at this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))

end RegretKappa.UnknownBT
