import RegretKappa.Upper.Mixability
import RegretKappa.Upper.SmallSteps
import RegretKappa.Upper.LargeSteps

/-!
# Upper bound: one round of the game

Proposition 3.2 of the paper with `β = 60`: in the variables `ρ`, `b` (`b² = s`) the
learner's loss plus the potential after the round is at most the potential before it
(`step_abstract`); `step` restates it on the state `(S, V)` and the current feature `x`, where
`ρ = S/√V`, `b = x/√(V + x²)`, `ρ √(1 - b²) = S/√(V + x²)`, including the empty state `V = 0`
and the feature `x = 0` (Lemma 2.3 of the paper).
-/

namespace RegretKappa.Upper

open Real

theorem step_abstract {lam ρ b y : ℝ} (hlam : 0 < lam) (hb : b ^ 2 ≤ 1) (hy : |y| ≤ 1) :
    eta lam (ρ * √(1 - b ^ 2)) b ^ 2 - 2 * eta lam (ρ * √(1 - b ^ 2)) b * y +
        2 * log (lam + G (ρ * √(1 - b ^ 2) + b * y)) ≤ 2 * log (lam + beta + G ρ) := by
  have hA : 0 < lam + G (ρ * √(1 - b ^ 2) + b * y) := add_pos_of_pos_of_nonneg hlam (G_nonneg _)
  have key : exp (eta lam (ρ * √(1 - b ^ 2)) b ^ 2 / 2 - eta lam (ρ * √(1 - b ^ 2)) b * y) *
      (lam + G (ρ * √(1 - b ^ 2) + b * y)) ≤ lam + beta + G ρ := by
    rcases le_or_gt (b ^ 2) (3 / 4) with h | h
    · have h1 := mix_small (a := ρ * √(1 - b ^ 2)) hlam hy (by linarith : b ^ 2 < 1)
      have h2 := small_step ρ h
      unfold beta
      linarith
    · have h1 := mix_large (a := ρ * √(1 - b ^ 2)) (b := b) hlam hy
      have h2 := large_step ρ h.le hb
      have h3 := G_two_le
      unfold beta
      linarith
  have hpos := mul_pos (exp_pos (eta lam (ρ * √(1 - b ^ 2)) b ^ 2 / 2 - eta lam (ρ * √(1 - b ^ 2)) b * y)) hA
  have := Real.log_le_log hpos key
  rw [Real.log_mul (exp_pos _).ne' hA.ne', Real.log_exp] at this
  linarith

theorem step {lam S V x y : ℝ} (hlam : 0 < lam) (hV : 0 ≤ V) (hSV : V = 0 → S = 0) (hy : |y| ≤ 1) :
    pred lam S V x ^ 2 - 2 * pred lam S V x * y + 2 * log (lam + G ((S + x * y) / √(V + x ^ 2))) ≤
      2 * log (lam + beta + G (S / √V)) := by
  unfold pred
  have hD0 : 0 ≤ V + x ^ 2 := by positivity
  have hb2 : (x / √(V + x ^ 2)) ^ 2 = x ^ 2 / (V + x ^ 2) := by rw [div_pow, Real.sq_sqrt hD0]
  have hb1 : (x / √(V + x ^ 2)) ^ 2 ≤ 1 := by
    rw [hb2]
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h, div_zero]
      norm_num
    · rw [div_le_one h]
      linarith
  have ha : S / √(V + x ^ 2) = S / √V * √(1 - (x / √(V + x ^ 2)) ^ 2) := by
    rcases eq_or_lt_of_le hV with h | h
    · rw [hSV h.symm]
      simp
    · have hDpos : 0 < V + x ^ 2 := by positivity
      have h1 : 1 - (x / √(V + x ^ 2)) ^ 2 = V / (V + x ^ 2) := by
        rw [hb2]
        field_simp
        ring
      have h2 : 0 < √V := Real.sqrt_pos.2 h
      have h3 : 0 < √(V + x ^ 2) := Real.sqrt_pos.2 hDpos
      rw [h1, Real.sqrt_div h.le]
      field_simp
  have hρ' : (S + x * y) / √(V + x ^ 2) =
      S / √V * √(1 - (x / √(V + x ^ 2)) ^ 2) + x / √(V + x ^ 2) * y := by
    rw [add_div, ← ha]
    ring
  rw [hρ', ha]
  exact step_abstract hlam hb1 hy

end RegretKappa.Upper
