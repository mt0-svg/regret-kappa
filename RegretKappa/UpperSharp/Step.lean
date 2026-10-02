import RegretKappa.UpperSharp.Bridge
import RegretKappa.UpperSharp.SmallSteps
import RegretKappa.UpperSharp.LargeSteps
import RegretKappa.Upper.Mixability

/-!
# Theorem 3.1 with the paper's constants: one round of the game

Proposition 3.2 of the paper with `β = 3` (`3/2` in the units of `G`): the learner's loss plus the
potential after the round is at most the potential before it. In the variables `ρ`, `b`
(`step_abstract_sharp`): for `b² ≤ 2/3` mixability (`Upper.mix_small`) and Lemma 3.10
(`small_step_sharp`, `2.8857/2 ≤ 3/2`); for `b² ≥ 2/3` the prediction `0` (`Upper.mix_large`) and
Lemma 3.11 (`large_step_sharp`, `2.7053/2 ≤ 3/2`). `step_sharp` restates it on the state `(S, V)`
and the current feature `x` (Lemma 2.3 of the paper), and `step_paper` in the units of the
statement, for the prediction `predU` and the potential `Γ`.
-/

namespace RegretKappa.UpperSharp

open Real

theorem step_abstract_sharp {lam ρ b y : ℝ} (hlam : 0 < lam) (hb : b ^ 2 ≤ 1) (hy : |y| ≤ 1) :
    Upper.eta lam (ρ * √(1 - b ^ 2)) b ^ 2 - 2 * Upper.eta lam (ρ * √(1 - b ^ 2)) b * y +
        2 * log (lam + Upper.G (ρ * √(1 - b ^ 2) + b * y)) ≤
      2 * log (lam + 3 / 2 + Upper.G ρ) := by
  have hA : 0 < lam + Upper.G (ρ * √(1 - b ^ 2) + b * y) :=
    add_pos_of_pos_of_nonneg hlam (Upper.G_nonneg _)
  have key : exp (Upper.eta lam (ρ * √(1 - b ^ 2)) b ^ 2 / 2 -
      Upper.eta lam (ρ * √(1 - b ^ 2)) b * y) * (lam + Upper.G (ρ * √(1 - b ^ 2) + b * y)) ≤
      lam + 3 / 2 + Upper.G ρ := by
    rcases le_or_gt (b ^ 2) (2 / 3) with h | h
    · have h1 := Upper.mix_small (a := ρ * √(1 - b ^ 2)) hlam hy (by linarith : b ^ 2 < 1)
      have h2 := small_step_sharp ρ h
      linarith
    · have h1 := Upper.mix_large (a := ρ * √(1 - b ^ 2)) (b := b) hlam hy
      have h2 := large_step_sharp ρ h.le hb
      linarith
  have hpos := mul_pos (exp_pos (Upper.eta lam (ρ * √(1 - b ^ 2)) b ^ 2 / 2 -
    Upper.eta lam (ρ * √(1 - b ^ 2)) b * y)) hA
  have := Real.log_le_log hpos key
  rw [Real.log_mul (exp_pos _).ne' hA.ne', Real.log_exp] at this
  linarith

theorem step_sharp {lam S V x y : ℝ} (hlam : 0 < lam) (hV : 0 ≤ V) (hSV : V = 0 → S = 0)
    (hy : |y| ≤ 1) :
    Upper.pred lam S V x ^ 2 - 2 * Upper.pred lam S V x * y +
        2 * log (lam + Upper.G ((S + x * y) / √(V + x ^ 2))) ≤
      2 * log (lam + 3 / 2 + Upper.G (S / √V)) := by
  unfold Upper.pred
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
  exact step_abstract_sharp hlam hb1 hy

/-- **Proposition 3.2** (`β = 3`) in the units of the statement: for the prediction `predU` of
round `t` and the potential `Γ`. -/
theorem step_paper {T t : ℕ} {S V x y : ℝ} (hlam : 0 < lamU T t) (hV : 0 ≤ V)
    (hSV : V = 0 → S = 0) (hy : |y| ≤ 1) :
    predU T t S V x ^ 2 - 2 * predU T t S V x * y +
        2 * log (lamU T t + Gam ((S + x * y) / √(V + x ^ 2))) ≤
      2 * log (lamU T t + beta + Gam (S / √V)) := by
  rw [predU_eq T t hV hSV]
  have h := step_sharp (lam := lamU T t / 2) (x := x) (half_pos hlam) hV hSV hy
  have e1 : lamU T t + Gam ((S + x * y) / √(V + x ^ 2)) =
      2 * (lamU T t / 2 + Upper.G ((S + x * y) / √(V + x ^ 2))) := by
    rw [Gam_eq]; ring
  have e2 : lamU T t + beta + Gam (S / √V) = 2 * (lamU T t / 2 + 3 / 2 + Upper.G (S / √V)) := by
    rw [Gam_eq, beta]; ring
  have p1 : 0 < lamU T t / 2 + Upper.G ((S + x * y) / √(V + x ^ 2)) :=
    add_pos_of_pos_of_nonneg (half_pos hlam) (Upper.G_nonneg _)
  have p2 : 0 < lamU T t / 2 + 3 / 2 + Upper.G (S / √V) := by
    have := Upper.G_nonneg (S / √V)
    have := half_pos hlam
    linarith
  rw [e1, e2, Real.log_mul two_ne_zero p1.ne', Real.log_mul two_ne_zero p2.ne']
  linarith

end RegretKappa.UpperSharp
