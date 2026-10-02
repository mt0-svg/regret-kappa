import RegretKappa.UnknownBT.UnknownB.Learner
import RegretKappa.UnknownBT.Anytime.ScheduleB

/-!
# The scale-free bound (B and T unknown)

The constant `KB` of the surprise round is at most `10.38` (`KB_le`): `kappaB ≤ 3.4426` from
`log 2 < 0.6931471808`
and the enclosures of `e^{-1/2}` and `K0` of regret-kappa, and `lipB = 4 Dg(1)/e^{-1/2} ≤ 5.9365`
from the first four terms of the series of `Dg(1)` and the coefficient bound of regret-kappa for
the rest (`Dg_one_le`). With the anytime schedule of `TheoremB` (`isSchedule_B`, `LT_le_num`),
the running-maximum bound `regret_le` gives `ScaleFreeBound 12` (`scaleFreeBound_twelve`):
`Regret_T ≤ M_T² (3 log T + 4 log log(T + 2) + 12 + 2/√T + 4/T)` for every `T ≥ 1` and every play.
-/

namespace RegretKappa.UnknownBT.UB

open Real RegretKappa RegretKappa.UpperSharp

theorem Dg_one_le : Dg 1 ≤ (exp (-1 / 2) + 2 * K0) / 2 + 5 * exp (-1 / 2) / 12 +
    19 * exp (-1 / 2) / 240 + exp (-1 / 2) / 96 + (exp 1 - 65 / 24) := by
  set f : ℕ → ℝ := fun n => ((n : ℝ) + 1) * (1 : ℝ) ^ n / ((2 * n + 2).factorial : ℝ) * Mw (n + 1)
    with hf
  have hD : HasSum f (Dg 1) := Dg_hasSum one_pos
  have hT : HasSum (fun n => f (n + 4)) (Dg 1 - ∑ i ∈ Finset.range 4, f i) :=
    (hasSum_nat_add_iff' 4).2 hD
  have hE : HasSum (fun n : ℕ => (1 : ℝ) ^ n / (n.factorial : ℝ)) (exp 1) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  have hE5 : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 5).factorial : ℝ))
      (exp 1 - ∑ i ∈ Finset.range 5, (1 : ℝ) ^ i / (i.factorial : ℝ)) := by
    have := (hasSum_nat_add_iff' 5).2 hE
    simpa using this
  have hle : Dg 1 - ∑ i ∈ Finset.range 4, f i ≤
      exp 1 - ∑ i ∈ Finset.range 5, (1 : ℝ) ^ i / (i.factorial : ℝ) := by
    refine hasSum_le (fun n => ?_) hT hE5
    have hc := coeff_le (n + 4)
    simp only [hf, one_pow, mul_one]
    push_cast at hc ⊢
    calc ((n : ℝ) + 4 + 1) / ((2 * (n + 4) + 2).factorial : ℝ) * Mw (n + 4 + 1)
        = ((n : ℝ) + 4 + 1) * Mw (n + 4 + 1) / ((2 * (n + 4) + 2).factorial : ℝ) := by ring
      _ ≤ 1 / ((n + 4 + 1).factorial : ℝ) := hc
      _ = 1 / ((n + 5).factorial : ℝ) := rfl
  have hM2 : Mw 2 = 5 * exp (-1 / 2) := by
    rw [Mw_eq_GamC (by norm_num)]; simp [GamC, kk]; ring
  have hM3 : Mw 3 = 19 * exp (-1 / 2) := by
    rw [Mw_eq_GamC (by norm_num)]; simp [GamC, kk]; ring
  have hM4 : Mw 4 = 105 * exp (-1 / 2) := by
    rw [Mw_eq_GamC (by norm_num)]; simp [GamC, kk]; ring
  have h1 : Mw 1 = exp (-1 / 2) + 2 * K0 := by rw [Mw_one, mom_one]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf] at hle
  norm_num [Nat.factorial, h1, hM2, hM3, hM4] at hle
  linarith

theorem kappaB_le : kappaB ≤ 3.4426 := by
  have hE := exp_neg_half_bounds
  have hK := K0_le
  have hK0 := K0_nonneg
  have hl2 := Real.log_two_lt_d9
  have he : 0 < exp (-1 / 2 : ℝ) := exp_pos _
  set x := (exp (-1 / 2) + 2 * K0) / exp (-1 / 2) with hx
  have hxpos : 0 < x := div_pos (by linarith) he
  have hxle : x ≤ 1.92292 := by
    rw [hx, div_le_iff₀ he]; nlinarith
  have hlog : log x ≤ log 2 + (x / 2 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / 2 by positivity)
    rw [Real.log_div hxpos.ne' two_ne_zero] at h
    linarith
  unfold kappaB
  rw [← hx]
  norm_num at hlog hxle ⊢
  linarith

theorem lipB_le : lipB ≤ 5.9365 := by
  have hE := exp_neg_half_bounds
  have hK := K0_le
  have he1 := Real.exp_one_lt_d9
  have he : 0 < exp (-1 / 2 : ℝ) := exp_pos _
  have hD := Dg_one_le
  unfold lipB
  rw [div_le_iff₀ he]
  linarith

theorem KB_le : KB ≤ 10.38 := by
  unfold KB
  linarith [kappaB_le, lipB_le]

/-- **B and T unknown**: `ScaleFreeBound 12`. -/
theorem scaleFreeBound_twelve : ScaleFreeBound 12 := by
  intro T hT x y
  rw [learnerBT_eq]
  have h := regret_le isSchedule_B x y
    (3 * log T + 4 * log (log (T + 2)) + 1.3706 + 2 / √(T : ℝ) + 4 / T)
    (fun w hw => LT_le_num hT hw)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  linarith [KB_le]

end RegretKappa.UnknownBT.UB
