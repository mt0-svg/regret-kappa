import RegretKappa.LowerSharp.DriftCells
import RegretKappa.Lower.Hitting

/-!
# Sharp lower bound: the move rule and the drift

The paper, Section 4.2 (the move rule) and Lemma B.1 (drift). The move is `s(ρ) = s_j` on
`|ρ| ∈ [j/10, (j+1)/10)` for `j < 28` (the table `stab` of `DriftCells`) and
`(5/8) e^{-ρ²/2}` for `|ρ| ≥ 2.8` (`smove`); one step of the chain from `ρ` with sign `b` is
`ρ √(1 - s) + sgn b √s` (`stepS`), and `U(ρ) = 8 e^{ρ²/2}`.

`drift`: `U(ρ) + 1 ≤ (U(ρ⁺) + U(ρ⁻))/2` for every `ρ`. The average is `8 h_s(ρ)` (`avg_U_stepS`),
so the claim is `0 ≤ driftGap s ρ`; both sides are even in `ρ`; on `[0, 2.8)` it is the kernel
certificate `drift_table`, on `[2.8, ∞)` part (a) of the paper (`driftGap_large`, through
`drift_core` of `Lower/Drift.lean` and `χ(ρ) ≤ 12/25`).

The chain stopped at level `L` (`ssm`, `sst`): the move is `0` once `ρ² ≥ L`, and the state stays
put.
-/

namespace RegretKappa.LowerSharp

open Real RegretKappa.Lower

/-- The move rule of the paper. -/
noncomputable def smove (ρ : ℝ) : ℝ :=
  if |ρ| < 28 / 10 then ((stab ⌊10 * |ρ|⌋₊ : ℚ) : ℝ) else 5 / 8 * exp (-ρ ^ 2 / 2)

/-- One step of the chain with move `s` from `ρ` with sign `b`. -/
noncomputable def stepS (s ρ : ℝ) (b : Bool) : ℝ := ρ * √(1 - s) + sgn b * √s

/-- The Lyapunov function `U(ρ) = 8 e^{ρ²/2}`. -/
noncomputable def U (ρ : ℝ) : ℝ := 8 * exp (ρ ^ 2 / 2)

theorem stab_bounds {j : ℕ} (hj : j < 28) :
    0 < ((stab j : ℚ) : ℝ) ∧ ((stab j : ℚ) : ℝ) ≤ 6242 / 10000 := by
  interval_cases j <;> norm_num [stab]

theorem smove_pos (ρ : ℝ) : 0 < smove ρ := by
  unfold smove
  split_ifs with h
  · refine (stab_bounds ?_).1
    have h0 : 0 ≤ 10 * |ρ| := by positivity
    have : ((⌊10 * |ρ|⌋₊ : ℕ) : ℝ) < 28 := by
      have := Nat.floor_le h0
      linarith
    exact_mod_cast this
  · positivity

theorem smove_le (ρ : ℝ) : smove ρ ≤ 6242 / 10000 := by
  unfold smove
  split_ifs with h
  · refine (stab_bounds ?_).2
    have h0 : 0 ≤ 10 * |ρ| := by positivity
    have : ((⌊10 * |ρ|⌋₊ : ℕ) : ℝ) < 28 := by
      have := Nat.floor_le h0
      linarith
    exact_mod_cast this
  · have h2 : 784 / 100 ≤ ρ ^ 2 := by
      have := not_lt.1 h
      nlinarith [sq_abs ρ, abs_nonneg ρ]
    have h3 : ρ ^ 2 / 2 + 1 ≤ exp (ρ ^ 2 / 2) := Real.add_one_le_exp _
    have h4 : exp (-ρ ^ 2 / 2) * exp (ρ ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    nlinarith [Real.exp_pos (-ρ ^ 2 / 2)]

theorem smove_neg (ρ : ℝ) : smove (-ρ) = smove ρ := by
  simp only [smove, abs_neg, neg_sq]

theorem driftGap_neg (s ρ : ℝ) : driftGap s (-ρ) = driftGap s ρ := by
  simp only [driftGap, neg_sq, neg_mul, Real.cosh_neg]

/-- The average of `U` over the two moves is `8 h_s(ρ) = U(ρ) + 1 + driftGap s ρ`. -/
theorem avg_U_stepS {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ρ : ℝ) :
    (U (stepS s ρ true) + U (stepS s ρ false)) / 2 = U ρ + 1 + driftGap s ρ := by
  have h1 : 0 ≤ 1 - s := by linarith
  have hm : √(1 - s) * √s = √(s * (1 - s)) := by
    rw [← Real.sqrt_mul h1, mul_comm]
  set A := ρ ^ 2 * (1 - s) + s
  set B := ρ * √(s * (1 - s))
  have hp : stepS s ρ true ^ 2 = A + 2 * B := by
    simp only [stepS, sgn_true, one_mul, A, B]
    rw [← hm]
    ring_nf
    rw [Real.sq_sqrt hs0, Real.sq_sqrt h1]
    ring
  have hn : stepS s ρ false ^ 2 = A - 2 * B := by
    simp only [stepS, sgn_false, neg_one_mul, A, B]
    rw [← hm]
    ring_nf
    rw [Real.sq_sqrt hs0, Real.sq_sqrt h1]
    ring
  have hc : (exp ((A + 2 * B) / 2) + exp ((A - 2 * B) / 2)) / 2 = exp (A / 2) * cosh B := by
    rw [Real.cosh_eq, show (A + 2 * B) / 2 = A / 2 + B by ring,
      show (A - 2 * B) / 2 = A / 2 + -B by ring, Real.exp_add, Real.exp_add]
    ring
  simp only [U, driftGap, hp, hn]
  linear_combination 8 * hc

/-- `χ(ρ) = e^{-ρ²/2} (ρ²/2 + ρ⁴/4) ≤ 12/25` for `ρ ≥ 2.8` (the paper, Lemma B.1 (a)). -/
theorem chi_le {ρ : ℝ} (h : 28 / 10 ≤ ρ) :
    exp (-ρ ^ 2 / 2) * (ρ ^ 2 / 2 + ρ ^ 4 / 4) ≤ 12 / 25 := by
  set u := ρ ^ 2 / 2 with hu_def
  have hu_nonneg : 0 ≤ u := by
    rw [hu_def]
    have hsq : 0 ≤ ρ ^ 2 := pow_two_nonneg ρ
    nlinarith
  have hu_ge : 392 / 100 ≤ u := by
    rw [hu_def]
    have hρsq : (28 / 10) ^ 2 ≤ ρ ^ 2 := by
      nlinarith
    nlinarith
  have h_poly_aux : 0 ≤ 120 - 130 * u - 190 * u ^ 2 + 20 * u ^ 3 + 5 * u ^ 4 + u ^ 5 := by
    have h0 : 0 ≤ u - 392 / 100 := by nlinarith
    have h1 : 0 ≤ u ^ 2 - (392 / 100 : ℝ) * u := by nlinarith
    have h2 : 0 ≤ u ^ 3 - (392 / 100 : ℝ) * u ^ 2 := by nlinarith
    have h3 : 0 ≤ u ^ 4 - (392 / 100 : ℝ) * u ^ 3 := by nlinarith
    have h4 : 0 ≤ u ^ 5 - (392 / 100 : ℝ) * u ^ 4 := by nlinarith
    nlinarith
  have h_poly : (25 / 12 : ℝ) * (u + u ^ 2) ≤
      1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 := by
    have h := h_poly_aux
    nlinarith
  have h_sum : (25 / 12 : ℝ) * (u + u ^ 2) ≤ Real.exp u := by
    have h_partial : ∑ i ∈ Finset.range 6, u ^ i / (i.factorial : ℝ) ≤ Real.exp u :=
      Real.sum_le_exp_of_nonneg hu_nonneg 6
    have h_sum_val : (∑ i ∈ Finset.range 6, u ^ i / (i.factorial : ℝ)) =
        1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 := by
      simp [Finset.sum_range_succ]
      ring
    rw [h_sum_val] at h_partial
    nlinarith
  have h_target : Real.exp (-u) * (u + u ^ 2) ≤ 12 / 25 := by
    have hpos : 0 ≤ Real.exp (-u) := by positivity
    have h_mul : (25 / 12 : ℝ) * (Real.exp (-u) * (u + u ^ 2)) ≤ 1 := by
      calc
        (25 / 12 : ℝ) * (Real.exp (-u) * (u + u ^ 2)) =
            Real.exp (-u) * ((25 / 12 : ℝ) * (u + u ^ 2)) := by ring
        _ ≤ Real.exp (-u) * Real.exp u :=
          mul_le_mul_of_nonneg_left h_sum hpos
        _ = Real.exp ((-u) + u) := by rw [Real.exp_add]
        _ = Real.exp 0 := by ring_nf
        _ = 1 := Real.exp_zero
    nlinarith
  have h_u2 : (ρ ^ 2 / 2) ^ 2 = ρ ^ 4 / 4 := by ring
  have h_goal_eq : exp (-ρ ^ 2 / 2) * (ρ ^ 2 / 2 + ρ ^ 4 / 4) = Real.exp (-u) * (u + u ^ 2) := by
    rw [hu_def, h_u2]
    congr 1
    ring_nf
  rw [h_goal_eq]
  exact h_target

/-- Lemma B.1 (a): the drift for `ρ ≥ 2.8`. -/
theorem driftGap_large {ρ : ℝ} (h : 28 / 10 ≤ ρ) :
    0 ≤ driftGap (5 / 8 * exp (-ρ ^ 2 / 2)) ρ := by
  set s := 5 / 8 * exp (-ρ ^ 2 / 2) with hs
  have he : exp (-ρ ^ 2 / 2) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg ρ])
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by linarith
  have hcore := drift_core ρ s hs0 hs1
  have hchi := chi_le h
  have hprod : exp (ρ ^ 2 / 2) * exp (-ρ ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE : exp (ρ ^ 2 / 2) * s = 5 / 8 := by rw [hs]; linear_combination 5 / 8 * hprod
  unfold driftGap
  have key : exp (ρ ^ 2 / 2) * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) =
      exp (ρ ^ 2 / 2) + 5 / 16 - 5 / 8 * s * (ρ ^ 2 / 2 + ρ ^ 4 / 4) := by
    linear_combination (1 / 2 - s * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) * hE
  have hs' : s * (ρ ^ 2 / 2 + ρ ^ 4 / 4) ≤ 5 / 8 * (12 / 25) := by
    rw [hs, mul_assoc]
    exact mul_le_mul_of_nonneg_left hchi (by norm_num)
  nlinarith

/-- The drift inequality `0 ≤ 8 h_s(ρ) - U(ρ) - 1` at `s = s(ρ)`, for every `ρ`. -/
theorem driftGap_smove (ρ : ℝ) : 0 ≤ driftGap (smove ρ) ρ := by
  wlog hρ : 0 ≤ ρ generalizing ρ
  · have := this (-ρ) (by linarith)
    rwa [smove_neg, driftGap_neg] at this
  unfold smove
  rw [abs_of_nonneg hρ]
  split_ifs with h
  · exact drift_table ρ hρ h
  · exact driftGap_large (not_lt.1 h)

/-- **Lemma B.1 (drift).** -/
theorem drift (ρ : ℝ) :
    U ρ + 1 ≤ (U (stepS (smove ρ) ρ true) + U (stepS (smove ρ) ρ false)) / 2 := by
  rw [avg_U_stepS (smove_pos ρ).le (by linarith [smove_le ρ])]
  linarith [driftGap_smove ρ]

/-- The move stopped at level `L`. -/
noncomputable def ssm (L ρ : ℝ) : ℝ := if ρ ^ 2 < L then smove ρ else 0

/-- One step of the chain stopped at level `L`. -/
noncomputable def sst (L ρ : ℝ) (b : Bool) : ℝ := stepS (ssm L ρ) ρ b

theorem ssm_nonneg (L ρ : ℝ) : 0 ≤ ssm L ρ := by
  unfold ssm; split_ifs
  · exact (smove_pos ρ).le
  · exact le_rfl

theorem ssm_le (L ρ : ℝ) : ssm L ρ ≤ 6242 / 10000 := by
  unfold ssm; split_ifs
  · exact smove_le ρ
  · norm_num

theorem ssm_lt_one (L ρ : ℝ) : ssm L ρ < 1 := by linarith [ssm_le L ρ]

theorem sst_of_lt {L ρ : ℝ} (h : ρ ^ 2 < L) (b : Bool) : sst L ρ b = stepS (smove ρ) ρ b := by
  simp [sst, ssm, h]

theorem sst_of_le {L ρ : ℝ} (h : L ≤ ρ ^ 2) (b : Bool) : sst L ρ b = ρ := by
  simp [sst, ssm, not_lt.2 h, stepS]

end RegretKappa.LowerSharp
