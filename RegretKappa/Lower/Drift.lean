import RegretKappa.Lower.Basic

/-!
# Lower bound: the move rule of phase 1 and its drift

Phase 1 moves the self-normalized statistic `ρ = S / √V` as the chain of the paper,
Lemma 4.2: from `ρ` to `ρ √(1 - s) ± √s` with probability `1/2` each, `s = s(ρ)` the share of the
next feature in the new `V`.

Departure from the paper (simpler, constants only): the move rule is `s(ρ) = e^{-ρ²/2} / 4` for every
`ρ` (the paper uses a table of 28 rational values below `2.8` and `(5/8) e^{-ρ²/2}` above) and the
Lyapunov function is `g(ρ) = 16 e^{ρ²/2}` (the paper's is `8 e^{ρ²/2}`). With these the drift
inequality `g(ρ) + 1 ≤ (g(ρ₊) + g(ρ₋)) / 2` holds for every `ρ` by the argument of part (a) of
Lemma B.1 of the paper alone, with no rational certificate:
`e^{-z} cosh x ≥ (1 - z)(1 + x²/2) ≥ 1 + s/2 - s² (ρ²/2 + ρ⁴/4)` (`drift_core`), and
`e^{-ρ²/2} (ρ²/2 + ρ⁴/4) ≤ 1` (`add_sq_le_exp`), so the drift is at least `2 - 1`. The constant `16`
costs a constant in the level reached, which the asymptotic target does not see.

Also `step_sq_le`: one step raises `ρ²` by at most `1` (Cauchy-Schwarz), which bounds the
overshoot at the hitting time (the paper's Lemma B.3 is sharper).
-/

namespace RegretKappa.Lower

open Real

/-- The move rule: `s(ρ) = e^{-ρ²/2} / 4`. -/
noncomputable def mv (ρ : ℝ) : ℝ := exp (-ρ ^ 2 / 2) / 4

/-- One step of the phase-1 chain with sign `b`. -/
noncomputable def step (ρ : ℝ) (b : Bool) : ℝ := ρ * √(1 - mv ρ) + sgn b * √(mv ρ)

/-- The Lyapunov function `g(ρ) = 16 e^{ρ²/2}`. -/
noncomputable def lyap (ρ : ℝ) : ℝ := 16 * exp (ρ ^ 2 / 2)

theorem mv_pos (ρ : ℝ) : 0 < mv ρ := by
  unfold mv
  positivity

theorem mv_le (ρ : ℝ) : mv ρ ≤ 1 / 4 := by
  unfold mv
  have : exp (-ρ ^ 2 / 2) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg ρ])
  linarith

theorem lyap_pos (ρ : ℝ) : 0 < lyap ρ := by
  unfold lyap
  positivity

/-- `lyap` is monotone in `ρ²`. -/
theorem lyap_le_of_sq_le {ρ ρ' : ℝ} (h : ρ ^ 2 ≤ ρ' ^ 2) : lyap ρ ≤ lyap ρ' := by
  unfold lyap
  gcongr

/-- The square of a step. -/
theorem step_sq (ρ : ℝ) (b : Bool) :
    step ρ b ^ 2 = ρ ^ 2 * (1 - mv ρ) + mv ρ + 2 * sgn b * (ρ * √(mv ρ * (1 - mv ρ))) := by
  have h0 := (mv_pos ρ).le
  have h1 : 0 ≤ 1 - mv ρ := by linarith [mv_le ρ]
  unfold step
  rw [Real.sqrt_mul h0, add_sq, mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h0, sgn_sq]
  ring

-- TARGET

/-- One step raises `ρ²` by at most `1`. -/
theorem step_sq_le (ρ : ℝ) (b : Bool) : step ρ b ^ 2 ≤ ρ ^ 2 + 1 := by
  unfold step
  let s := mv ρ
  have hs_pos : 0 < s := mv_pos ρ
  have hs_le_one : s ≤ 1 := by
    have hexp : exp (-ρ ^ 2 / 2) ≤ 1 := by
      have h_nonpos : -ρ ^ 2 / 2 ≤ 0 := by
        nlinarith [sq_nonneg ρ]
      have := Real.exp_le_exp_of_le h_nonpos
      simpa [Real.exp_zero] using this
    unfold s mv
    nlinarith
  have h_sq_sqrt_s : (√s) ^ 2 = s := Real.sq_sqrt hs_pos.le
  have h_sq_sqrt_1ms : (√(1 - s)) ^ 2 = 1 - s := Real.sq_sqrt (by nlinarith)
  have h_sgn_sq : (sgn b) ^ 2 = 1 := sgn_sq b
  have h_cauchy : (ρ * √(1 - s) + sgn b * √s) ^ 2 ≤ (ρ ^ 2 + (sgn b) ^ 2) * ((√(1 - s)) ^ 2 + (√s) ^ 2) := by
    have h_nonneg : 0 ≤ (ρ * √s - sgn b * √(1 - s)) ^ 2 := sq_nonneg _
    nlinarith
  calc
    (ρ * √(1 - s) + sgn b * √s) ^ 2 ≤ (ρ ^ 2 + (sgn b) ^ 2) * ((√(1 - s)) ^ 2 + (√s) ^ 2) := h_cauchy
    _ = (ρ ^ 2 + 1) * ((1 - s) + s) := by rw [h_sgn_sq, h_sq_sqrt_1ms, h_sq_sqrt_s]
    _ = (ρ ^ 2 + 1) * 1 := by ring
    _ = ρ ^ 2 + 1 := by ring

theorem one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ cosh x := by
  have h2 : cosh x = 2 * sinh (x / 2) ^ 2 + 1 := by
    rw [show x = 2 * (x / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
    ring_nf
  have h3 : (x / 2) ^ 2 ≤ sinh (x / 2) ^ 2 := by
    rcases le_total 0 (x / 2) with h | h
    · have := Real.self_le_sinh_iff.2 h
      nlinarith
    · have := Real.sinh_le_self_iff.2 h
      nlinarith
  rw [h2]
  nlinarith

/-- `u + u² ≤ e^u` for `u ≥ 0`. -/
theorem add_sq_le_exp {u : ℝ} (hu : 0 ≤ u) : u + u ^ 2 ≤ exp u := by
  have hsum := Real.sum_le_exp_of_nonneg hu 4
  have hsum_eq : (∑ i ∈ Finset.range 4, u ^ i / (i.factorial : ℝ)) = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum_eq] at hsum
  have hineq : u + u ^ 2 ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by
    nlinarith [sq_nonneg (u - 2)]
  linarith

/-- The average of `e^{ρ'²/2}` over the two moves. -/
theorem avg_exp_step (ρ : ℝ) :
    (exp (step ρ true ^ 2 / 2) + exp (step ρ false ^ 2 / 2)) / 2 =
      exp ((ρ ^ 2 * (1 - mv ρ) + mv ρ) / 2) * cosh (ρ * √(mv ρ * (1 - mv ρ))) := by
  have hs_pos : 0 < mv ρ := mv_pos ρ
  have hs_nonneg : 0 ≤ mv ρ := by linarith
  have h_exp_le_one : exp (-ρ ^ 2 / 2) ≤ 1 := by
    have h_nonpos : -ρ ^ 2 / 2 ≤ 0 := by
      nlinarith [sq_nonneg ρ]
    exact calc
      exp (-ρ ^ 2 / 2) ≤ exp (0 : ℝ) := (Real.exp_le_exp.mpr h_nonpos)
      _ = 1 := Real.exp_zero
  have hs_le_one : mv ρ ≤ 1 := by
    dsimp [mv]
    nlinarith
  have h1m_nonneg : 0 ≤ 1 - mv ρ := by linarith
  have h_sqrt_mul : √(1 - mv ρ) * √(mv ρ) = √(mv ρ * (1 - mv ρ)) := by
    calc
      √(1 - mv ρ) * √(mv ρ) = √((1 - mv ρ) * (mv ρ)) := by rw [Real.sqrt_mul h1m_nonneg (mv ρ)]
      _ = √(mv ρ * (1 - mv ρ)) := by rw [mul_comm]
  set A := ρ ^ 2 * (1 - mv ρ) + mv ρ with hA
  set B := ρ * √(mv ρ * (1 - mv ρ)) with hB
  have hstep_true_sq : step ρ true ^ 2 = A + 2 * B := by
    dsimp [step, sgn, A, B]
    simp
    calc
      (ρ * √(1 - mv ρ) + √(mv ρ)) ^ 2
          = (ρ * √(1 - mv ρ)) ^ 2 + (√(mv ρ)) ^ 2 + 2 * (ρ * √(1 - mv ρ)) * √(mv ρ) := by ring
      _ = ρ ^ 2 * (√(1 - mv ρ)) ^ 2 + mv ρ + 2 * ρ * (√(1 - mv ρ) * √(mv ρ)) := by
        rw [Real.sq_sqrt hs_nonneg]
        ring
      _ = ρ ^ 2 * (1 - mv ρ) + mv ρ + 2 * ρ * (√(1 - mv ρ) * √(mv ρ)) := by
        rw [Real.sq_sqrt h1m_nonneg]
      _ = ρ ^ 2 * (1 - mv ρ) + mv ρ + 2 * ρ * √(mv ρ * (1 - mv ρ)) := by
        rw [h_sqrt_mul]
      _ = (ρ ^ 2 * (1 - mv ρ) + mv ρ) + 2 * (ρ * √(mv ρ * (1 - mv ρ))) := by ring
  have hstep_false_sq : step ρ false ^ 2 = A - 2 * B := by
    dsimp [step, sgn, A, B]
    calc
      (ρ * √(1 - mv ρ) + (-1) * √(mv ρ)) ^ 2
          = (ρ * √(1 - mv ρ) - √(mv ρ)) ^ 2 := by ring
      _ = (ρ * √(1 - mv ρ)) ^ 2 + (√(mv ρ)) ^ 2 - 2 * (ρ * √(1 - mv ρ)) * √(mv ρ) := by ring
      _ = ρ ^ 2 * (√(1 - mv ρ)) ^ 2 + mv ρ - 2 * ρ * (√(1 - mv ρ) * √(mv ρ)) := by
        rw [Real.sq_sqrt hs_nonneg]
        ring
      _ = ρ ^ 2 * (1 - mv ρ) + mv ρ - 2 * ρ * (√(1 - mv ρ) * √(mv ρ)) := by
        rw [Real.sq_sqrt h1m_nonneg]
      _ = ρ ^ 2 * (1 - mv ρ) + mv ρ - 2 * ρ * √(mv ρ * (1 - mv ρ)) := by
        rw [h_sqrt_mul]
      _ = (ρ ^ 2 * (1 - mv ρ) + mv ρ) - 2 * (ρ * √(mv ρ * (1 - mv ρ))) := by ring
  calc
    (exp (step ρ true ^ 2 / 2) + exp (step ρ false ^ 2 / 2)) / 2
        = (exp ((A + 2 * B) / 2) + exp ((A - 2 * B) / 2)) / 2 := by
          rw [hstep_true_sq, hstep_false_sq]
    _ = (exp (A / 2 + B) + exp (A / 2 - B)) / 2 := by ring_nf
    _ = (exp (A / 2) * exp B + exp (A / 2) * exp (-B)) / 2 := by
      rw [Real.exp_add (A / 2) B, show exp (A / 2 - B) = exp (A / 2) * exp (-B) by
        rw [sub_eq_add_neg, Real.exp_add]]
    _ = exp (A / 2) * ((exp B + exp (-B)) / 2) := by ring
    _ = exp (A / 2) * Real.cosh B := by rw [Real.cosh_eq]
    _ = exp ((ρ ^ 2 * (1 - mv ρ) + mv ρ) / 2) * cosh (ρ * √(mv ρ * (1 - mv ρ))) := by
      dsimp [A, B]

-- Helper lemma: sinh² t ≥ t² for all real t
lemma sinh_sq_ge_sq (t : ℝ) : t ^ 2 ≤ Real.sinh t ^ 2 := by
  by_cases h : 0 ≤ t
  · have hle : t ≤ Real.sinh t := by
      rw [Real.self_le_sinh_iff]
      exact h
    nlinarith
  · have hle : Real.sinh t ≤ t := by
      rw [Real.sinh_le_self_iff]
      linarith
    nlinarith

-- Helper lemma: cosh x ≥ 1 + x²/2 for all real x
lemma cosh_ge_one_plus_half_sq (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hcosh : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    calc
      Real.cosh x = Real.cosh (2 * (x / 2)) := by ring_nf
      _ = Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 := Real.cosh_two_mul (x / 2)
      _ = (1 + Real.sinh (x / 2) ^ 2) + Real.sinh (x / 2) ^ 2 := by rw [Real.cosh_sq']
      _ = 1 + 2 * Real.sinh (x / 2) ^ 2 := by ring
  rw [hcosh]
  have hsq : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := sinh_sq_ge_sq (x / 2)
  nlinarith

/-- The core inequality of the drift, for any move `s ∈ [0, 1]`. -/
theorem drift_core (ρ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    exp (ρ ^ 2 / 2) * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) ≤
      exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) := by
  have hA_pos : 0 < exp (ρ ^ 2 / 2) := Real.exp_pos (ρ ^ 2 / 2)
  set z := s * (ρ ^ 2 - 1) / 2 with hz
  set x := ρ * √(s * (1 - s)) with hx
  have hx_sq : x ^ 2 = ρ ^ 2 * s * (1 - s) := by
    rw [hx]
    calc
      (ρ * √(s * (1 - s))) ^ 2 = ρ ^ 2 * (√(s * (1 - s))) ^ 2 := by ring
      _ = ρ ^ 2 * (s * (1 - s)) := by rw [Real.sq_sqrt (by nlinarith)]
      _ = ρ ^ 2 * s * (1 - s) := by ring
  have h_exp_eq : exp ((ρ ^ 2 * (1 - s) + s) / 2) = exp (ρ ^ 2 / 2) * exp (-z) := by
    calc
      exp ((ρ ^ 2 * (1 - s) + s) / 2) = exp (ρ ^ 2 / 2 - s * (ρ ^ 2 - 1) / 2) := by ring_nf
      _ = exp (ρ ^ 2 / 2 - z) := by rw [hz]
      _ = exp (ρ ^ 2 / 2) * exp (-z) := by rw [Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
  rw [h_exp_eq, hx]
  -- Goal: A*(1 + s/2 - s²*(ρ²/2 + ρ⁴/4)) ≤ A*exp(-z)*cosh(x) where A = exp(ρ²/2) > 0
  -- Since A > 0, it suffices to show: 1 + s/2 - s²*(ρ²/2 + ρ⁴/4) ≤ exp(-z)*cosh(x)
  -- Key algebraic identity: (1 - z)*(1 + x²/2) - (1 + s/2 - s²*(ρ²/2 + ρ⁴/4)) = s²*ρ²/4 * (1 + s*(ρ²-1))
  have h_algebra : 1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4) ≤ (1 - z) * (1 + x ^ 2 / 2) := by
    rw [hz, hx_sq]
    -- Show: (1 - s*(ρ²-1)/2)*(1 + ρ²*s*(1-s)/2) - (1 + s/2 - s²*(ρ²/2 + ρ⁴/4)) ≥ 0
    -- The difference equals s²*ρ²/4 * (1 + s*(ρ²-1))
    have h_diff : (1 - s * (ρ ^ 2 - 1) / 2) * (1 + ρ ^ 2 * s * (1 - s) / 2) -
        (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) =
        s ^ 2 * ρ ^ 2 / 4 * (1 + s * (ρ ^ 2 - 1)) := by
      ring
    have h_nonneg : 0 ≤ s ^ 2 * ρ ^ 2 / 4 * (1 + s * (ρ ^ 2 - 1)) := by
      by_cases hρ : ρ ^ 2 ≥ 1
      · have : 0 ≤ 1 + s * (ρ ^ 2 - 1) := by nlinarith
        positivity
      · have hρ' : ρ ^ 2 ≤ 1 := by linarith
        have h_lower : -1 ≤ s * (ρ ^ 2 - 1) := by
          -- Since s ≤ 1 and ρ²-1 ≥ -1 (because ρ² ≥ 0), we have s*(ρ²-1) ≥ 1*(ρ²-1) = ρ²-1 ≥ -1
          nlinarith
        have : 0 ≤ 1 + s * (ρ ^ 2 - 1) := by nlinarith
        positivity
    linarith
  by_cases hz_one : 1 - z ≥ 0
  · -- Case 1: 1 - z ≥ 0, then exp(-z) ≥ 1 - z and cosh(x) ≥ 1 + x²/2
    have h_exp_ineq : 1 - z ≤ exp (-z) := by
      have h := Real.add_one_le_exp (-z)
      linarith
    have h_cosh_ineq : 1 + x ^ 2 / 2 ≤ Real.cosh x := cosh_ge_one_plus_half_sq x
    have h_nonneg_cosh : 0 ≤ Real.cosh x := by linarith [Real.cosh_pos x]
    have h_mul : (1 - z) * (1 + x ^ 2 / 2) ≤ exp (-z) * Real.cosh x := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h_mul (by positivity : 0 ≤ exp (ρ ^ 2 / 2))]
  · -- Case 2: 1 - z < 0, then (1 - z)(1 + x²/2) < 0 < exp(-z)*cosh(x)
    -- But we also have the algebraic inequality: LHS ≤ (1 - z)(1 + x²/2) < 0
    -- So LHS < 0 < exp(-z)*cosh(x)
    have h_neg : (1 - z) * (1 + x ^ 2 / 2) < 0 := by
      have h_pos : 0 < 1 + x ^ 2 / 2 := by nlinarith
      nlinarith
    have hL_neg : 1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4) < 0 := by
      linarith
    have hLHS_neg : exp (ρ ^ 2 / 2) * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) < 0 := by
      nlinarith
    have hRHS_pos : 0 < exp (ρ ^ 2 / 2) * exp (-z) * Real.cosh (ρ * √(s * (1 - s))) := by
      positivity
    linarith

-- TARGET

/-- **Drift** (the paper, Lemma B.1, with the move rule and `g` of this file). -/
theorem drift (ρ : ℝ) : lyap ρ + 1 ≤ (lyap (step ρ true) + lyap (step ρ false)) / 2 := by
  set s := mv ρ with hs
  have hs_pos : 0 ≤ s := (mv_pos ρ).le
  have hs_le_one : s ≤ 1 := by
    have h := mv_le ρ
    linarith
  have h_avg_exp : (exp (step ρ true ^ 2 / 2) + exp (step ρ false ^ 2 / 2)) / 2 =
      exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) := by
    rw [hs]
    exact avg_exp_step ρ
  have h_lyap_eq : (lyap (step ρ true) + lyap (step ρ false)) / 2 =
      16 * exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) := by
    unfold lyap
    calc
      (16 * exp (step ρ true ^ 2 / 2) + 16 * exp (step ρ false ^ 2 / 2)) / 2
          = 16 * ((exp (step ρ true ^ 2 / 2) + exp (step ρ false ^ 2 / 2)) / 2) := by ring
      _ = 16 * (exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s)))) := by rw [h_avg_exp]
      _ = 16 * exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) := by ring
  have h_drift_core : exp (ρ ^ 2 / 2) * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) ≤
      exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) :=
    drift_core ρ s hs_pos hs_le_one
  have h_main : 16 * exp (ρ ^ 2 / 2) + 1 ≤
      16 * exp (ρ ^ 2 / 2) * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) := by
    set E := exp (ρ ^ 2 / 2) with hE
    have h_Es : E * s = 1/4 := by
      rw [hE, hs, mv]
      have h_arg : ρ ^ 2 / 2 + (-ρ ^ 2 / 2) = 0 := by
        calc
          ρ ^ 2 / 2 + (-ρ ^ 2 / 2) = ρ ^ 2 / 2 + (-(ρ ^ 2 / 2)) := by simp [neg_div]
          _ = 0 := by ring
      calc
        exp (ρ ^ 2 / 2) * (exp (-ρ ^ 2 / 2) / 4) = (exp (ρ ^ 2 / 2) * exp (-ρ ^ 2 / 2)) / 4 := by ring
        _ = exp (ρ ^ 2 / 2 + (-ρ ^ 2 / 2)) / 4 := by rw [Real.exp_add]
        _ = exp 0 / 4 := by rw [h_arg]
        _ = 1/4 := by norm_num
    have h_Esq : E * s ^ 2 = Real.exp (-(ρ ^ 2 / 2)) / 16 := by
      rw [hE, hs, mv]
      have h_arg : ρ ^ 2 / 2 + (-ρ ^ 2 / 2) = 0 := by
        calc
          ρ ^ 2 / 2 + (-ρ ^ 2 / 2) = ρ ^ 2 / 2 + (-(ρ ^ 2 / 2)) := by simp [neg_div]
          _ = 0 := by ring
      calc
        exp (ρ ^ 2 / 2) * (exp (-ρ ^ 2 / 2) / 4) ^ 2 = exp (ρ ^ 2 / 2) * (exp (-ρ ^ 2 / 2) ^ 2 / 16) := by ring
        _ = (exp (ρ ^ 2 / 2) * exp (-ρ ^ 2 / 2) ^ 2) / 16 := by ring
        _ = (exp (ρ ^ 2 / 2) * exp (-ρ ^ 2 / 2) * exp (-ρ ^ 2 / 2)) / 16 := by ring
        _ = ((exp (ρ ^ 2 / 2) * exp (-ρ ^ 2 / 2)) * exp (-ρ ^ 2 / 2)) / 16 := by ring
        _ = (exp (ρ ^ 2 / 2 + (-ρ ^ 2 / 2)) * exp (-ρ ^ 2 / 2)) / 16 := by rw [Real.exp_add]
        _ = (exp 0 * exp (-ρ ^ 2 / 2)) / 16 := by rw [h_arg]
        _ = exp (-ρ ^ 2 / 2) / 16 := by rw [Real.exp_zero, one_mul]
        _ = Real.exp (-(ρ ^ 2 / 2)) / 16 := by
          simp [neg_div]
    have h_exp_ineq : Real.exp (-(ρ ^ 2 / 2)) * (ρ ^ 2 / 2 + ρ ^ 4 / 4) ≤ 1 := by
      have hu_nonneg : 0 ≤ ρ ^ 2 / 2 := by nlinarith [sq_nonneg ρ]
      have h_add_sq : (ρ ^ 2 / 2) + (ρ ^ 2 / 2) ^ 2 ≤ Real.exp (ρ ^ 2 / 2) :=
        add_sq_le_exp hu_nonneg
      have h_sq_eq : (ρ ^ 2 / 2) ^ 2 = ρ ^ 4 / 4 := by ring
      rw [h_sq_eq] at h_add_sq
      have h_arg : (-(ρ ^ 2 / 2)) + (ρ ^ 2 / 2) = 0 := by ring
      calc
        Real.exp (-(ρ ^ 2 / 2)) * (ρ ^ 2 / 2 + ρ ^ 4 / 4) ≤
            Real.exp (-(ρ ^ 2 / 2)) * Real.exp (ρ ^ 2 / 2) := by
          nlinarith [Real.exp_pos (-(ρ ^ 2 / 2))]
        _ = Real.exp ((-(ρ ^ 2 / 2)) + (ρ ^ 2 / 2)) := by rw [Real.exp_add]
        _ = Real.exp 0 := by rw [h_arg]
        _ = 1 := Real.exp_zero
    have h_diff_eq : 16 * E * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) - (16 * E + 1) =
        1 - Real.exp (-(ρ ^ 2 / 2)) * (ρ ^ 2 / 2 + ρ ^ 4 / 4) := by
      calc
        16 * E * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) - (16 * E + 1)
            = (16 * E + 8 * (E * s) - 16 * (E * s ^ 2) * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) - (16 * E + 1) := by ring
        _ = (16 * E + 8 * (1/4) - 16 * (Real.exp (-(ρ ^ 2 / 2)) / 16) * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) -
            (16 * E + 1) := by rw [h_Es, h_Esq]
        _ = (16 * E + 2 - Real.exp (-(ρ ^ 2 / 2)) * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) - (16 * E + 1) := by ring
        _ = 1 - Real.exp (-(ρ ^ 2 / 2)) * (ρ ^ 2 / 2 + ρ ^ 4 / 4) := by ring
    have h_diff_nonneg : 0 ≤ 16 * E * (1 + s / 2 - s ^ 2 * (ρ ^ 2 / 2 + ρ ^ 4 / 4)) - (16 * E + 1) := by
      rw [h_diff_eq]
      linarith [h_exp_ineq]
    linarith
  have h_bound : lyap ρ + 1 ≤ 16 * exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) := by
    unfold lyap
    nlinarith
  linarith

end RegretKappa.Lower
