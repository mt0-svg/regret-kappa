import Mathlib

/-!
# The checker of the drift certificate

The paper, Lemma B.1 (b): on a cell `[j/10, (j+1)/10)` of `[0, 2.8)` the step `s = s_j` is a
constant rational number, and on a subinterval `[ℓ, ℓ']` the drift `8 h_s(ρ) - 8 e^{ρ²/2} - 1`
is at least the rational number `certQ N ℓ ℓ' s`, built from the partial sums `e_N`, `ch_N` and
the upper bound `ē_N` of the exponential. `check` runs over a bisection tree of a cell, encoded as
a natural number (preorder bits from the least significant one: `1` splits the interval at its
midpoint, `0` is a leaf where `certQ` must be nonnegative), and `check_sound` turns a successful
check into the inequality on the whole cell. The cells themselves are in
`RegretKappa/LowerSharp/DriftCells.lean`.
-/

namespace RegretKappa.LowerSharp

open Real Finset

/-- Horner for the exponential: `expAux q k acc = Σ_{n<k} q^n/n! + q^k/k! * acc`. -/
def expAux (q : ℚ) : ℕ → ℚ → ℚ
  | 0, acc => acc
  | k + 1, acc => expAux q k (1 + q / (k + 1) * acc)

/-- Horner for `cosh √y`: `chAux y k acc = Σ_{n<k} y^n/(2n)! + y^k/(2k)! * acc`. -/
def chAux (y : ℚ) : ℕ → ℚ → ℚ
  | 0, acc => acc
  | k + 1, acc => chAux y k (1 + y / ((2 * k + 1) * (2 * k + 2)) * acc)

/-- `q^k/k!`. -/
def termAux (q : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => termAux q k * q / (k + 1)

/-- `e_N(q) = Σ_{n≤N} q^n/n!`. -/
def eLo (N : ℕ) (q : ℚ) : ℚ := expAux q N 1

/-- `ē_N(q) = e_N(q) + q^(N+1)/(N+1)! (N+2)/(N+2-q)`. -/
def eUp (N : ℕ) (q : ℚ) : ℚ := eLo N q + termAux q (N + 1) * (N + 2) / (N + 2 - q)

/-- `ch_N(y) = Σ_{n≤N} y^n/(2n)!`. -/
def chLo (N : ℕ) (y : ℚ) : ℚ := chAux y N 1

/-- The rational lower bound of drift minus 1 on `[lo, hi]` with move `s`. -/
def certQ (N : ℕ) (lo hi s : ℚ) : ℚ :=
  8 * (eLo N ((lo ^ 2 * (1 - s) + s) / 2) * chLo N (lo ^ 2 * s * (1 - s)) - eUp N (hi ^ 2 / 2)) - 1

/-- Walk a bisection tree; returns the verdict and the unread bits. -/
def check (N : ℕ) (s : ℚ) : ℕ → ℚ → ℚ → ℕ → Bool × ℕ
  | 0, _, _, code => (false, code)
  | f + 1, lo, hi, code =>
    if code % 2 = 0 then (decide (0 ≤ certQ N lo hi s), code / 2)
    else
      let r1 := check N s f lo ((lo + hi) / 2) (code / 2)
      let r2 := check N s f ((lo + hi) / 2) hi r1.2
      (r1.1 && r2.1, r2.2)

/-! ### The tail of the exponential series

The same two lemmas as in `RegretKappa/UpperSharp/Weights.lean`, so that this library imports
Mathlib only. -/

/-- `(N+1)! (N+2)^n ≤ (N+n+1)!`. -/
theorem factorial_mul_pow_le_factorial_add (N n : ℕ) :
    ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ n) ≤ ((N+n+1).factorial : ℝ) := by
  induction' n with k ih
  · norm_num
  · have h_eq : ((N+(k+1)+1).factorial : ℝ) = ((N+k+1).factorial : ℝ) * (N+k+2 : ℝ) := by
      rw [show (N+(k+1)+1 : ℕ) = (N+k+1)+1 by omega]
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [h_eq, pow_succ]
    -- Goal: ↑(N+1)! * ((↑N+2)^k * (↑N+2)) ≤ ↑(N+k+1)! * (↑N+↑k+2)
    rw [← mul_assoc]
    -- Goal: (↑(N+1)! * (↑N+2)^k) * (↑N+2) ≤ ↑(N+k+1)! * (↑N+↑k+2)
    have h_ineq1 : ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ k) * (N+2 : ℝ) ≤
        ((N+k+1).factorial : ℝ) * (N+2 : ℝ) := by
      nlinarith
    have h_ineq2 : ((N+k+1).factorial : ℝ) * (N+2 : ℝ) ≤
        ((N+k+1).factorial : ℝ) * (N+k+2 : ℝ) := by
      have h_le : (N+2 : ℝ) ≤ (N+k+2 : ℝ) := by
        exact mod_cast (show N+2 ≤ N+k+2 from by omega)
      nlinarith
    nlinarith

/-- The tail of the exponential series after `x^N/(N+1)!` is at most a geometric series of ratio
`x/(N+2)`. -/
theorem sum_tail_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (hxN : x < N + 2) (M : ℕ) :
    ∑ n ∈ range M, x ^ (N + n) / ((N + n + 1).factorial : ℝ) ≤
      x ^ N / (((N + 1).factorial : ℝ) * (1 - x / (N + 2))) := by
  set q := x / (N + 2 : ℝ) with hq
  have hNpos : 0 < (N : ℝ) + 2 := by
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hq_nonneg : 0 ≤ q := div_nonneg hx (by nlinarith)
  have hq_lt_one : q < 1 := by
    rw [hq]
    exact (div_lt_one hNpos).mpr hxN
  have h_term (n : ℕ) : x ^ (N + n) / ((N + n + 1).factorial : ℝ) ≤
      x ^ N / ((N + 1).factorial : ℝ) * q ^ n := by
    rw [hq]
    have h_fact : ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ n) ≤ ((N+n+1).factorial : ℝ) :=
      factorial_mul_pow_le_factorial_add N n
    have h_denom1_pos : 0 < ((N+n+1).factorial : ℝ) :=
      mod_cast Nat.factorial_pos (N+n+1)
    have h_denom2_pos : 0 < ((N+1).factorial : ℝ) * ((N+2 : ℝ) ^ n) := by
      positivity
    -- RHS = x^N/(N+1)! * (x/(N+2))^n = x^(N+n) / ((N+1)! * (N+2)^n)
    -- LHS = x^(N+n) / (N+n+1)!
    -- So we need: x^(N+n) / (N+n+1)! ≤ x^(N+n) / ((N+1)! * (N+2)^n)
    -- which follows from (N+n+1)! ≥ (N+1)! * (N+2)^n
    have h_rhs : x ^ N / ((N + 1).factorial : ℝ) * ((x / (N + 2)) ^ n) =
        x ^ (N + n) / (((N + 1).factorial : ℝ) * ((N + 2 : ℝ) ^ n)) := by
      rw [div_pow]
      ring
    rw [h_rhs]
    rw [div_le_div_iff₀ h_denom1_pos h_denom2_pos]
    have h_pow_nonneg : 0 ≤ x ^ (N + n) := pow_nonneg hx (N + n)
    nlinarith
  have h_geom : ∑ n ∈ range M, q ^ n ≤ (1 - q)⁻¹ := by
    -- Use geom_sum_Ico_le_of_lt_one which works for ℝ
    have h := geom_sum_Ico_le_of_lt_one hq_nonneg hq_lt_one (m := 0) (n := M)
    -- h : ∑ i ∈ Ico 0 M, q ^ i ≤ q ^ 0 / (1 - q)
    -- q^0 = 1, and Ico 0 M = range M
    rw [← range_eq_Ico] at h
    rw [pow_zero] at h
    -- h : ∑ n ∈ range M, q ^ n ≤ 1 / (1 - q)
    simpa [div_eq_inv_mul] using h
  calc
    ∑ n ∈ range M, x ^ (N + n) / ((N + n + 1).factorial : ℝ) ≤
        ∑ n ∈ range M, (x ^ N / ((N + 1).factorial : ℝ) * q ^ n) :=
      Finset.sum_le_sum fun i hi => h_term i
    _ = (x ^ N / ((N + 1).factorial : ℝ)) * (∑ n ∈ range M, q ^ n) := by
      rw [Finset.mul_sum]
    _ ≤ (x ^ N / ((N + 1).factorial : ℝ)) * ((1 - q)⁻¹) := by
      gcongr
    _ = x ^ N / (((N + 1).factorial : ℝ) * (1 - x / (N + 2))) := by
      rw [hq]
      field_simp

/-! ### Soundness -/

theorem expAux_eq (q : ℚ) (k : ℕ) (acc : ℚ) :
    (expAux q k acc : ℝ) = ∑ n ∈ range k, (q : ℝ) ^ n / n.factorial +
      (q : ℝ) ^ k / k.factorial * acc := by
  induction k generalizing acc with
  | zero => simp [expAux]
  | succ k ih =>
    rw [expAux, ih, sum_range_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem chAux_eq (y : ℚ) (k : ℕ) (acc : ℚ) :
    (chAux y k acc : ℝ) = ∑ n ∈ range k, (y : ℝ) ^ n / (2 * n).factorial +
      (y : ℝ) ^ k / (2 * k).factorial * acc := by
  induction k generalizing acc with
  | zero => simp [chAux]
  | succ k ih =>
    rw [chAux, ih, sum_range_succ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem termAux_eq (q : ℚ) (k : ℕ) : (termAux q k : ℝ) = (q : ℝ) ^ k / k.factorial := by
  induction k with
  | zero => simp [termAux]
  | succ k ih =>
    rw [termAux, Nat.factorial_succ]
    push_cast
    rw [ih]
    field_simp
    ring

theorem eLo_eq (N : ℕ) (q : ℚ) :
    (eLo N q : ℝ) = ∑ n ∈ range (N + 1), (q : ℝ) ^ n / n.factorial := by
  rw [eLo, expAux_eq, sum_range_succ]
  push_cast
  ring

theorem chLo_eq (N : ℕ) (y : ℚ) :
    (chLo N y : ℝ) = ∑ n ∈ range (N + 1), (y : ℝ) ^ n / (2 * n).factorial := by
  rw [chLo, chAux_eq, sum_range_succ]
  push_cast
  ring

theorem eLo_le_exp (N : ℕ) {q : ℚ} (hq : 0 ≤ q) : (eLo N q : ℝ) ≤ exp q := by
  rw [eLo_eq]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hq) _

theorem chLo_le_cosh (N : ℕ) {y : ℚ} (hy : 0 ≤ y) : (chLo N y : ℝ) ≤ cosh √(y : ℝ) := by
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  rw [chLo_eq]
  have h := Real.hasSum_cosh √(y : ℝ)
  simp only [pow_mul, Real.sq_sqrt hy'] at h
  exact sum_le_hasSum _ (fun n _ => by positivity) h

theorem exp_le_eUp (N : ℕ) {q : ℚ} (hq : 0 ≤ q) (hqN : (q : ℝ) < N + 2) :
    exp (q : ℝ) ≤ (eUp N q : ℝ) := by
  set x : ℝ := (↑q : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; exact_mod_cast hq
  have hN : (0 : ℝ) < N + 2 - x := by linarith
  have hE : (eUp N q : ℝ) = ∑ n ∈ range (N + 1), x ^ n / n.factorial +
      x ^ (N + 1) / (N + 1).factorial * (N + 2) / (N + 2 - x) := by
    rw [eUp]; push_cast; rw [eLo_eq, termAux_eq]
  rw [hE]
  have hS := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at hS
  rw [← hS.tsum_eq]
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun K => ?_
  have h1 : ∑ n ∈ range K, x ^ n / n.factorial ≤ ∑ n ∈ range (N + 1 + K), x ^ n / n.factorial :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun n _ _ => by positivity
  refine h1.trans ?_
  rw [sum_range_add]
  have ht := sum_tail_le hx0 N (by linarith) K
  have e : ∀ n : ℕ, x ^ (N + 1 + n) / ((N + 1 + n).factorial : ℝ) =
      x * (x ^ (N + n) / ((N + n + 1).factorial : ℝ)) := fun n => by
    rw [show N + 1 + n = N + n + 1 by ring, pow_succ]; ring
  simp only [e, ← mul_sum]
  have hb : x * (x ^ N / (((N + 1).factorial : ℝ) * (1 - x / (N + 2)))) =
      x ^ (N + 1) / (N + 1).factorial * (N + 2) / (N + 2 - x) := by
    have : (1 : ℝ) - x / (N + 2) = (N + 2 - x) / (N + 2) := by field_simp
    rw [this, pow_succ]
    field_simp
  have := mul_le_mul_of_nonneg_left ht hx0
  linarith

/-- The drift minus 1 in the form of the paper: `8 (h_s(ρ) - e^{ρ²/2}) - 1`. -/
noncomputable def driftGap (s ρ : ℝ) : ℝ :=
  8 * (exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √(s * (1 - s))) - exp (ρ ^ 2 / 2)) - 1

theorem leaf_sound {N : ℕ} {lo hi s : ℚ} (h : 0 ≤ certQ N lo hi s) (hlo : 0 ≤ lo)
    (hs0 : 0 < s) (hs1 : s < 1) (hhi : ((hi : ℝ) ^ 2 / 2) < N + 2) {ρ : ℝ} (h1 : (lo : ℝ) ≤ ρ)
    (h2 : ρ ≤ hi) : 0 ≤ driftGap s ρ := by
  have hlo' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1' : (s : ℝ) < 1 := by exact_mod_cast hs1
  have hρ0 : 0 ≤ ρ := hlo'.trans h1
  have hsq : (lo : ℝ) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hlo' h1 2
  have hsq' : ρ ^ 2 ≤ (hi : ℝ) ^ 2 := pow_le_pow_left₀ hρ0 h2 2
  have hq1 : (0 : ℚ) ≤ (lo ^ 2 * (1 - s) + s) / 2 := by
    have : 0 ≤ lo ^ 2 * (1 - s) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hy1 : (0 : ℚ) ≤ lo ^ 2 * s * (1 - s) := by
    have := mul_nonneg (mul_nonneg (sq_nonneg lo) hs0.le) (by linarith : (0 : ℚ) ≤ 1 - s)
    exact this
  have hq2 : (0 : ℚ) ≤ hi ^ 2 / 2 := by positivity
  have hc : (certQ N lo hi s : ℝ) = 8 * ((eLo N ((lo ^ 2 * (1 - s) + s) / 2) : ℝ) *
      (chLo N (lo ^ 2 * s * (1 - s)) : ℝ) - (eUp N (hi ^ 2 / 2) : ℝ)) - 1 := by
    simp only [certQ]; push_cast; ring
  have h' : (0 : ℝ) ≤ certQ N lo hi s := by exact_mod_cast h
  -- the three bounds
  have b1 := eLo_le_exp N hq1
  have b2 := chLo_le_cosh N hy1
  have b3 := exp_le_eUp N hq2 (by push_cast; linarith)
  push_cast at b1 b2 b3
  have e2 : √((lo : ℝ) ^ 2 * s * (1 - s)) = lo * √((s : ℝ) * (1 - s)) := by
    rw [mul_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlo']
  rw [e2] at b2
  -- monotonicity in ρ
  have m1 : exp (((lo : ℝ) ^ 2 * (1 - s) + s) / 2) ≤ exp ((ρ ^ 2 * (1 - s) + s) / 2) :=
    exp_le_exp.2 (by nlinarith)
  have hcs : 0 ≤ √((s : ℝ) * (1 - s)) := Real.sqrt_nonneg _
  have m2 : cosh ((lo : ℝ) * √((s : ℝ) * (1 - s))) ≤ cosh (ρ * √((s : ℝ) * (1 - s))) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hlo' hcs), abs_of_nonneg (mul_nonneg hρ0 hcs)]
    exact mul_le_mul_of_nonneg_right h1 hcs
  have m3 : exp (ρ ^ 2 / 2) ≤ exp ((hi : ℝ) ^ 2 / 2) := exp_le_exp.2 (by linarith)
  have hq1' : (0 : ℝ) ≤ ((lo ^ 2 * (1 - s) + s) / 2 : ℚ) := by exact_mod_cast hq1
  have hy1' : (0 : ℝ) ≤ (lo ^ 2 * s * (1 - s) : ℚ) := by exact_mod_cast hy1
  have p1 : (0 : ℝ) ≤ chLo N (lo ^ 2 * s * (1 - s)) := by
    rw [chLo_eq]
    exact sum_nonneg fun n _ => by positivity
  have prod : (eLo N ((lo ^ 2 * (1 - s) + s) / 2) : ℝ) * (chLo N (lo ^ 2 * s * (1 - s)) : ℝ) ≤
      exp ((ρ ^ 2 * (1 - s) + s) / 2) * cosh (ρ * √((s : ℝ) * (1 - s))) := by
    have := mul_le_mul (b1.trans m1) (b2.trans m2) p1 (exp_pos _).le
    simpa using this
  unfold driftGap
  rw [hc] at h'
  have : (eUp N (hi ^ 2 / 2) : ℝ) ≥ exp (ρ ^ 2 / 2) := by
    have := m3.trans b3; simpa using this
  linarith

theorem check_sound (N : ℕ) {s : ℚ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ (f : ℕ) (lo hi : ℚ) (code : ℕ), (check N s f lo hi code).1 = true → 0 ≤ lo → lo ≤ hi →
      ((hi : ℝ) ^ 2 / 2) < N + 2 → ∀ ρ : ℝ, (lo : ℝ) ≤ ρ → ρ ≤ hi → 0 ≤ driftGap s ρ := by
  intro f
  induction f with
  | zero => intro lo hi code h; simp [check] at h
  | succ f ih =>
    intro lo hi code h hlo hlh hhi ρ h1 h2
    by_cases hc : code % 2 = 0
    · simp only [check, hc, ite_true, decide_eq_true_eq] at h
      exact leaf_sound h hlo hs0 hs1 hhi h1 h2
    · simp only [check, hc, ite_false, Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      have hm0 : lo ≤ (lo + hi) / 2 := by linarith
      have hm1 : (lo + hi) / 2 ≤ hi := by linarith
      have hm2 : (((lo + hi) / 2 : ℚ) : ℝ) ^ 2 / 2 < N + 2 := by
        have h0 : (0 : ℝ) ≤ ((lo + hi) / 2 : ℚ) := by exact_mod_cast hlo.trans hm0
        have h3 : (((lo + hi) / 2 : ℚ) : ℝ) ≤ hi := by exact_mod_cast hm1
        nlinarith
      rcases le_total ρ (((lo + hi) / 2 : ℚ) : ℝ) with hr | hr
      · exact ih lo _ _ ha hlo hm0 hm2 ρ h1 hr
      · exact ih _ hi _ hb (hlo.trans hm0) hm1 hhi ρ hr h2

end RegretKappa.LowerSharp
