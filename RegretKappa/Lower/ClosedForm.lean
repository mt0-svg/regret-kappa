import Mathlib

/-!
# Lower bound: the phase-2 schedule and the closed form of its van Trees sum

The paper, Lemma 4.11 (iv), in the indexing of Lean (round `i = 0, ..., k - 1` here is
round `i + 1` of the paper). With `r = |ρ| + 2`, the phase-2 feature of round `i`, normalized by
`√V_{T₁}`, is `ε_i = √((i + 1) / (2 k r²))`, so `|θ* x| ≤ r ε_i = ν_i` with
`ν_i² = (i + 1) / (2 k) ≤ 1/2`. The information available before round `i` is at most
`W_i = 5/2 + ∑_{l < i} ε_l² / (1 - ν_l²)` (`5/2` the information of the prior), and round `i`
contributes `ε_i² / W_i`.

`closedForm`: `∑_{i < k} ε_i² / W_i ≥ Λ (1 - 1/(2k)) - 1` with `Λ = log (k / (10 r²))`. Proof as in
the paper: `ε_i² / W_i ≥ (1 - ν_i²) (l_{i+1} - l_i)` with `l_i = log (W_i / (5/2))`
(`log x ≤ x - 1`), summation by parts gives `l_k / 2 + (1/(2k)) ∑_{i<k} l_i`, and
`l_i ≥ log (β i²) = Λ + 2 log (i / k)` with `β = 1/(10 r² k)` for `i ≥ 1`. Departure from the paper:
the sum of `log (i / k)` is bounded by `log (k! / k^k) ≥ -k` (from `k^k / k! ≤ e^k`) instead of an
integral of `log`.
-/

namespace RegretKappa.Lower

open Finset Real

/-- The normalized phase-2 feature of round `i` out of `k`, `r = |ρ| + 2`. -/
noncomputable def eps (k : ℕ) (r : ℝ) (i : ℕ) : ℝ := √((i + 1) / (2 * k * r ^ 2))

/-- The bound `ν_i² = (i + 1) / (2 k)` of `(θ* x)²` in round `i`. -/
noncomputable def nu2 (k i : ℕ) : ℝ := (i + 1) / (2 * k)

/-- The information available before round `i`, prior included. -/
noncomputable def wInfo (k : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  5 / 2 + ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l)

theorem eps_sq {k : ℕ} {r : ℝ} (i : ℕ) : eps k r i ^ 2 = (i + 1) / (2 * k * r ^ 2) := by
  unfold eps
  exact Real.sq_sqrt (by positivity)

theorem eps_nonneg (k : ℕ) (r : ℝ) (i : ℕ) : 0 ≤ eps k r i := Real.sqrt_nonneg _

/-- `r ε_i = ν_i`. -/
theorem mul_eps_sq {k : ℕ} {r : ℝ} (hr : 0 < r) (i : ℕ) : (r * eps k r i) ^ 2 = nu2 k i := by
  rw [mul_pow, eps_sq]
  unfold nu2
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · field_simp

theorem nu2_le_half {k i : ℕ} (hi : i < k) : nu2 k i ≤ 1 / 2 := by
  unfold nu2
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [div_le_iff₀ (by positivity)]
  have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
  linarith

theorem nu2_nonneg (k i : ℕ) : 0 ≤ nu2 k i := by
  unfold nu2
  positivity

-- TARGET

/-- The information grows at least like `5/2 (1 + β i²)`, `β = 1 / (10 r² k)`. -/
theorem wInfo_ge {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) {i : ℕ} (hi : i ≤ k) :
    5 / 2 * (1 + i ^ 2 / (10 * r ^ 2 * k)) ≤ wInfo k r i := by
  have h_gauss : (∑ l ∈ range i, ((l : ℝ) + 1)) = ((i : ℝ) * ((i : ℝ) + 1)) / 2 := by
    induction i with
    | zero => simp
    | succ n ih =>
      have hn_le_k : n ≤ k := by omega
      rw [Finset.sum_range_succ, ih hn_le_k]
      push_cast
      ring
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hk
  have hr_sq_pos : 0 < r ^ 2 := pow_pos hr 2
  have h_nu2_nonneg (l : ℕ) : 0 ≤ nu2 k l := nu2_nonneg k l
  have h_nu2_le_half (l : ℕ) (hl : l < k) : nu2 k l ≤ 1/2 := nu2_le_half hl
  have h_one_minus_nu2_pos (l : ℕ) (hl : l < i) : 0 < 1 - nu2 k l := by
    have h := h_nu2_le_half l (lt_of_lt_of_le hl hi)
    linarith
  have h_term_ge (l : ℕ) (hl : l < i) : eps k r l ^ 2 ≤ eps k r l ^ 2 / (1 - nu2 k l) := by
    have hpos : 0 < 1 - nu2 k l := h_one_minus_nu2_pos l hl
    field_simp [hpos.ne.symm]
    nlinarith [h_nu2_nonneg l, pow_two_nonneg (eps k r l)]
  have h_eps_sq (l : ℕ) : eps k r l ^ 2 = ((l : ℝ) + 1) / (2 * (k : ℝ) * r ^ 2) := by
    simpa using eps_sq (k := k) (r := r) l
  have h_sum_eps_sq : ∑ l ∈ range i, eps k r l ^ 2 = ((i : ℝ) * ((i : ℝ) + 1)) / (4 * r ^ 2 * (k : ℝ)) := by
    calc
      ∑ l ∈ range i, eps k r l ^ 2 = ∑ l ∈ range i, (((l : ℝ) + 1) / (2 * (k : ℝ) * r ^ 2)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [h_eps_sq l]
      _ = (∑ l ∈ range i, ((l : ℝ) + 1)) / (2 * (k : ℝ) * r ^ 2) := by rw [Finset.sum_div]
      _ = (((i : ℝ) * ((i : ℝ) + 1)) / 2) / (2 * (k : ℝ) * r ^ 2) := by rw [h_gauss]
      _ = ((i : ℝ) * ((i : ℝ) + 1)) / (4 * r ^ 2 * (k : ℝ)) := by ring
  have h_sum_ge : (i : ℝ) ^ 2 / (4 * r ^ 2 * (k : ℝ)) ≤ ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l) := by
    have h_denom_nonneg : 0 ≤ 4 * r ^ 2 * (k : ℝ) := by positivity
    have hi_nonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    have h_sq_le : (i : ℝ) ^ 2 ≤ (i : ℝ) * ((i : ℝ) + 1) := by
      nlinarith
    have h_main : (i : ℝ) ^ 2 / (4 * r ^ 2 * (k : ℝ)) ≤ ((i : ℝ) * ((i : ℝ) + 1)) / (4 * r ^ 2 * (k : ℝ)) :=
      div_le_div_of_nonneg_right h_sq_le h_denom_nonneg
    have h_term_le : ∑ l ∈ range i, eps k r l ^ 2 ≤ ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l) :=
      Finset.sum_le_sum fun l hl => h_term_ge l (by simpa [Finset.mem_range] using hl)
    calc
      (i : ℝ) ^ 2 / (4 * r ^ 2 * (k : ℝ)) ≤ ((i : ℝ) * ((i : ℝ) + 1)) / (4 * r ^ 2 * (k : ℝ)) := h_main
      _ = ∑ l ∈ range i, eps k r l ^ 2 := by rw [h_sum_eps_sq]
      _ ≤ ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l) := h_term_le
  calc
    5 / 2 * (1 + (i : ℝ) ^ 2 / (10 * r ^ 2 * (k : ℝ))) = 5/2 + (i : ℝ) ^ 2 / (4 * r ^ 2 * (k : ℝ)) := by ring
    _ ≤ 5/2 + ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l) := by nlinarith
    _ = wInfo k r i := rfl

-- TARGET

/-- One round against the logarithm of the information. -/
theorem round_ge_log {k : ℕ} {r : ℝ} {i : ℕ} (hi : i < k) :
    (1 - nu2 k i) * (log (wInfo k r (i + 1)) - log (wInfo k r i)) ≤
      eps k r i ^ 2 / wInfo k r i := by
  have hWpos : 0 < wInfo k r i := by
    unfold wInfo
    have hsum : 0 ≤ ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l) := by
      refine Finset.sum_nonneg fun l hl => ?_
      have hnum : 0 ≤ eps k r l ^ 2 := by positivity
      have hden : 0 < 1 - nu2 k l := by
        have hl_lt_k : l < k := lt_trans (Finset.mem_range.1 hl) hi
        have hνl : nu2 k l ≤ 1/2 := nu2_le_half hl_lt_k
        linarith
      positivity
    nlinarith
  have h_one_minus_nu_pos : 0 < 1 - nu2 k i := by
    have hν : nu2 k i ≤ 1/2 := nu2_le_half hi
    linarith
  have h_wInfo_succ : wInfo k r (i + 1) = wInfo k r i + eps k r i ^ 2 / (1 - nu2 k i) := by
    unfold wInfo
    rw [Finset.sum_range_succ]
    ring
  have hWpos' : 0 < wInfo k r (i + 1) := by
    rw [h_wInfo_succ]
    have : 0 ≤ eps k r i ^ 2 / (1 - nu2 k i) := by
      have hnum : 0 ≤ eps k r i ^ 2 := by positivity
      have hden : 0 ≤ 1 - nu2 k i := le_of_lt h_one_minus_nu_pos
      positivity
    nlinarith
  have h_ratio_pos : 0 < wInfo k r (i + 1) / wInfo k r i :=
    div_pos hWpos' hWpos
  have h_log_div : log (wInfo k r (i + 1)) - log (wInfo k r i) = log (wInfo k r (i + 1) / wInfo k r i) := by
    rw [Real.log_div (ne_of_gt hWpos') (ne_of_gt hWpos)]
  rw [h_log_div]
  have h_log_le : log (wInfo k r (i + 1) / wInfo k r i) ≤ eps k r i ^ 2 / ((1 - nu2 k i) * wInfo k r i) := by
    have h := Real.log_le_sub_one_of_pos h_ratio_pos
    have h_sub_eq : wInfo k r (i + 1) / wInfo k r i - 1 = eps k r i ^ 2 / ((1 - nu2 k i) * wInfo k r i) := by
      rw [h_wInfo_succ]
      field_simp [ne_of_gt hWpos, ne_of_gt h_one_minus_nu_pos]
      ring
    rw [h_sub_eq] at h
    exact h
  have h_mul : (1 - nu2 k i) * (log (wInfo k r (i + 1) / wInfo k r i)) ≤ eps k r i ^ 2 / wInfo k r i := by
    have hpos' : 0 ≤ 1 - nu2 k i := le_of_lt h_one_minus_nu_pos
    have htemp : (1 - nu2 k i) * (eps k r i ^ 2 / ((1 - nu2 k i) * wInfo k r i)) = eps k r i ^ 2 / wInfo k r i := by
      field_simp [ne_of_gt h_one_minus_nu_pos, ne_of_gt hWpos]
    apply mul_le_mul_of_nonneg_left h_log_le hpos' |>.trans ?_
    rw [htemp]
  exact h_mul

private lemma sum_abel (k : ℕ) (l : ℕ → ℝ) : ∑ i ∈ range k, ((i : ℝ) + 1) * (l (i + 1) - l i) = (k : ℝ) * l k - ∑ i ∈ range k, l i := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- Summation by parts with the weights `1 - (i + 1)/(2k)`. -/
theorem sum_by_parts (k : ℕ) (hk : 1 ≤ k) (l : ℕ → ℝ) (h0 : l 0 = 0) :
    ∑ i ∈ range k, (1 - ((i : ℝ) + 1) / (2 * k)) * (l (i + 1) - l i) =
      l k / 2 + (∑ i ∈ range k, l i) / (2 * k) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hk)
  have h_telescope : ∑ i ∈ range k, (l (i + 1) - l i) = l k := by
    rw [Finset.sum_range_sub, h0, sub_zero]
  have h_factor : (∑ i ∈ range k, (((i : ℝ) + 1) / (2 * (k : ℝ))) * (l (i + 1) - l i)) =
      (1 / (2 * (k : ℝ))) * (∑ i ∈ range k, ((i : ℝ) + 1) * (l (i + 1) - l i)) := by
    calc
      (∑ i ∈ range k, (((i : ℝ) + 1) / (2 * (k : ℝ))) * (l (i + 1) - l i)) =
          ∑ i ∈ range k, ((1 / (2 * (k : ℝ))) * (((i : ℝ) + 1) * (l (i + 1) - l i))) := by
        refine Finset.sum_congr rfl (λ i hi => ?_)
        ring
      _ = (1 / (2 * (k : ℝ))) * (∑ i ∈ range k, ((i : ℝ) + 1) * (l (i + 1) - l i)) := by
        rw [Finset.mul_sum]
  calc
    ∑ i ∈ range k, (1 - ((i : ℝ) + 1) / (2 * k)) * (l (i + 1) - l i) =
        ∑ i ∈ range k, ((l (i + 1) - l i) - (((i : ℝ) + 1) / (2 * k)) * (l (i + 1) - l i)) := by
      refine Finset.sum_congr rfl (λ i hi => ?_)
      ring
    _ = (∑ i ∈ range k, (l (i + 1) - l i)) -
        (∑ i ∈ range k, (((i : ℝ) + 1) / (2 * k)) * (l (i + 1) - l i)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ range k, (l (i + 1) - l i)) -
        ((1 / (2 * (k : ℝ))) * (∑ i ∈ range k, ((i : ℝ) + 1) * (l (i + 1) - l i))) := by
      rw [h_factor]
    _ = l k - ((1 / (2 * (k : ℝ))) * ((k : ℝ) * l k - ∑ i ∈ range k, l i)) := by
      rw [h_telescope, sum_abel]
    _ = l k / 2 + (∑ i ∈ range k, l i) / (2 * (k : ℝ)) := by
      field_simp [hk0]
      ring

/-- `∑_{1 ≤ i < k} log (i / k) ≥ -k`. -/
theorem sum_log_div_ge (k : ℕ) (hk : 1 ≤ k) :
    -(k : ℝ) ≤ ∑ i ∈ Ico 1 k, log ((i : ℝ) / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsplit : ∑ i ∈ Ico 1 (k + 1), log ((i : ℝ) / k) = ∑ i ∈ Ico 1 k, log ((i : ℝ) / k) := by
    rw [Finset.sum_Ico_succ_top (by omega), div_self hk0.ne', Real.log_one, add_zero]
  rw [← hsplit, ← Real.log_prod (fun i hi => by
    have : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    have : (0 : ℝ) < i := by exact_mod_cast this
    positivity)]
  have hprod : ∏ i ∈ Ico 1 (k + 1), ((i : ℝ) / k) = (Nat.factorial k : ℝ) / (k : ℝ) ^ k := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel]
    congr 1
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
  rw [hprod]
  have hf : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h1 := Real.pow_div_factorial_le_exp (k : ℝ) hk0.le k
  have h2 : Real.exp (-(k : ℝ)) ≤ (Nat.factorial k : ℝ) / (k : ℝ) ^ k := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact h1
  calc -(k : ℝ) = Real.log (Real.exp (-(k : ℝ))) := (Real.log_exp _).symm
    _ ≤ Real.log ((Nat.factorial k : ℝ) / (k : ℝ) ^ k) := Real.log_le_log (Real.exp_pos _) h2

/-- **Closed form of the van Trees sum** (Lemma 4.11 (iv) of the paper, this schedule). -/
theorem closedForm {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) :
    log (k / (10 * r ^ 2)) * (1 - 1 / (2 * k)) - 1 ≤
      ∑ i ∈ range k, eps k r i ^ 2 / wInfo k r i := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set Λ := log (k / (10 * r ^ 2)) with hΛ
  set l : ℕ → ℝ := fun i => log (wInfo k r i) - log (5 / 2) with hl
  have hW : ∀ i ≤ k, 0 < wInfo k r i := fun i hi =>
    lt_of_lt_of_le (by positivity) (wInfo_ge hk hr hi)
  have hl0 : l 0 = 0 := by simp [hl, wInfo]
  -- step 1
  have h1 : ∑ i ∈ range k, (1 - ((i : ℝ) + 1) / (2 * k)) * (l (i + 1) - l i) ≤
      ∑ i ∈ range k, eps k r i ^ 2 / wInfo k r i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := round_ge_log (r := r) (Finset.mem_range.1 hi)
    simp only [hl, nu2] at this ⊢
    linarith
  rw [sum_by_parts k hk l hl0] at h1
  -- step 2
  have hli : ∀ i ≤ k, log (1 + (i : ℝ) ^ 2 / (10 * r ^ 2 * k)) ≤ l i := fun i hi => by
    have h := wInfo_ge hk hr hi
    simp only [hl]
    rw [le_sub_iff_add_le, ← Real.log_mul (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlk : Λ ≤ l k := by
    refine le_trans ?_ (hli k le_rfl)
    refine Real.log_le_log (by positivity) ?_
    rw [show (k : ℝ) ^ 2 / (10 * r ^ 2 * k) = k / (10 * r ^ 2) by field_simp]
    linarith
  have hl1 : ∀ i ∈ Ico 1 k, Λ + 2 * log ((i : ℝ) / k) ≤ l i := fun i hi => by
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
    refine le_trans ?_ (hli i hi2.le)
    have e : Λ + 2 * log ((i : ℝ) / k) = log ((i : ℝ) ^ 2 / (10 * r ^ 2 * k)) := by
      rw [show (i : ℝ) ^ 2 / (10 * r ^ 2 * k) = (k / (10 * r ^ 2)) * ((i : ℝ) / k) ^ 2 by
        field_simp, Real.log_mul (by positivity) (by positivity), Real.log_pow, hΛ]
      push_cast
      ring
    rw [e]
    exact Real.log_le_log (by positivity) (by linarith)
  -- step 3
  have h3 : ((k : ℝ) - 1) * Λ - 2 * k ≤ ∑ i ∈ range k, l i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hl0, zero_add]
    have hs := Finset.sum_le_sum hl1
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, ← Finset.mul_sum] at hs
    have hlog := sum_log_div_ge k hk
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
    rw [nsmul_eq_mul, hc] at hs
    linarith
  -- step 4
  have h4 : Λ * (1 - 1 / (2 * k)) - 1 ≤ l k / 2 + (∑ i ∈ range k, l i) / (2 * k) := by
    have e : Λ * (1 - 1 / (2 * k)) - 1 = Λ / 2 + (((k : ℝ) - 1) * Λ - 2 * k) / (2 * k) := by
      field_simp
      ring
    rw [e]
    have : (((k : ℝ) - 1) * Λ - 2 * k) / (2 * k) ≤ (∑ i ∈ range k, l i) / (2 * k) :=
      div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  linarith

end RegretKappa.Lower
