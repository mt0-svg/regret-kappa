import RegretKappa.Lower.ClosedForm
import RegretKappa.LowerSharp.Statement

/-!
# Sharp lower bound: the closed form of the phase-2 sum

Step (iv) of the phase-2 bound, with the prior information `J` as a parameter (`wInfoJ`; Lower's
`wInfo` is the case `J = 5/2`), in the indexing of Lean (round `i = 0, ..., k - 1` here is round
`i + 1` of the paper; `ε_i = eps k r i`, `ν_i² = nu2 k i`).

* `closedFormJ`: `∑_{i<k} ε_i² / W_i ≥ Λ (1 - 1/(2k)) - 1` with `Λ = log(k / (4 J r²))`, the proof
  of `Lower.closedForm` with `J` in place of `5/2`. The sum of `log(i/k)` is bounded through
  `k^k / k! ≤ e^k`; this is the paper's integral of `log` (it gives the same `(k - 1)(Λ - 2) - 2`).
* `comparator_closed`: the comparator term, `(1 + A)/W_k ≥ 1/2 - (J - 2) r² / (k + 1)` with
  `A = ∑ ε_i² = (k + 1)/(4 r²)`.
* `beta_ge`: for `J = π²/4`, `E Z² = 4/3 - 8/π²`, `r ≥ 2` and `k ≥ π² e² r²`,
  `β(ρ, k) ≥ log(k/r²) - c₁ - log k/(2k) - 1/k`.
-/

namespace RegretKappa.LowerSharp

open Finset Real RegretKappa.Lower

/-- The information available before round `i`, prior information `J` included. -/
noncomputable def wInfoJ (J : ℝ) (k : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  J + ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l)

/-- The information grows at least like `J (1 + i² / (4 J r² k))`. -/
theorem wInfoJ_ge {J : ℝ} (hJ : 0 < J) {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) {i : ℕ}
    (hi : i ≤ k) : J * (1 + i ^ 2 / (4 * J * r ^ 2 * k)) ≤ wInfoJ J k r i := by
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
  have hJ_ne_zero : J ≠ 0 := by linarith
  calc
    J * (1 + (i : ℝ) ^ 2 / (4 * J * r ^ 2 * (k : ℝ))) = J + (i : ℝ) ^ 2 / (4 * r ^ 2 * (k : ℝ)) := by
      field_simp [hJ_ne_zero, hk_pos.ne.symm, hr.ne.symm]
    _ ≤ J + ∑ l ∈ range i, eps k r l ^ 2 / (1 - nu2 k l) := by nlinarith
    _ = wInfoJ J k r i := rfl

/-- One round against the logarithm of the information. -/
theorem round_ge_logJ {J : ℝ} (hJ : 0 < J) {k : ℕ} {r : ℝ} {i : ℕ} (hi : i < k) :
    (1 - nu2 k i) * (log (wInfoJ J k r (i + 1)) - log (wInfoJ J k r i)) ≤
      eps k r i ^ 2 / wInfoJ J k r i := by
  have hWpos : 0 < wInfoJ J k r i := by
    unfold wInfoJ
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
  have h_wInfo_succ : wInfoJ J k r (i + 1) = wInfoJ J k r i + eps k r i ^ 2 / (1 - nu2 k i) := by
    unfold wInfoJ
    rw [Finset.sum_range_succ]
    ring
  have hWpos' : 0 < wInfoJ J k r (i + 1) := by
    rw [h_wInfo_succ]
    have : 0 ≤ eps k r i ^ 2 / (1 - nu2 k i) := by
      have hnum : 0 ≤ eps k r i ^ 2 := by positivity
      have hden : 0 ≤ 1 - nu2 k i := le_of_lt h_one_minus_nu_pos
      positivity
    nlinarith
  have h_ratio_pos : 0 < wInfoJ J k r (i + 1) / wInfoJ J k r i :=
    div_pos hWpos' hWpos
  have h_log_div : log (wInfoJ J k r (i + 1)) - log (wInfoJ J k r i) = log (wInfoJ J k r (i + 1) / wInfoJ J k r i) := by
    rw [Real.log_div (ne_of_gt hWpos') (ne_of_gt hWpos)]
  rw [h_log_div]
  have h_log_le : log (wInfoJ J k r (i + 1) / wInfoJ J k r i) ≤ eps k r i ^ 2 / ((1 - nu2 k i) * wInfoJ J k r i) := by
    have h := Real.log_le_sub_one_of_pos h_ratio_pos
    have h_sub_eq : wInfoJ J k r (i + 1) / wInfoJ J k r i - 1 = eps k r i ^ 2 / ((1 - nu2 k i) * wInfoJ J k r i) := by
      rw [h_wInfo_succ]
      field_simp [ne_of_gt hWpos, ne_of_gt h_one_minus_nu_pos]
      ring
    rw [h_sub_eq] at h
    exact h
  have h_mul : (1 - nu2 k i) * (log (wInfoJ J k r (i + 1) / wInfoJ J k r i)) ≤ eps k r i ^ 2 / wInfoJ J k r i := by
    have hpos' : 0 ≤ 1 - nu2 k i := le_of_lt h_one_minus_nu_pos
    have htemp : (1 - nu2 k i) * (eps k r i ^ 2 / ((1 - nu2 k i) * wInfoJ J k r i)) = eps k r i ^ 2 / wInfoJ J k r i := by
      field_simp [ne_of_gt h_one_minus_nu_pos, ne_of_gt hWpos]
    apply mul_le_mul_of_nonneg_left h_log_le hpos' |>.trans ?_
    rw [htemp]
  exact h_mul

/-- **Closed form of the van Trees sum** with prior information `J`. -/
theorem closedFormJ {J : ℝ} (hJ : 0 < J) {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) :
    log (k / (4 * J * r ^ 2)) * (1 - 1 / (2 * k)) - 1 ≤
      ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ J k r i := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set Λ := log (k / (4 * J * r ^ 2)) with hΛ
  set l : ℕ → ℝ := fun i => log (wInfoJ J k r i) - log J with hl
  have hW : ∀ i ≤ k, 0 < wInfoJ J k r i := fun i hi => by
    have hge := wInfoJ_ge hJ hk hr hi
    have hpos : J ≤ J * (1 + (i : ℝ) ^ 2 / (4 * J * r ^ 2 * k)) := by
      have : 0 ≤ (i : ℝ) ^ 2 / (4 * J * r ^ 2 * k) := by positivity
      nlinarith
    linarith
  have hl0 : l 0 = 0 := by simp [hl, wInfoJ]
  -- step 1
  have h1 : ∑ i ∈ range k, (1 - ((i : ℝ) + 1) / (2 * k)) * (l (i + 1) - l i) ≤
      ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ J k r i := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := round_ge_logJ hJ (r := r) (Finset.mem_range.1 hi)
    simp only [hl, nu2] at this ⊢
    linarith
  rw [sum_by_parts k hk l hl0] at h1
  -- step 2
  have hli : ∀ i ≤ k, log (1 + (i : ℝ) ^ 2 / (4 * J * r ^ 2 * k)) ≤ l i := fun i hi => by
    have h := wInfoJ_ge hJ hk hr hi
    simp only [hl]
    rw [le_sub_iff_add_le, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlk : Λ ≤ l k := by
    refine le_trans ?_ (hli k le_rfl)
    refine Real.log_le_log (by positivity) ?_
    have : (k : ℝ) ^ 2 / (4 * J * r ^ 2 * k) = k / (4 * J * r ^ 2) := by
      field_simp [ne_of_gt hk0]
    rw [this]
    linarith
  have hl1 : ∀ i ∈ Ico 1 k, Λ + 2 * log ((i : ℝ) / k) ≤ l i := fun i hi => by
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
    refine le_trans ?_ (hli i hi2.le)
    have e : Λ + 2 * log ((i : ℝ) / k) = log ((i : ℝ) ^ 2 / (4 * J * r ^ 2 * k)) := by
      rw [show (i : ℝ) ^ 2 / (4 * J * r ^ 2 * k) = (k / (4 * J * r ^ 2)) * ((i : ℝ) / k) ^ 2 by
        field_simp [ne_of_gt hk0], Real.log_mul (by positivity) (by positivity), Real.log_pow, hΛ]
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
      field_simp [ne_of_gt hk0]
      ring
    rw [e]
    have : (((k : ℝ) - 1) * Λ - 2 * k) / (2 * k) ≤ (∑ i ∈ range k, l i) / (2 * k) :=
      div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  linarith

/-- `A = ∑_{i<k} ε_i² = (k + 1)/(4 r²)`. -/
theorem sum_eps_sq {k : ℕ} (hk : 1 ≤ k) (r : ℝ) :
    ∑ i ∈ range k, eps k r i ^ 2 = (k + 1) / (4 * r ^ 2) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hk)
  calc
    ∑ i ∈ range k, eps k r i ^ 2 = ∑ i ∈ range k, ((i + 1 : ℝ) / (2 * (k : ℝ) * r ^ 2)) := by
      refine Finset.sum_congr rfl (λ i hi => ?_)
      rw [eps_sq]
    _ = (∑ i ∈ range k, ((i : ℝ) + 1)) / ((2 : ℝ) * (k : ℝ) * r ^ 2) := by
      rw [Finset.sum_div]
    _ = (((k : ℝ) * ((k : ℝ) + 1)) / 2) / ((2 : ℝ) * (k : ℝ) * r ^ 2) := by
      have hsum : ∑ i ∈ range k, ((i : ℝ) + 1) = ((k : ℝ) * ((k : ℝ) + 1)) / 2 := by
        refine Nat.rec ?_ (λ m ih => ?_) k
        · simp
        · rw [Finset.sum_range_succ, ih]
          push_cast
          ring
      rw [hsum]
    _ = (k + 1) / (4 * r ^ 2) := by
      field_simp [hk0]
      ring

/-- The comparator term: `(1 + A)/W_k ≥ 1/2 - (J - 2) r² / (k + 1)`. -/
theorem comparator_closed {J : ℝ} (hJ : 2 ≤ J) {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) :
    1 / 2 - (J - 2) * r ^ 2 / (k + 1) ≤
      (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ J k r k := by
  set A := ∑ i ∈ range k, eps k r i ^ 2 with hA_def
  set W := wInfoJ J k r k with hW_def
  have hApos : 0 < A := by
    rw [hA_def, sum_eps_sq hk r]
    have hk' : (0 : ℝ) < k + 1 := by
      have : (0 : ℕ) < k + 1 := by omega
      exact_mod_cast this
    have hr_sq_pos : 0 < r ^ 2 := pow_pos hr 2
    positivity
  have hA_nonneg : 0 ≤ A := le_of_lt hApos
  have hWpos : 0 < W := by
    rw [hW_def, wInfoJ]
    have hJpos : 0 < J := by linarith
    have hsum_nonneg : 0 ≤ ∑ l ∈ range k, eps k r l ^ 2 / (1 - nu2 k l) := by
      refine Finset.sum_nonneg (λ l hl => ?_)
      have h_eps_sq_nonneg : 0 ≤ eps k r l ^ 2 := pow_two_nonneg _
      have h_denom_pos : 0 < 1 - nu2 k l := by
        have h_nu2_le_half : nu2 k l ≤ 1/2 := nu2_le_half (by
          rw [Finset.mem_range] at hl
          exact hl)
        linarith
      exact div_nonneg h_eps_sq_nonneg h_denom_pos.le
    nlinarith
  have hW_le_J_plus_2A : W ≤ J + 2 * A := by
    rw [hW_def, hA_def, wInfoJ]
    have hsum : ∑ l ∈ range k, eps k r l ^ 2 / (1 - nu2 k l) ≤ ∑ l ∈ range k, (2 * eps k r l ^ 2) := by
      refine Finset.sum_le_sum (λ l hl => ?_)
      have h_eps_sq_nonneg : 0 ≤ eps k r l ^ 2 := pow_two_nonneg _
      have h_nu2_le_half : nu2 k l ≤ 1/2 := nu2_le_half (by
        rw [Finset.mem_range] at hl
        exact hl)
      have h_nu2_ge_half : 1/2 ≤ 1 - nu2 k l := by linarith
      calc
        eps k r l ^ 2 / (1 - nu2 k l) ≤ eps k r l ^ 2 / (1/2) := by
          refine (div_le_div_of_nonneg_left h_eps_sq_nonneg (by norm_num) h_nu2_ge_half)
        _ = 2 * eps k r l ^ 2 := by ring
    have hsum2 : ∑ l ∈ range k, (2 * eps k r l ^ 2) = 2 * (∑ l ∈ range k, eps k r l ^ 2) := by
      simp [Finset.mul_sum]
    nlinarith
  have h_alg : (1 + A) / (J + 2 * A) ≥ 1/2 - (J - 2) / (4 * A) := by
    have hpos_denom1 : 0 < J + 2 * A := by nlinarith
    have hpos_denom2 : 0 < 4 * A := by nlinarith
    have h_diff_nonneg : 0 ≤ (1 + A) / (J + 2 * A) - (1/2 - (J - 2) / (4 * A)) := by
      field_simp [hpos_denom1.ne', hpos_denom2.ne']
      ring_nf
      nlinarith
    linarith
  have h_goal : (1 + A) / W ≥ 1/2 - (J - 2) * r ^ 2 / (k + 1) := by
    calc
      (1 + A) / W ≥ (1 + A) / (J + 2 * A) := by
        refine div_le_div_of_nonneg_left (by nlinarith) hWpos hW_le_J_plus_2A
      _ ≥ 1/2 - (J - 2) / (4 * A) := h_alg
      _ = 1/2 - (J - 2) * r ^ 2 / (k + 1) := by
        rw [hA_def, sum_eps_sq hk r]
        have hk1_ne_zero : (k : ℝ) + 1 ≠ 0 := by
          intro hzero
          have : (k : ℕ) + 1 = 0 := by exact_mod_cast hzero
          omega
        field_simp [hk1_ne_zero]
  -- Now rewrite the goal using A and W
  rw [hA_def, hW_def]
  exact h_goal

/-- **The phase-2 bound, step (iv)**: `β(ρ, k) ≥ log(k/r²) - c₁ - log k/(2k) - 1/k` for `k ≥ π² e² r²`. -/
theorem beta_ge {k : ℕ} {r : ℝ} (hr : 2 ≤ r) (hk : π ^ 2 * exp 2 * r ^ 2 ≤ k) :
    log (k / r ^ 2) - c1 - log k / (2 * k) - 1 / k ≤
      -(4 / 3 - 8 / π ^ 2) + ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i +
        (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ Jc k r k := by
  have hrpos : 0 < r := by linarith
  have h_exp_gt_1 : 1 < exp 2 := by
    linarith [Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)]
  have hkpos : 1 ≤ k := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by
      have h_ineq : (1 : ℝ) ≤ π ^ 2 * exp 2 * r ^ 2 := by
        have hπgt3 : (3 : ℝ) < π := Real.pi_gt_three
        have hr2 : (4 : ℝ) ≤ r ^ 2 := by nlinarith
        have hπsq_gt_9 : (9 : ℝ) < π ^ 2 := by nlinarith
        have hprod : (36 : ℝ) < π ^ 2 * r ^ 2 := by nlinarith
        have hpos : 0 < exp 2 := Real.exp_pos 2
        nlinarith
      have hk_real : (π ^ 2 * exp 2 * r ^ 2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    exact_mod_cast hk'
  have hkpos_real : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hJcpos : 0 < Jc := by
    unfold Jc
    positivity
  have hJcge2 : 2 ≤ Jc := by
    unfold Jc
    have hπgt3 : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  have h_closed := closedFormJ hJcpos hkpos hrpos
  have h_4Jc : (4 : ℝ) * Jc = π ^ 2 := by
    unfold Jc
    ring
  have h_sum1_lower : log (↑k / (π ^ 2 * r ^ 2)) - log (k : ℝ) / (2 * (k : ℝ)) - 1 ≤
      ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i := by
    have h_log_eq : log (↑k / ((4 : ℝ) * Jc * r ^ 2)) = log (↑k / (π ^ 2 * r ^ 2)) := by
      rw [h_4Jc]
    have h_Λ_le_logk : log (↑k / (π ^ 2 * r ^ 2)) ≤ log (k : ℝ) := by
      have h_denom_ge_one : (1 : ℝ) ≤ π ^ 2 * r ^ 2 := by
        have hπgt3 : (3 : ℝ) < π := Real.pi_gt_three
        have hr2 : (4 : ℝ) ≤ r ^ 2 := by nlinarith
        have hπsq_gt_9 : (9 : ℝ) < π ^ 2 := by nlinarith
        nlinarith
      have h_div_le : (k : ℝ) / (π ^ 2 * r ^ 2) ≤ (k : ℝ) :=
        div_le_self (by exact_mod_cast (Nat.zero_le _)) h_denom_ge_one
      have h_div_pos : 0 < (k : ℝ) / (π ^ 2 * r ^ 2) := by positivity
      exact Real.log_le_log h_div_pos h_div_le
    have h_Λ_mul_ge : log (↑k / (π ^ 2 * r ^ 2)) * (1 - 1 / (2 * (k : ℝ))) ≥
        log (↑k / (π ^ 2 * r ^ 2)) - log (k : ℝ) / (2 * (k : ℝ)) := by
      have h_eq : log (↑k / (π ^ 2 * r ^ 2)) * (1 - 1 / (2 * (k : ℝ))) =
          log (↑k / (π ^ 2 * r ^ 2)) - log (↑k / (π ^ 2 * r ^ 2)) / (2 * (k : ℝ)) := by ring
      rw [h_eq]
      have h_div : log (↑k / (π ^ 2 * r ^ 2)) / (2 * (k : ℝ)) ≤ log (k : ℝ) / (2 * (k : ℝ)) :=
        div_le_div_of_nonneg_right h_Λ_le_logk (by positivity)
      linarith
    have h_closed' : log (↑k / (π ^ 2 * r ^ 2)) * (1 - 1 / (2 * (k : ℝ))) - 1 ≤
        ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i := by
      simpa [h_log_eq] using h_closed
    linarith
  have h_sum2_lower : 1 / 2 - (Jc - 2) / (π ^ 2 * exp 2) ≤
      (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ Jc k r k := by
    have h_comp := comparator_closed hJcge2 hkpos hrpos
    have h_bound : (Jc - 2) * r ^ 2 / ((k : ℝ) + 1) ≤ (Jc - 2) / (π ^ 2 * exp 2) := by
      have hJc_minus_2_nonneg : 0 ≤ Jc - 2 := by linarith
      have h_r2_div_kp1 : r ^ 2 / ((k : ℝ) + 1) ≤ 1 / (π ^ 2 * exp 2) := by
        have h_r2_div_k : r ^ 2 / (k : ℝ) ≤ 1 / (π ^ 2 * exp 2) := by
          have hk_real : π ^ 2 * exp 2 * r ^ 2 ≤ (k : ℝ) := by exact_mod_cast hk
          have hpos_k : 0 < (k : ℝ) := hkpos_real
          have hpos_denom : 0 < π ^ 2 * exp 2 := by positivity
          field_simp [hpos_k.ne', hpos_denom.ne']
          nlinarith
        have h_r2_div_kp1' : r ^ 2 / ((k : ℝ) + 1) ≤ r ^ 2 / (k : ℝ) := by
          have hpos_k : 0 < (k : ℝ) := hkpos_real
          have hpos_kp1 : 0 < (k : ℝ) + 1 := by nlinarith
          field_simp [hpos_kp1.ne', hpos_k.ne']
          nlinarith [sq_nonneg r]
        linarith
      calc
        (Jc - 2) * r ^ 2 / ((k : ℝ) + 1) = (Jc - 2) * (r ^ 2 / ((k : ℝ) + 1)) := by ring
        _ ≤ (Jc - 2) * (1 / (π ^ 2 * exp 2)) := by
          gcongr
        _ = (Jc - 2) / (π ^ 2 * exp 2) := by ring
    linarith
  have h_total : log (↑k / r ^ 2) - log (k : ℝ) / (2 * (k : ℝ)) - c1 ≤
      -(4 / 3 - 8 / π ^ 2) + ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i +
        (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ Jc k r k := by
    have h_log_eq : log (↑k / (π ^ 2 * r ^ 2)) = log (↑k / r ^ 2) - log (π ^ 2) := by
      calc
        log (↑k / (π ^ 2 * r ^ 2)) = log ((↑k / r ^ 2) / π ^ 2) := by ring_nf
        _ = log (↑k / r ^ 2) - log (π ^ 2) := Real.log_div (by positivity) (by positivity)
    have h_algebraic : -(4 / 3 - 8 / π ^ 2) + (log (↑k / (π ^ 2 * r ^ 2)) - log (k : ℝ) / (2 * (k : ℝ)) - 1) +
        (1 / 2 - (Jc - 2) / (π ^ 2 * exp 2)) = log (↑k / r ^ 2) - log (k : ℝ) / (2 * (k : ℝ)) - c1 := by
      unfold c1 Jc
      rw [h_log_eq]
      ring_nf
    have h_sum : -(4 / 3 - 8 / π ^ 2) + (log (↑k / (π ^ 2 * r ^ 2)) - log (k : ℝ) / (2 * (k : ℝ)) - 1) +
        (1 / 2 - (Jc - 2) / (π ^ 2 * exp 2)) ≤
        -(4 / 3 - 8 / π ^ 2) + ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i +
          (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ Jc k r k := by
      nlinarith
    linarith
  have h_final : log (↑k / r ^ 2) - c1 - log (k : ℝ) / (2 * (k : ℝ)) - 1 / (k : ℝ) ≤
      log (↑k / r ^ 2) - log (k : ℝ) / (2 * (k : ℝ)) - c1 := by
    have h_nonneg : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  linarith

end RegretKappa.LowerSharp
