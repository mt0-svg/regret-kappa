import RegretKappa.LowerSharp.Chain

/-!
# Sharp lower bound: the hitting time of phase 1

The paper, Lemmas B.3 (the overshoot), B.4 (a geometric tail) and 4.4 (1) and (2), for the chain
stopped at level `L` (`sst`). The expectations are the backward recursion `ex` of
`Lower/Hitting.lean` (the Markov property built in; `avg_chainOf` turns it into the average over
the signs).

* Overshoot: the set `|ρ| ≤ a₊`, `a₊ = √L + √(5/8) e^{-L/4}` (`aP`), is invariant under the moves
  when `L ≥ 14.5` (`abs_sst_le`), and on it `U ≤ G = 8.8 e^{L/2}` (`U_le_G`).
* Optional stopping on a finite horizon: `U(ρ) + n P(ρ_n² < L) ≤ E U(ρ_n) ≤ G`
  (`lyap_add_mul_leS`), so `P(ρ_n² < L) ≤ G/n` from every state of the invariant set.
* Restart: `P(ρ_{jn}² < L) ≤ (G/n)^j` (`ex_below_pow`), by the semigroup law of `ex`
  (`ex_add`) and the pointwise bound `P_ρ(ρ_n² < L) ≤ (G/n) 1{ρ² < L}` on the invariant set
  (the stopped chain stays above `L`); the restart of the paper needs no conditional probability.
* Phase 1 (1): the failure probability after `m - 1` steps from `ρ_0 = ±1` is at most
  `(G/n)^j` whenever `j n ≤ m - 1` (`avg_fail_le`).
-/

namespace RegretKappa.LowerSharp

open Real RegretKappa.Lower

/-- `a₊ = √L + √(5/8) e^{-L/4}`, the largest `|ρ|` the chain stopped at `L` reaches. -/
noncomputable def aP (L : ℝ) : ℝ := √L + √(5 / 8) * exp (-L / 4)

/-- The constant `G = 8.8 e^{L/2}` of Lemma B.3. -/
noncomputable def Gc (L : ℝ) : ℝ := 88 / 10 * exp (L / 2)

/-- The semigroup law of the backward recursion. -/
theorem ex_add (st : ℝ → Bool → ℝ) (a b : ℕ) (f : ℝ → ℝ) (ρ : ℝ) :
    ex st (a + b) f ρ = ex st a (ex st b f) ρ := by
  induction a generalizing ρ with
  | zero =>
    simp [ex]
  | succ a ih =>
    rw [Nat.succ_add]
    simp [ex]
    rw [ih (st ρ true), ih (st ρ false)]

/-- The backward recursion is linear. -/
theorem ex_mul_left (st : ℝ → Bool → ℝ) (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (ρ : ℝ) :
    ex st n (fun x => c * f x) ρ = c * ex st n f ρ := by
  induction n generalizing ρ with
  | zero =>
      simp [ex]
  | succ n ih =>
      simp [ex]
      rw [ih (st ρ true), ih (st ρ false)]
      ring

theorem ex_below_nonneg' (st : ℝ → Bool → ℝ) (L : ℝ) (n : ℕ) (ρ : ℝ) :
    0 ≤ ex st n (below L) ρ := by
  have h := ex_mono_on st (S := Set.univ) (fun _ _ _ => Set.mem_univ _)
    (f := fun _ => (0 : ℝ)) (g := below L) (fun ρ _ => by unfold below; split_ifs <;> norm_num) n
    (Set.mem_univ ρ)
  rwa [ex_const] at h

theorem ex_below_le_one' (st : ℝ → Bool → ℝ) (L : ℝ) (n : ℕ) (ρ : ℝ) :
    ex st n (below L) ρ ≤ 1 := by
  have h := ex_mono_on st (S := Set.univ) (fun _ _ _ => Set.mem_univ _)
    (f := below L) (g := fun _ => (1 : ℝ)) (fun ρ _ => by unfold below; split_ifs <;> norm_num) n
    (Set.mem_univ ρ)
  rwa [ex_const] at h

theorem abs_stepS_le {s : ℝ} (hs0 : 0 ≤ s) (ρ : ℝ) (b : Bool) :
    |stepS s ρ b| ≤ |ρ| + √s := by
  unfold stepS
  have h1 : √(1 - s) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have h2 : 0 ≤ √(1 - s) := Real.sqrt_nonneg _
  calc |ρ * √(1 - s) + sgn b * √s| ≤ |ρ * √(1 - s)| + |sgn b * √s| := abs_add_le _ _
    _ = |ρ| * √(1 - s) + √s := by
        rw [abs_mul, abs_mul, abs_sgn, abs_of_nonneg h2, abs_of_nonneg (Real.sqrt_nonneg _),
          one_mul]
    _ ≤ |ρ| * 1 + √s := by gcongr
    _ = |ρ| + √s := by ring

/-- `u ↦ u + √(5/8) e^{-u²/4}` is nondecreasing. -/
theorem overshoot_mono {u v : ℝ} (huv : u ≤ v) :
    u + √(5 / 8) * exp (-u ^ 2 / 4) ≤ v + √(5 / 8) * exp (-v ^ 2 / 4) := by
  set c := √(5 / 8) with hc
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hc_lt_one : c < 1 := by
    rw [hc, ← Real.sqrt_one]
    refine Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (5 : ℝ) / 8 < 1)
  have h_bound : ∀ x : ℝ, x * Real.exp (-(x ^ 2) / 4) ≤ 1 := by
    intro x
    have h_exp : x ^ 2 / 4 + 1 ≤ Real.exp (x ^ 2 / 4) := Real.add_one_le_exp _
    have h_sq_ineq : x ≤ x ^ 2 / 4 + 1 := by
      have h_nonneg_sq : (x / 2 - 1) ^ 2 ≥ 0 := by positivity
      nlinarith
    have hx : x ≤ Real.exp (x ^ 2 / 4) := by linarith
    have h_exp_nonneg : 0 ≤ Real.exp (-(x ^ 2) / 4) := Real.exp_nonneg _
    calc
      x * Real.exp (-(x ^ 2) / 4) ≤ Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2) / 4) :=
        mul_le_mul_of_nonneg_right hx h_exp_nonneg
      _ = Real.exp ((x ^ 2 / 4) + (-(x ^ 2) / 4)) := by rw [Real.exp_add]
      _ = Real.exp 0 := by ring_nf
      _ = 1 := Real.exp_zero
  set f := fun x : ℝ => x + c * Real.exp (-(x ^ 2) / 4) with hf
  set f' := fun x : ℝ => 1 - c * (x / 2) * Real.exp (-(x ^ 2) / 4) with hf'
  have h_deriv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    dsimp [f, f']
    have h_id : HasDerivAt (fun x' : ℝ => x') 1 x := hasDerivAt_id x
    have h_neg_sq_div_four : HasDerivAt (fun x' : ℝ => -(x' ^ 2) / 4) (-(x / 2)) x := by
      have h_sq : HasDerivAt (fun x' : ℝ => x' ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have h_neg_sq : HasDerivAt (fun x' : ℝ => -(x' ^ 2)) (-(2 * x)) x :=
        HasDerivAt.neg h_sq
      have h_div : HasDerivAt (fun x' : ℝ => -(x' ^ 2) / 4) (-(2 * x) / 4) x :=
        HasDerivAt.div_const h_neg_sq 4
      have : -(2 * x) / 4 = -(x / 2) := by ring
      rw [this] at h_div
      exact h_div
    have h_exp : HasDerivAt (fun x' : ℝ => Real.exp (-(x' ^ 2) / 4))
        (Real.exp (-(x ^ 2) / 4) * (-(x / 2))) x :=
      HasDerivAt.exp h_neg_sq_div_four
    have h_mul : HasDerivAt (fun x' : ℝ => c * Real.exp (-(x' ^ 2) / 4))
        (c * (Real.exp (-(x ^ 2) / 4) * (-(x / 2)))) x :=
      HasDerivAt.const_mul c h_exp
    have h_sum : HasDerivAt (fun x' : ℝ => x' + c * Real.exp (-(x' ^ 2) / 4))
        (1 + c * (Real.exp (-(x ^ 2) / 4) * (-(x / 2)))) x :=
      HasDerivAt.add h_id h_mul
    have : 1 + c * (Real.exp (-(x ^ 2) / 4) * (-(x / 2))) = f' x := by
      dsimp [f']
      ring
    rw [this] at h_sum
    exact h_sum
  have h_f'_nonneg : 0 ≤ f' := by
    intro x
    dsimp [f']
    have hx_bound : x * Real.exp (-(x ^ 2) / 4) ≤ 1 := h_bound x
    have : c * (x / 2) * Real.exp (-(x ^ 2) / 4) ≤ c / 2 := by
      nlinarith
    have hc2 : c / 2 < 1 := by linarith [hc_lt_one]
    nlinarith
  have h_mono : Monotone f := monotone_of_hasDerivAt_nonneg h_deriv h_f'_nonneg
  exact h_mono huv

/-- `a₊²/2 ≤ L/2 + log 1.1` for `L ≥ 14.5` (the paper, Lemma B.3). -/
theorem exp_aP_sq_le {L : ℝ} (hL : 145 / 10 ≤ L) :
    exp (aP L ^ 2 / 2) ≤ 11 / 10 * exp (L / 2) := by
  have hL0 : 0 ≤ L := by linarith
  have haP : aP L = √L + √(5 / 8) * exp (-L / 4) := rfl
  set s := √L with hs
  set e := exp (-L / 4) with he
  set c := √(5 / 8 : ℝ) with hc
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 5 / 8 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc8 : c ≤ 4 / 5 := by nlinarith
  have he0 : 0 < e := Real.exp_pos _
  have h36 : (36 : ℝ) ≤ exp (29 / 8) := by
    have h1 : exp (29 / 8 : ℝ) = exp 1 ^ 3 * exp (5 / 8) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h2 : (2.7182818283 : ℝ) ^ 3 ≤ exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
    have h3 : 1 + 5 / 8 + (5 / 8 : ℝ) ^ 2 / 2 ≤ exp (5 / 8) :=
      Real.quadratic_le_exp_of_nonneg (by norm_num)
    have h4 : 0 ≤ exp 1 ^ 3 := by positivity
    rw [h1]
    nlinarith
  have hee : e * exp (L / 4) = 1 := by
    rw [he, ← Real.exp_add, show -L / 4 + L / 4 = 0 by ring, Real.exp_zero]
  have hE : 36 * (1 + (L - 29 / 2) / 4) ≤ exp (L / 4) := by
    have h1 : exp (L / 4) = exp (29 / 8) * exp ((L - 29 / 2) / 4) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (L - 29 / 2) / 4 + 1 ≤ exp ((L - 29 / 2) / 4) := Real.add_one_le_exp _
    have h3 : 0 ≤ (L - 29 / 2) / 4 + 1 := by linarith
    rw [h1]
    nlinarith [Real.exp_pos ((L - 29 / 2) / 4)]
  have hsle : s ≤ 4 + (L - 29 / 2) := by nlinarith
  have h9 : 9 * s ≤ exp (L / 4) := by nlinarith
  have hse : s * e ≤ 1 / 9 := by nlinarith
  have he36 : e ≤ 1 / 36 := by nlinarith
  have hid : aP L ^ 2 / 2 = L / 2 + (c * (s * e) + 5 / 16 * e ^ 2) := by
    rw [haP]
    linear_combination (1 / 2 : ℝ) * hs2 + (e ^ 2 / 2) * hc2
  have hε0 : 0 ≤ c * (s * e) + 5 / 16 * e ^ 2 := by positivity
  have hcse : c * (s * e) ≤ 4 / 5 * (1 / 9) :=
    mul_le_mul hc8 hse (mul_nonneg hs0 he0.le) (by norm_num)
  have he2 : e ^ 2 ≤ (1 / 36) ^ 2 := pow_le_pow_left₀ he0.le he36 2
  have hεle : c * (s * e) + 5 / 16 * e ^ 2 ≤ 9 / 100 := by nlinarith
  have hexp : exp (c * (s * e) + 5 / 16 * e ^ 2) ≤ 11 / 10 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := c * (s * e) + 5 / 16 * e ^ 2)
      (by rw [abs_of_nonneg hε0]; linarith)
    have h' := (abs_le.1 h).2
    nlinarith
  rw [hid, Real.exp_add, mul_comm]
  exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le

theorem sqrt_large_move (ρ : ℝ) : √(5 / 8 * exp (-ρ ^ 2 / 2)) = √(5 / 8) * exp (-ρ ^ 2 / 4) := by
  have h : exp (-ρ ^ 2 / 2) = exp (-ρ ^ 2 / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [Real.sqrt_mul (by norm_num), h, Real.sqrt_sq (Real.exp_pos _).le]

/-- **Lemma B.3 (the overshoot), invariance**: for `L ≥ 14.5` the stopped chain keeps
`|ρ| ≤ a₊`. -/
theorem abs_sst_le {L : ℝ} (hL : 145 / 10 ≤ L) {ρ : ℝ} (hρ : |ρ| ≤ aP L) (b : Bool) :
    |sst L ρ b| ≤ aP L := by
  rcases le_or_gt L (ρ ^ 2) with h | h
  · rw [sst_of_le h]; exact hρ
  rw [sst_of_lt h]
  have hs0 := (smove_pos ρ).le
  have hst := abs_stepS_le hs0 ρ b
  have hL0 : 0 ≤ L := by linarith
  have ha : |ρ| < √L := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) h
  have hsa : √L ≤ aP L := by
    unfold aP; have := Real.sqrt_nonneg (5 / 8); have := Real.exp_pos (-L / 4); nlinarith
  have h38 : 38 / 10 ≤ √L := by
    rw [Real.le_sqrt (by norm_num) hL0]; linarith
  by_cases hc : |ρ| < 28 / 10
  · have : √(smove ρ) ≤ 8 / 10 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith [smove_le ρ]
    linarith
  · have hsm : smove ρ = 5 / 8 * exp (-ρ ^ 2 / 2) := by simp [smove, hc]
    rw [hsm]
    rw [hsm, sqrt_large_move] at hst
    have hm := overshoot_mono ha.le
    rw [Real.sq_sqrt hL0, sq_abs] at hm
    unfold aP
    linarith

/-- Every state of the stopped chain has `|ρ| ≤ a₊`. -/
theorem abs_rhoS_le {L : ℝ} (hL : 145 / 10 ≤ L) (ζ : ℕ → Bool) (t : ℕ) :
    |rhoS L ζ t| ≤ aP L := by
  induction t with
  | zero =>
    simp only [rhoS, abs_sgn]
    have h38 : 38 / 10 ≤ √L := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    unfold aP
    have := Real.sqrt_nonneg (5 / 8)
    have := Real.exp_pos (-L / 4)
    nlinarith
  | succ t ih => exact abs_sst_le hL ih _

theorem U_le_G {L : ℝ} (hL : 145 / 10 ≤ L) {ρ : ℝ} (hρ : |ρ| ≤ aP L) : U ρ ≤ Gc L := by
  have h1 : ρ ^ 2 ≤ aP L ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hρ 2
  have h2 : exp (ρ ^ 2 / 2) ≤ exp (aP L ^ 2 / 2) := Real.exp_le_exp.2 (by linarith)
  have h3 := exp_aP_sq_le hL
  unfold U Gc
  linarith

/-- Optional stopping on a finite horizon: `U(ρ) + n P(ρ_n² < L) ≤ E U(ρ_n)`. -/
theorem lyap_add_mul_leS (L : ℝ) (n : ℕ) (ρ : ℝ) :
    U ρ + n * ex (sst L) n (below L) ρ ≤ ex (sst L) n U ρ := by
  induction n generalizing ρ with
  | zero => simp [ex]
  | succ n ih =>
    simp only [ex]
    have iht := ih (sst L ρ true)
    have ihf := ih (sst L ρ false)
    by_cases h : ρ ^ 2 < L
    · rw [sst_of_lt h true] at iht ⊢
      rw [sst_of_lt h false] at ihf ⊢
      have hd := drift ρ
      have h1 := ex_below_le_one' (sst L) L n (stepS (smove ρ) ρ true)
      have h2 := ex_below_le_one' (sst L) L n (stepS (smove ρ) ρ false)
      push_cast
      nlinarith
    · have hL : L ≤ ρ ^ 2 := by linarith
      rw [sst_of_le hL true, sst_of_le hL false]
      rw [ex_fixed (sst L) (fun b => sst_of_le hL b) U n,
        ex_fixed (sst L) (fun b => sst_of_le hL b) (below L) n]
      simp [below, not_lt.2 hL]

theorem ex_U_le {L : ℝ} (hL : 145 / 10 ≤ L) (n : ℕ) {ρ : ℝ} (hρ : |ρ| ≤ aP L) :
    ex (sst L) n U ρ ≤ Gc L := by
  have h := ex_mono_on (sst L) (S := {ρ | |ρ| ≤ aP L}) (fun ρ hρ b => abs_sst_le hL hρ b)
    (f := U) (g := fun _ => Gc L) (fun ρ hρ => U_le_G hL hρ) n hρ
  rwa [ex_const] at h

/-- The pointwise restart bound: `P_ρ(ρ_n² < L) ≤ (G/n) 1{ρ² < L}` on the invariant set. -/
theorem ex_below_pt {L : ℝ} (hL : 145 / 10 ≤ L) {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ}
    (hρ : |ρ| ≤ aP L) : ex (sst L) n (below L) ρ ≤ Gc L / n * below L ρ := by
  by_cases h : ρ ^ 2 < L
  · have h1 := lyap_add_mul_leS L n ρ
    have h2 := ex_U_le hL n hρ
    have h3 : 0 < U ρ := by unfold U; positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [below, h, ite_true, mul_one]
    rw [le_div_iff₀ hn']
    linarith
  · have hL' : L ≤ ρ ^ 2 := by linarith
    rw [ex_fixed (sst L) (fun b => sst_of_le hL' b) (below L) n]
    simp [below, h]

/-- **Lemma B.4, the geometric tail**: `P(ρ_{jn}² < L) ≤ (G/n)^j`. -/
theorem ex_below_pow {L : ℝ} (hL : 145 / 10 ≤ L) {n : ℕ} (hn : 1 ≤ n) (j : ℕ) {ρ : ℝ}
    (hρ : |ρ| ≤ aP L) : ex (sst L) (j * n) (below L) ρ ≤ (Gc L / n) ^ j := by
  induction j generalizing ρ with
  | zero =>
    simp only [zero_mul, ex, pow_zero]
    unfold below; split_ifs <;> norm_num
  | succ j ih =>
    rw [show (j + 1) * n = j * n + n by ring, ex_add]
    have hG : 0 ≤ Gc L / n := by unfold Gc; positivity
    have h1 := ex_mono_on (sst L) (S := {ρ | |ρ| ≤ aP L}) (fun ρ hρ b => abs_sst_le hL hρ b)
      (f := ex (sst L) n (below L)) (g := fun x => Gc L / n * below L x)
      (fun ρ hρ => ex_below_pt hL hn hρ) (j * n) hρ
    rw [ex_mul_left] at h1
    calc _ ≤ _ := h1
      _ ≤ Gc L / n * (Gc L / n) ^ j := mul_le_mul_of_nonneg_left (ih hρ) hG
      _ = (Gc L / n) ^ (j + 1) := by ring

/-- The failure probability does not grow with the horizon. -/
theorem ex_below_le_below (L : ℝ) (d : ℕ) (ρ : ℝ) : ex (sst L) d (below L) ρ ≤ below L ρ := by
  by_cases h : ρ ^ 2 < L
  · simp only [below, h, ite_true]
    exact ex_below_le_one' _ L d ρ
  · have hL' : L ≤ ρ ^ 2 := by linarith
    rw [ex_fixed (sst L) (fun b => sst_of_le hL' b) (below L) d]

theorem ex_below_anti (L : ℝ) {n N : ℕ} (h : n ≤ N) (ρ : ℝ) :
    ex (sst L) N (below L) ρ ≤ ex (sst L) n (below L) ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [ex_add]
  exact ex_mono_on (sst L) (S := Set.univ) (fun _ _ _ => Set.mem_univ _)
    (fun ρ _ => ex_below_le_below L d ρ) n (Set.mem_univ ρ)

/-- The final phase-1 statistic `ρ_F = ρ_{m-1}`. -/
noncomputable def rhoF (L : ℝ) {m : ℕ} (ξ : Fin m → Bool) : ℝ := rhoS L (ext ξ) (m - 1)

/-- The final `V = V_{m-1}`. -/
noncomputable def VF (L : ℝ) {m : ℕ} (ξ : Fin m → Bool) : ℝ := VS L (ext ξ) (m - 1)

/-- **Lemma 4.4 (1)**: phase 1 fails with probability at most `(G/n)^j` when `j n ≤ m - 1`. -/
theorem avg_fail_le {L : ℝ} (hL : 145 / 10 ≤ L) {m : ℕ} (hm : 1 ≤ m) {j n : ℕ} (hn : 1 ≤ n)
    (hjn : j * n ≤ m - 1) : avg m (fun ξ => below L (rhoF L ξ)) ≤ (Gc L / n) ^ j := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hjn
  have hb : ∀ b : Bool, avg m' (fun ξ => below L (rhoF L (Fin.cons b ξ : Fin (m' + 1) → Bool)))
      ≤ (Gc L / n) ^ j := fun b => by
    have h1 : ∀ ξ : Fin m' → Bool, rhoF L (Fin.cons b ξ : Fin (m' + 1) → Bool) =
        chainOf (sst L) (sgn b) (ext ξ) m' := fun ξ => by
      unfold rhoF
      rw [Nat.add_sub_cancel, rhoS_eq_chainOf, ext_cons]
      rfl
    simp_rw [h1]
    rw [avg_chainOf]
    have h0 : |sgn b| ≤ aP L := by
      have := abs_rhoS_le hL (fun _ => b) 0
      simpa [rhoS] using this
    exact (ex_below_anti L hjn _).trans (ex_below_pow hL hn j h0)
  rw [avg_cons]
  linarith [hb true, hb false]

end RegretKappa.LowerSharp
