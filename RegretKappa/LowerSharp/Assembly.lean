import RegretKappa.LowerSharp.Adversary
import RegretKappa.LowerSharp.Phase2
import RegretKappa.LowerSharp.Side

/-!
# Sharp lower bound: assembly

The paper, proof of Theorem 4.1, on the adversary of `LowerSharp/Adversary.lean` at level `L` on
`m + k` rounds. Its randomness: phase-1 signs `ξ` uniform (`avg`), the prior variable `z` with
density `g²` on `[-2, 2]` (`gP`), phase-2 signs `η` with law `lik` given `z`.

* `expReg_ge`: given `ξ`, the expected regret is at least `P₁(ξ) + 1_Succ (ρ_F² + β(ρ_F, k))`
  (`regret_succ`, `phase2S` on success; `regret_fail` on failure);
* `avg_P1_nonneg`: `E P₁ ≥ 0` (Lemma 4.7 (3));
* `avg_expReg_ge`: `E Reg ≥ P(Succ) B₀` (`beta_ge`, `mono_u`, Lemma 4.7 (2) as `abs_rhoS_le`);
* `prob_fail_le`: `P(fail) ≤ e^{-j}` (Lemma 4.7 (1) from `avg_fail_le`);
* `adv_core`: the adversary as a finite mixture of plays with weights
  `w(ξ, η) = 2^{-m} ∫ g² lik(η | z) dz`, forcing `(1 - e^{-j}) B₀` on every learner;
* `lowerSharpAdv`, `lowerSharpBound`: the statements of `RegretKappa/LowerSharp/Statement.lean`.
-/

namespace RegretKappa.LowerSharp

open Finset Real RegretKappa.Lower

/-- The weights `∑_η g² lik(η | z) F(η)` are continuous in `z`. -/
theorem continuous_weightedP {k : ℕ} (α β : Fin k → ℝ) (F : (Fin k → Bool) → ℝ) :
    Continuous fun z => ∑ η, gP z ^ 2 * lik α β η z * F η :=
  continuous_finsetSum _ fun η _ =>
    ((continuous_gP.pow 2).mul (continuous_lik α β η)).mul continuous_const

/-- The weights integrate to `1`. -/
theorem integral_weightsP {k : ℕ} (α β : Fin k → ℝ) (c : ℝ) :
    ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 * lik α β η z * c = c := by
  have h : ∀ z, ∑ η, gP z ^ 2 * lik α β η z * c = c * gP z ^ 2 := fun z => by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_lik, mul_one, mul_comm]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_gP_sq, mul_one]

theorem weight_nonnegP (L : ℝ) {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) {z : ℝ}
    (hz : z ∈ Set.Icc (-2 : ℝ) 2) :
    0 ≤ gP z ^ 2 * lik (fun l => rhoF L ξ * eps k (rr L ξ) l) (fun l => eps k (rr L ξ) l) η z := by
  refine mul_nonneg (sq_nonneg _) (lik_nonneg (fun l => ?_) η)
  rw [show rhoF L ξ * eps k (rr L ξ) l + eps k (rr L ξ) l * z =
    (rhoF L ξ + z) * eps k (rr L ξ) l by ring]
  refine (abs_mean_le (le_refl (rr L ξ)) l hz).trans ?_
  rw [Real.sqrt_le_one]
  linarith [nu2_le_half l.isLt]

/-- The expected regret given the phase-1 signs `ξ`. -/
noncomputable def expReg (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool) : ℝ :=
  ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 *
    lik (fun l => rhoF L ξ * eps k (rr L ξ) l) (fun l => eps k (rr L ξ) l) η z *
      regret Lrn (xA L k ξ) (yA L ξ η)

/-- `β(ρ, k)` of Lemma 4.11 at radius `r`. -/
noncomputable def betaS (k : ℕ) (r : ℝ) : ℝ :=
  -(4 / 3 - 8 / π ^ 2) + ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i +
    (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ Jc k r k

theorem expReg_ge (L : ℝ) {m k : ℕ} (hm : 1 ≤ m) (Lrn : Learner (m + k)) (ξ : Fin m → Bool) :
    P1 L Lrn ξ + (if L ≤ rhoF L ξ ^ 2 then rhoF L ξ ^ 2 + betaS k (rr L ξ) else 0) ≤
      expReg L Lrn ξ := by
  set α : Fin k → ℝ := fun l => rhoF L ξ * eps k (rr L ξ) l with hα
  set β : Fin k → ℝ := fun l => eps k (rr L ξ) l with hβ
  split_ifs with hs
  · set c := P1 L Lrn ξ + rhoF L ξ ^ 2 with hc
    set Q : (Fin k → Bool) → ℝ → ℝ := fun η z =>
      -z ^ 2 + ∑ i : Fin k, ((pred L Lrn ξ η (Fin.natAdd m i) - sgn (η i)) ^ 2 -
        ((rhoF L ξ + z) * eps k (rr L ξ) i - sgn (η i)) ^ 2) +
        (1 + ∑ i : Fin k, eps k (rr L ξ) i ^ 2) *
          ((rhoF L ξ + ∑ i : Fin k, eps k (rr L ξ) i * sgn (η i)) /
            (1 + ∑ i : Fin k, eps k (rr L ξ) i ^ 2) - rhoF L ξ - z) ^ 2 with hQ
    have hph := phase2S (le_refl (rr L ξ)) (fun i η => pred L Lrn ξ η (Fin.natAdd m i))
      (fun i η η' h => pred_natAdd_congr L Lrn ξ i h)
    have hcQ : Continuous fun z => ∑ η, gP z ^ 2 * lik α β η z * Q η z := by
      simp only [hQ]
      fun_prop
    have hE : expReg L Lrn ξ = ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 * lik α β η z * (c + Q η z) := by
      unfold expReg
      congr 1
      funext z
      exact Finset.sum_congr rfl fun η _ => by
        rw [regret_succ L hm Lrn ξ η z hs]
    have hsplit : ∀ z, ∑ η, gP z ^ 2 * lik α β η z * (c + Q η z) =
        ∑ η, gP z ^ 2 * lik α β η z * c + ∑ η, gP z ^ 2 * lik α β η z * Q η z := fun z => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun η _ => by ring
    rw [hE]
    simp_rw [hsplit]
    rw [intervalIntegral.integral_add ((continuous_weightedP α β _).intervalIntegrable _ _)
      (hcQ.intervalIntegrable _ _), integral_weightsP]
    have : betaS k (rr L ξ) ≤ ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 * lik α β η z * Q η z := hph
    linarith
  · rw [add_zero, ← integral_weightsP (fun l => rhoF L ξ * eps k (rr L ξ) l)
      (fun l => eps k (rr L ξ) l) (P1 L Lrn ξ)]
    unfold expReg
    apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
    · exact (continuous_weightedP (k := k) _ _ _).intervalIntegrable _ _
    · exact (continuous_weightedP (k := k) _ _ _).intervalIntegrable _ _
    · intro z hz
      exact Finset.sum_le_sum fun η _ =>
        mul_le_mul_of_nonneg_left (regret_fail L Lrn ξ η hs) (weight_nonnegP L ξ η hz)

/-- **Lemma 4.7 (3)**: `E ∑_{t<m} (ŷ_t² - 2 ŷ_t y_t) ≥ 0`. -/
theorem avg_P1_nonneg (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) : 0 ≤ avg m (P1 L Lrn) := by
  unfold P1
  rw [avg_sum]
  refine Finset.sum_nonneg fun t _ => ?_
  have h0 : avg m (fun ξ => 2 * pred L Lrn ξ (fun _ => false) (Fin.castAdd k t) *
      sgn (ξ t)) = 0 := avg_eq_zero_of_flipAt t _ fun ξ => by
    rw [pred_castAdd_flipAt, flipAt_self, sgn_not]
    ring
  rw [avg_sub, h0, sub_zero]
  exact avg_nonneg fun ξ => sq_nonneg _

/-- `B₀` at level `L` and phase-2 length `k`. -/
noncomputable def B0L (L : ℝ) (k : ℕ) : ℝ :=
  L + log (k / (√L + 2) ^ 2) - c1 - log k / (2 * k) - 1 / k

/-- On success the phase-2 bound is at least `B₀` (Lemma 4.11 (iv), monotonicity in `|ρ_{T₁}|`). -/
theorem succ_ge {L : ℝ} (hL : 145 / 10 ≤ L) {m k : ℕ} (hk : π ^ 2 * exp 2 * (aP L + 2) ^ 2 ≤ k)
    (ξ : Fin m → Bool) (hs : L ≤ rhoF L ξ ^ 2) :
    B0L L k ≤ rhoF L ξ ^ 2 + betaS k (rr L ξ) := by
  have hρ := abs_rhoS_le hL (ext ξ) (m - 1)
  have hr2 : 2 ≤ rr L ξ := by unfold rr; linarith [abs_nonneg (rhoF L ξ)]
  have hrk : π ^ 2 * exp 2 * rr L ξ ^ 2 ≤ k := by
    refine le_trans ?_ hk
    have h1 : rr L ξ ≤ aP L + 2 := by unfold rr rhoF; linarith
    have h2 : 0 ≤ rr L ξ := by linarith
    have := pow_le_pow_left₀ h2 h1 2
    have h3 : 0 ≤ π ^ 2 * exp 2 := by positivity
    nlinarith
  have hb := beta_ge hr2 hrk
  have hL0 : 0 ≤ L := by linarith
  have ha1 : 1 ≤ √L := by rw [Real.one_le_sqrt]; linarith
  have hau : √L ≤ |rhoF L ξ| := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hs
  have hk0 : (0 : ℝ) < k := by
    have : 0 < π ^ 2 * exp 2 * (aP L + 2) ^ 2 := by
      have : 0 < aP L + 2 := by unfold aP; positivity
      positivity
    linarith
  have hm := mono_u hk0 ha1 hau
  rw [Real.sq_sqrt hL0, sq_abs] at hm
  unfold B0L betaS
  unfold rr at hb ⊢
  linarith

/-- **Expected regret** (proof of Theorem 4.1): `E Reg ≥ P(Succ) B₀`. -/
theorem avg_expReg_ge {L : ℝ} (hL : 145 / 10 ≤ L) {m k : ℕ} (hm : 1 ≤ m)
    (hk : π ^ 2 * exp 2 * (aP L + 2) ^ 2 ≤ k) (Lrn : Learner (m + k)) :
    (1 - avg m (fun ξ => below L (rhoF L ξ))) * B0L L k ≤ avg m (expReg L Lrn) := by
  have hpt : ∀ ξ : Fin m → Bool,
      P1 L Lrn ξ + (1 - below L (rhoF L ξ)) * B0L L k ≤ expReg L Lrn ξ := fun ξ => by
    have h := expReg_ge L hm Lrn ξ
    unfold below
    split_ifs at h ⊢ with h1 h2 h2
    · exact absurd h1 (not_lt.2 h2)
    · linarith
    · linarith [succ_ge hL hk ξ (not_lt.1 h1)]
    · exact absurd (not_lt.1 h1) h2
  have h := avg_mono hpt
  rw [avg_add] at h
  have e : avg m (fun ξ => (1 - below L (rhoF L ξ)) * B0L L k) =
      (1 - avg m (fun ξ => below L (rhoF L ξ))) * B0L L k := by
    simp_rw [mul_comm _ (B0L L k)]
    rw [avg_mul_left, avg_sub, avg_const]
  rw [e] at h
  linarith [avg_P1_nonneg L Lrn]

/-- **Lemma 4.7 (1)**: `P(fail) ≤ e^{-j}` when `j n ≤ m - 1` with `n ≥ e G`. -/
theorem prob_fail_le {L : ℝ} (hL : 145 / 10 ≤ L) {m j n : ℕ} (hm : 1 ≤ m) (hn : exp 1 * Gc L ≤ n)
    (hjn : j * n ≤ m - 1) : avg m (fun ξ => below L (rhoF L ξ)) ≤ exp (-(j : ℝ)) := by
  have hG : 0 < Gc L := by unfold Gc; positivity
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have h := avg_fail_le hL hm hn1 hjn
  have hq : Gc L / n ≤ exp (-1) := by
    rw [div_le_iff₀ hn0, Real.exp_neg]
    rw [mul_comm] at hn
    calc Gc L = (Gc L * exp 1) * (exp 1)⁻¹ := by field_simp
      _ ≤ n * (exp 1)⁻¹ := by gcongr
      _ = (exp 1)⁻¹ * n := by ring
  have hq0 : 0 ≤ Gc L / n := by positivity
  calc avg m (fun ξ => below L (rhoF L ξ)) ≤ (Gc L / n) ^ j := h
    _ ≤ exp (-1) ^ j := pow_le_pow_left₀ hq0 hq j
    _ = exp (-(j : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- The average over the phase-1 signs of an interval integral of a finite sum over the phase-2
signs is a finite weighted sum over both. -/
theorem avg_integral_sumP {m k : ℕ} (g : (Fin m → Bool) → (Fin k → Bool) → ℝ → ℝ)
    (hg : ∀ ξ η, Continuous (g ξ η)) (r : (Fin m → Bool) → (Fin k → Bool) → ℝ) :
    avg m (fun ξ => ∫ z in (-2 : ℝ)..2, ∑ η, g ξ η z * r ξ η) =
      ∑ p : (Fin m → Bool) × (Fin k → Bool),
        (∫ z in (-2 : ℝ)..2, g p.1 p.2 z) / 2 ^ m * r p.1 p.2 := by
  dsimp [avg]
  have hsum : (∑ ξ : Fin m → Bool, ∫ z in (-2 : ℝ)..2, ∑ η : Fin k → Bool, g ξ η z * r ξ η) =
      (∑ p : (Fin m → Bool) × (Fin k → Bool), ((∫ z in (-2 : ℝ)..2, g p.1 p.2 z) * r p.1 p.2)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun η _ => ?_
      rw [intervalIntegral.integral_mul_const]
    · intro η _
      exact ((hg ξ η).mul continuous_const).intervalIntegrable _ _
  rw [hsum, Finset.sum_div]
  exact Finset.sum_congr rfl fun p _ => by rw [div_mul_eq_mul_div]

/-- **The adversary at a fixed horizon** as a finite mixture of plays. -/
theorem adv_core {L : ℝ} (hL : 145 / 10 ≤ L) {m k j n : ℕ} (hm : 1 ≤ m)
    (hn : exp 1 * Gc L ≤ n) (hjn : j * n ≤ m - 1)
    (hk : π ^ 2 * exp 2 * (aP L + 2) ^ 2 ≤ k) (hB : 0 ≤ B0L L k) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin (m + k) → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i t, 0 ≤ x i t) ∧
      (∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) ∧
      ∀ Lrn : Learner (m + k), (1 - exp (-(j : ℝ))) * B0L L k ≤ ∑ i, w i * regret Lrn (x i) (y i) := by
  set g : (Fin m → Bool) → (Fin k → Bool) → ℝ → ℝ := fun ξ η z => gP z ^ 2 *
    lik (fun l => rhoF L ξ * eps k (rr L ξ) l) (fun l => eps k (rr L ξ) l) η z with hgdef
  have hg : ∀ ξ η, Continuous (g ξ η) := fun ξ η => by
    simp only [hgdef]
    exact (continuous_gP.pow 2).mul (continuous_lik _ _ η)
  refine ⟨(Fin m → Bool) × (Fin k → Bool), inferInstance,
    fun p => (∫ z in (-2 : ℝ)..2, g p.1 p.2 z) / 2 ^ m,
    fun p => xA L k p.1, fun p => yA L p.1 p.2, fun p => ?_, ?_, fun p t => xA_nonneg L k p.1 t,
    fun p t => yA_mem L p.1 p.2 t, fun Lrn => ?_⟩
  · refine div_nonneg (intervalIntegral.integral_nonneg (by norm_num) fun z hz => ?_)
      (by positivity)
    exact weight_nonnegP L p.1 p.2 hz
  · have h := avg_integral_sumP g hg (fun _ _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [← h]
    have e : ∀ ξ : Fin m → Bool, ∫ z in (-2 : ℝ)..2, ∑ η, g ξ η z = 1 := fun ξ => by
      have := integral_weightsP (k := k) (fun l => rhoF L ξ * eps k (rr L ξ) l)
        (fun l => eps k (rr L ξ) l) 1
      simpa only [hgdef, mul_one] using this
    simp_rw [e]
    exact avg_const m 1
  · have h := avg_integral_sumP g hg (fun ξ η => regret Lrn (xA L k ξ) (yA L ξ η))
    have e : avg m (expReg L Lrn) =
        avg m (fun ξ => ∫ z in (-2 : ℝ)..2, ∑ η, g ξ η z * regret Lrn (xA L k ξ) (yA L ξ η)) :=
      rfl
    rw [← h, ← e]
    have h1 := avg_expReg_ge hL hm hk Lrn
    have h2 := prob_fail_le hL hm hn hjn
    nlinarith

/-- `B₀ T ≥ 0` for `T ≥ T₀`. -/
theorem B0_nonneg {T : ℕ} (hT : T0 ≤ T) : 0 ≤ B0 T := by
  have h1 := B0_ge hT
  have h2 := simplified_two hT
  have hu : 61 / 5 ≤ log T := by
    have hT' : (355713 : ℝ) ≤ T := by exact_mod_cast hT
    rw [Real.le_log_iff_exp_le (by linarith)]
    have e1 : exp (61 / 5 : ℝ) = exp 1 ^ 12 * exp (1 / 5) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have e2 : exp (1 / 5 : ℝ) ≤ 5 / 4 := by
      have h := Real.add_one_le_exp (-(1 / 5) : ℝ)
      have h' : exp (-(1 / 5) : ℝ) * exp (1 / 5) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (1 / 5 : ℝ)]
    have e3 : exp 1 ^ 12 ≤ 2.7182818286 ^ 12 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 12
    have e4 : 0 ≤ exp 1 ^ 12 := by positivity
    rw [e1]
    nlinarith [Real.exp_pos (1 / 5 : ℝ)]
  have hl : log (log T) ≤ log T - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith

/-- **The paper, Theorem 4.1, against a finite adversary.** -/
theorem lowerSharpAdv : LowerSharpAdv := by
  intro T hT
  have hT' : (355713 : ℕ) ≤ T := hT
  set L := level T with hLdef
  have hL : 145 / 10 ≤ L := by have := level_ge hT; rw [hLdef]; linarith
  set n := ⌈exp 1 * Gc L⌉₊ with hndef
  have hn : exp 1 * Gc L ≤ n := Nat.le_ceil _
  have hn' : (n : ℝ) < exp 1 * Gc L + 1 := Nat.ceil_lt_add_one (by unfold Gc; positivity)
  have hjn : j0 T * n ≤ T1 T - 1 := by
    have hc := C2 hT
    have hj0 : (0 : ℝ) ≤ j0 T := Nat.cast_nonneg _
    have h1 : ((j0 T * n : ℕ) : ℝ) ≤ (T1 T : ℝ) - 1 := by
      push_cast
      have : (j0 T : ℝ) * n ≤ (j0 T : ℝ) * (exp 1 * Gc L + 1) :=
        mul_le_mul_of_nonneg_left hn'.le hj0
      unfold Gc at this
      rw [hLdef] at this
      linarith
    have hT1 : 1 ≤ T1 T := by unfold T1; omega
    have : ((T1 T - 1 : ℕ) : ℝ) = (T1 T : ℝ) - 1 := by push_cast [Nat.cast_sub hT1]; ring
    rw [← this] at h1
    exact_mod_cast h1
  have key : ∀ N, N = T1 T + k0 T →
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin N → ℝ),
        (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i t, 0 ≤ x i t) ∧
        (∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) ∧
        ∀ Lrn : Learner N, bT T ≤ ∑ i, w i * regret Lrn (x i) (y i) := by
    rintro N rfl
    obtain ⟨ι, hι, w, x, y, h1, h2, h3, h4, h5⟩ := adv_core hL (m := T1 T) (k := k0 T)
      (j := j0 T) (n := n) (by unfold T1; omega) hn hjn (C3 hT) (B0_nonneg hT)
    exact ⟨ι, hι, w, x, y, h1, h2, h3, h4, fun Lrn => by
      have := h5 Lrn
      rw [bT_eq_B0]
      exact this⟩
  exact key T (by unfold k0 T1; omega)

/-- **The paper, Theorem 4.1, on one play**, for every `B > 0`. -/
theorem lowerSharpBound : LowerSharpBound := by
  intro B hB T hT Lrn
  obtain ⟨ι, hι, w, x, y, hw, hs, -, hy, hb⟩ := lowerSharpAdv T hT
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => regret (rescale Lrn B) (x i) (y i)) Finset.univ_nonempty
  have h1 := hb (rescale Lrn B)
  have h2 : ∑ j, w j * regret (rescale Lrn B) (x j) (y j) ≤ regret (rescale Lrn B) (x i) (y i) := by
    calc ∑ j, w j * regret (rescale Lrn B) (x j) (y j)
        ≤ ∑ j, w j * regret (rescale Lrn B) (x i) (y i) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (hw j)
      _ = regret (rescale Lrn B) (x i) (y i) := by rw [← Finset.sum_mul, hs, one_mul]
  refine ⟨x i, fun t => B * y i t, fun t => ?_, ?_⟩
  · have := hy i t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    show |B * y i t| ≤ B
    rcases this with h | h | h <;> rw [h] <;> simp [abs_of_pos hB, hB.le]
  · rw [regret_rescale Lrn hB.ne' (x i) (y i)]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg B)

end RegretKappa.LowerSharp
