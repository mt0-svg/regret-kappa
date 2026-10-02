import RegretKappa.Lower.Adversary
import RegretKappa.Lower.Phase2

/-!
# Lower bound: assembly

The paper, Section 4.5, with the simplifications of this library. The adversary of
`Lower/Adversary.lean` at level `L` and radius `rad L = √(L + 1) + 2` is randomized: phase-1 signs
`ξ` uniform, a prior variable `z` with density `prior` on `[-2, 2]`, phase-2 signs `η` with law
`lik` given `z`. The expected regret `expReg` is an average over `ξ` of one interval integral of a
finite sum over `η`; a learner is deterministic, so its regret on each play is a number, and some
play does at least as well as the average (`exists_ge_expReg`).

* `expReg_ge`: given `ξ`, the expected regret is at least `P₁(ξ) + ρ² - 4/7 + ∑ ε_i² / W_i`
  (`regret_ge`, `phase2`), with `P₁` the phase-1 part `∑_{t<m} (ŷ_t² - 2 ŷ_t y_t)`;
* `avg_P1_nonneg`: `E P₁ ≥ 0` (the sign of round `t` is a fair coin that `ŷ_t` does not see,
  Lemma 4.7 (3) of the paper);
* `avg_rhoF_sq`: `E ρ² ≥ L (1 - 16 e^{(L+1)/2} / (m - 1))` (`ex_below_le`);
* `core`: every learner has regret at least `lbound L m k` on some play with outcomes in
  `[-1, 1]`; `eventually_lbound`: with `m = T/2`, `k = T - m` and `L = 2 log T - 4 log log T`,
  `lbound ≥ (3 - ε) log T` for large `T`; `lowerBound`: rescaling by `B`.
-/

namespace RegretKappa.Lower

open Finset Real Filter

/-- The radius of phase 2 at level `L`. -/
noncomputable def rad (L : ℝ) : ℝ := √(L + 1) + 2

theorem abs_rhoF_add_le {L : ℝ} (hL : 0 < L) {m : ℕ} (ξ : Fin m → Bool) :
    |rhoF L ξ| + 2 ≤ rad L := by
  have h := rho1_sq_lt hL (ext ξ) (m - 1)
  have : |rhoF L ξ| < √(L + 1) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
    exact h
  unfold rad
  linarith

/-- The phase-2 weights times a function of the signs are continuous in `z`. -/
theorem continuous_weighted {k : ℕ} (α β : Fin k → ℝ) (F : (Fin k → Bool) → ℝ) :
    Continuous fun z => ∑ η, prior z * lik α β η z * F η :=
  continuous_finsetSum _ fun η _ => (continuous_prior.mul (continuous_lik α β η)).mul continuous_const

/-- The weights `∑_η prior z lik(η | z)` integrate to `1`, for any parameters. -/
theorem integral_weights {k : ℕ} (α β : Fin k → ℝ) (c : ℝ) :
    ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik α β η z * c = c := by
  have h : ∀ z, ∑ η, prior z * lik α β η z * c = c * prior z := fun z => by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_lik, mul_one, mul_comm]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_prior, mul_one]

/-- The phase-2 weights are nonnegative on `[-2, 2]`. -/
theorem weight_nonneg {L : ℝ} (hL : 0 < L) {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool)
    {z : ℝ} (hz : z ∈ Set.Icc (-2 : ℝ) 2) :
    0 ≤ prior z * lik (fun l => rhoF L ξ * eps k (rad L) l) (fun l => eps k (rad L) l) η z := by
  refine mul_nonneg (prior_nonneg z) (lik_nonneg (fun l => ?_) η)
  rw [show rhoF L ξ * eps k (rad L) l + eps k (rad L) l * z = (rhoF L ξ + z) * eps k (rad L) l by
    ring]
  refine (abs_mean_le (abs_rhoF_add_le hL ξ) l hz).trans ?_
  rw [Real.sqrt_le_one]
  linarith [nu2_le_half l.isLt]

/-- The expected regret given the phase-1 signs `ξ`. -/
noncomputable def expReg (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool) : ℝ :=
  ∫ z in (-2 : ℝ)..2, ∑ η, prior z *
    lik (fun l => rhoF L ξ * eps k (rad L) l) (fun l => eps k (rad L) l) η z *
      regret Lrn (xA L (rad L) k ξ) (yA ξ η)

/-- The phase-1 part of the regret, `∑_{t<m} (ŷ_t² - 2 ŷ_t y_t)`. -/
noncomputable def P1 (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool) : ℝ :=
  ∑ t : Fin m, (pred L (rad L) Lrn ξ (fun _ => false) (Fin.castAdd k t) ^ 2 -
    2 * pred L (rad L) Lrn ξ (fun _ => false) (Fin.castAdd k t) * sgn (ξ t))

theorem expReg_ge {L : ℝ} (hL : 0 < L) {m k : ℕ} (hm : 1 ≤ m) (Lrn : Learner (m + k))
    (ξ : Fin m → Bool) :
    P1 L Lrn ξ + rhoF L ξ ^ 2 +
        (-(4 / 7) + ∑ i ∈ range k, eps k (rad L) i ^ 2 / wInfo k (rad L) i) ≤
      expReg L Lrn ξ := by
  have hr := abs_rhoF_add_le hL ξ
  have hph := phase2 hr (fun i η => pred L (rad L) Lrn ξ η (Fin.natAdd m i))
    (fun i η η' h => pred_natAdd_congr L (rad L) Lrn ξ i h)
  set α : Fin k → ℝ := fun l => rhoF L ξ * eps k (rad L) l with hα
  set β : Fin k → ℝ := fun l => eps k (rad L) l with hβ
  set c := P1 L Lrn ξ + rhoF L ξ ^ 2 with hc
  set Q : (Fin k → Bool) → ℝ → ℝ := fun η z => -z ^ 2 + ∑ i : Fin k,
    ((pred L (rad L) Lrn ξ η (Fin.natAdd m i) - sgn (η i)) ^ 2 -
      ((rhoF L ξ + z) * eps k (rad L) i - sgn (η i)) ^ 2) with hQ
  have hP1 : ∀ η : Fin k → Bool, ∑ t : Fin m, (pred L (rad L) Lrn ξ η (Fin.castAdd k t) ^ 2 -
      2 * pred L (rad L) Lrn ξ η (Fin.castAdd k t) * sgn (ξ t)) = P1 L Lrn ξ := fun η => by
    unfold P1
    exact Finset.sum_congr rfl fun t _ => by
      rw [pred_castAdd_congr L (rad L) Lrn ξ η (fun _ => false) t]
  have hcQ : Continuous fun z => ∑ η, prior z * lik α β η z * Q η z := by
    simp only [hQ]
    fun_prop
  have hsplit : ∀ z, ∑ η, prior z * lik α β η z * (c + Q η z) =
      c * prior z + ∑ η, prior z * lik α β η z * Q η z := fun z => by
    have hs := sum_lik α β z
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    calc ∑ η, prior z * lik α β η z * c = c * prior z * ∑ η, lik α β η z := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun η _ => by ring
      _ = c * prior z := by rw [hs, mul_one]
  have hint : ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik α β η z * (c + Q η z) =
      c + ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik α β η z * Q η z := by
    simp_rw [hsplit]
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun z => c * prior z).intervalIntegrable _ _)
      (hcQ.intervalIntegrable _ _), intervalIntegral.integral_const_mul, integral_prior, mul_one]
  have hmono : ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik α β η z * (c + Q η z) ≤ expReg L Lrn ξ := by
    unfold expReg
    apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
    · exact (by simp only [hQ]; fun_prop :
        Continuous fun z => ∑ η, prior z * lik α β η z * (c + Q η z)).intervalIntegrable _ _
    · exact (continuous_weighted (k := k) _ _ _).intervalIntegrable _ _
    · intro z hz
      refine Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hL ξ η hz)
      have := regret_ge L (rad L) hm Lrn ξ η z
      rw [hP1 η] at this
      simp only [hc, hQ]
      linarith
  have : -(4 / 7) + ∑ i ∈ range k, eps k (rad L) i ^ 2 / wInfo k (rad L) i ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik α β η z * Q η z := hph
  linarith

theorem avg_P1_nonneg (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) : 0 ≤ avg m (P1 L Lrn) := by
  unfold P1
  rw [avg_sum]
  refine Finset.sum_nonneg fun t _ => ?_
  have h0 : avg m (fun ξ => 2 * pred L (rad L) Lrn ξ (fun _ => false) (Fin.castAdd k t) *
      sgn (ξ t)) = 0 := avg_eq_zero_of_flipAt t _ fun ξ => by
    rw [pred_castAdd_flipAt, flipAt_self, sgn_not]
    ring
  rw [avg_sub, h0, sub_zero]
  exact avg_nonneg fun ξ => sq_nonneg _

theorem avg_rhoF_sq {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 2 ≤ m) :
    L * (1 - 16 * exp ((L + 1) / 2) / ((m - 1 : ℕ) : ℝ)) ≤ avg m (fun ξ => rhoF L ξ ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  simp only [Nat.add_sub_cancel]
  have hb : ∀ b : Bool, avg n (fun ξ => below L (rhoF L (Fin.cons b ξ : Fin (n + 1) → Bool))) ≤
      16 * exp ((L + 1) / 2) / n := fun b => by
    have h1 : ∀ ξ : Fin n → Bool, rhoF L (Fin.cons b ξ : Fin (n + 1) → Bool) =
        chainOf (sstep L) (sgn b) (ext ξ) n := fun ξ => by
      unfold rhoF
      rw [Nat.add_sub_cancel, rho1_eq_chainOf, ext_cons]
      rfl
    simp_rw [h1]
    rw [avg_chainOf]
    exact ex_below_le L hn (by rw [sgn_sq]; linarith)
  have hP : avg (n + 1) (fun ξ => below L (rhoF L ξ)) ≤ 16 * exp ((L + 1) / 2) / n := by
    rw [avg_cons]
    linarith [hb true, hb false]
  have hpt : ∀ ξ : Fin (n + 1) → Bool, L * 1 - L * below L (rhoF L ξ) ≤ rhoF L ξ ^ 2 := fun ξ => by
    unfold below
    split_ifs with h
    · nlinarith [sq_nonneg (rhoF L ξ)]
    · linarith [not_lt.1 h]
  have := avg_mono hpt
  rw [avg_sub, avg_mul_left, avg_mul_left, avg_const] at this
  nlinarith

theorem exists_ge_expReg {L : ℝ} (hL : 0 < L) {m k : ℕ} (Lrn : Learner (m + k)) :
    ∃ (ξ : Fin m → Bool) (η : Fin k → Bool),
      avg m (expReg L Lrn) ≤ regret Lrn (xA L (rad L) k ξ) (yA ξ η) := by
  obtain ⟨ξ, hξ⟩ := exists_avg_le m (expReg L Lrn)
  obtain ⟨η, -, hη⟩ := Finset.exists_max_image Finset.univ
    (fun η => regret Lrn (xA L (rad L) k ξ) (yA ξ η)) Finset.univ_nonempty
  refine ⟨ξ, η, hξ.trans ?_⟩
  unfold expReg
  rw [← integral_weights (fun l => rhoF L ξ * eps k (rad L) l) (fun l => eps k (rad L) l)
    (regret Lrn (xA L (rad L) k ξ) (yA ξ η))]
  apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
  · exact (continuous_weighted (k := k) _ _ _).intervalIntegrable _ _
  · exact (continuous_weighted (k := k) _ _ _).intervalIntegrable _ _
  · intro z hz
    exact Finset.sum_le_sum fun η' _ =>
      mul_le_mul_of_nonneg_left (hη η' (Finset.mem_univ _)) (weight_nonneg hL ξ η' hz)

/-- The lower bound forced at level `L` on `m + k` rounds. -/
noncomputable def lbound (L : ℝ) (m k : ℕ) : ℝ :=
  L * (1 - 16 * exp ((L + 1) / 2) / ((m - 1 : ℕ) : ℝ)) +
    (log (k / (10 * rad L ^ 2)) * (1 - 1 / (2 * k)) - 1) - 4 / 7

/-- **The bound at a fixed horizon.** -/
theorem core {L : ℝ} (hL : 0 < L) {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (Lrn : Learner (m + k)) :
    ∃ x y : Fin (m + k) → ℝ, (∀ t, |y t| ≤ 1) ∧ lbound L m k ≤ regret Lrn x y := by
  obtain ⟨ξ, η, h⟩ := exists_ge_expReg hL Lrn
  refine ⟨xA L (rad L) k ξ, yA ξ η, abs_yA ξ η, le_trans ?_ h⟩
  have hrad : 0 < rad L := by unfold rad; positivity
  have hcf := closedForm hk hrad
  have h1 := avg_mono fun ξ => expReg_ge hL (by omega : 1 ≤ m) Lrn ξ
  rw [avg_add, avg_add, avg_const] at h1
  have h2 := avg_P1_nonneg L Lrn
  have h3 := avg_rhoF_sq hL hm
  unfold lbound
  linarith

/-- The level of phase 1 at horizon `T`. -/
noncomputable def level (T : ℕ) : ℝ := 2 * log T - 4 * log (log T)

/-- `log u ≤ c u` for large `u`, any `c > 0`. -/
theorem eventually_log_le {c : ℝ} (hc : 0 < c) : ∀ᶠ u : ℝ in atTop, log u ≤ c * u := by
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc, eventually_ge_atTop 1] with u hu hu1
  have h0 : 0 ≤ log u := Real.log_nonneg hu1
  simpa [Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)] using hu

/-- The bound in terms of `u = log T`. -/
theorem lbound_ge {T : ℕ} (hT : 8 ≤ T) {u : ℝ} (hu : u = log T) (hu1 : 256 ≤ u)
    (hlog : log u ≤ u / 10) :
    3 * u - 6 * log u - 4 ≤ lbound (level T) (T / 2) (T - T / 2) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hu0 : 0 < u := by linarith
  have hlu : 0 ≤ log u := Real.log_nonneg (by linarith)
  set L := level T with hL
  have hLu : L = 2 * u - 4 * log u := by rw [hL, level, hu]
  have hL0 : 0 ≤ L := by rw [hLu]; linarith
  have hL2 : L ≤ 2 * u := by rw [hLu]; linarith
  -- the failure term
  have hexp : exp ((L + 1) / 2) = exp (1 / 2) * T / u ^ 2 := by
    have e1 : (L + 1) / 2 = log T - log (u ^ 2) + 1 / 2 := by
      rw [hLu, Real.log_pow, hu]; push_cast; ring
    rw [e1, Real.exp_add, Real.exp_sub, Real.exp_log hT0, Real.exp_log (by positivity)]
    ring
  have hm : (T : ℝ) ≤ 4 * ((T / 2 - 1 : ℕ) : ℝ) := by
    have : T ≤ 4 * (T / 2 - 1) := by omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) < ((T / 2 - 1 : ℕ) : ℝ) := by
    have : 0 < T / 2 - 1 := by omega
    exact_mod_cast this
  have he : exp (1 / 2 : ℝ) ≤ 2 := by
    have h1 : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hx : 16 * exp ((L + 1) / 2) / ((T / 2 - 1 : ℕ) : ℝ) ≤ 128 / u ^ 2 := by
    rw [hexp, div_le_div_iff₀ hm0 (by positivity)]
    have : exp (1 / 2) * T ≤ 2 * T := mul_le_mul_of_nonneg_right he hT0.le
    calc 16 * (exp (1 / 2) * ↑T / u ^ 2) * u ^ 2 = 16 * (exp (1 / 2) * T) := by
          field_simp
      _ ≤ 16 * (2 * T) := by linarith
      _ ≤ 128 * ((T / 2 - 1 : ℕ) : ℝ) := by linarith
  have hx0 : 0 ≤ 16 * exp ((L + 1) / 2) / ((T / 2 - 1 : ℕ) : ℝ) := by positivity
  have hfirst : L - 1 ≤ L * (1 - 16 * exp ((L + 1) / 2) / ((T / 2 - 1 : ℕ) : ℝ)) := by
    have h1 : L * (16 * exp ((L + 1) / 2) / ((T / 2 - 1 : ℕ) : ℝ)) ≤ 2 * u * (128 / u ^ 2) :=
      mul_le_mul hL2 hx hx0 (by linarith)
    have h2 : 2 * u * (128 / u ^ 2) ≤ 1 := by
      rw [show 2 * u * (128 / u ^ 2) = 256 / u by field_simp; ring, div_le_one hu0]
      exact hu1
    nlinarith
  -- the phase-2 term
  have hrad : rad L ^ 2 ≤ 4 * u + 10 := by
    have ha : √(L + 1) ^ 2 = L + 1 := Real.sq_sqrt (by linarith)
    unfold rad
    nlinarith [sq_nonneg (√(L + 1) - 2)]
  have hrad0 : 4 ≤ rad L ^ 2 := by
    unfold rad
    nlinarith [Real.sqrt_nonneg (L + 1)]
  have hk : (T : ℝ) / 2 ≤ ((T - T / 2 : ℕ) : ℝ) := by
    have : T ≤ 2 * (T - T / 2) := by omega
    have : (T : ℝ) ≤ 2 * ((T - T / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hk0 : (0 : ℝ) < ((T - T / 2 : ℕ) : ℝ) := by linarith
  set k : ℝ := ((T - T / 2 : ℕ) : ℝ) with hkdef
  have hΛlow : u - 2 * log u ≤ log (k / (10 * rad L ^ 2)) := by
    have h1 : (T : ℝ) / (20 * (4 * u + 10)) ≤ k / (10 * rad L ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : log ((T : ℝ) / (20 * (4 * u + 10))) = u - log (20 * (4 * u + 10)) := by
      rw [Real.log_div hT0.ne' (by positivity), hu]
    have h3 : log (20 * (4 * u + 10)) ≤ 2 * log u := by
      have e2 : 2 * log u = log (u ^ 2) := by rw [Real.log_pow]; norm_num
      rw [e2]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have h4 := Real.log_le_log (by positivity) h1
    linarith
  have hΛup : log (k / (10 * rad L ^ 2)) ≤ k := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < k / (10 * rad L ^ 2) by positivity)
    have h2 : k / (10 * rad L ^ 2) ≤ k := div_le_self hk0.le (by nlinarith)
    linarith
  have hsecond : log (k / (10 * rad L ^ 2)) - 1 / 2 ≤
      log (k / (10 * rad L ^ 2)) * (1 - 1 / (2 * k)) := by
    have : log (k / (10 * rad L ^ 2)) / (2 * k) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have e : log (k / (10 * rad L ^ 2)) * (1 - 1 / (2 * k)) =
        log (k / (10 * rad L ^ 2)) - log (k / (10 * rad L ^ 2)) / (2 * k) := by ring
    linarith
  unfold lbound
  linarith

/-- The asymptotics of the bound. -/
theorem eventually_lbound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, 2 ≤ T / 2 ∧ 0 < level T ∧
      (3 - ε) * log T ≤ lbound (level T) (T / 2) (T - T / 2) := by
  have hu : Tendsto (fun T : ℕ => log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hU : ∀ᶠ u : ℝ in atTop, 256 ≤ u ∧ log u ≤ u / 10 ∧ 6 * log u + 4 ≤ ε * u := by
    filter_upwards [eventually_ge_atTop (256 : ℝ), eventually_ge_atTop (8 / ε),
      eventually_log_le (show (0 : ℝ) < 1 / 10 by norm_num),
      eventually_log_le (show 0 < ε / 12 by positivity)] with u h1 h2 h3 h4
    refine ⟨h1, by linarith, ?_⟩
    have : 8 ≤ ε * u := by rwa [div_le_iff₀ hε, mul_comm] at h2
    linarith
  filter_upwards [hu.eventually hU, eventually_ge_atTop 8] with T ⟨h1, h2, h3⟩ hT
  refine ⟨by omega, ?_, ?_⟩
  · rw [level]; linarith
  · have := lbound_ge hT rfl h1 h2
    linarith

/-- The lower bound for outcomes in `[-1, 1]`. -/
theorem lowerBound_one {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, ∀ Lrn : Learner T,
      ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ 1) ∧ (3 - ε) * log T ≤ regret Lrn x y := by
  filter_upwards [eventually_lbound hε] with T ⟨hm, hL, hb⟩
  intro Lrn
  have key : ∀ n, n = T / 2 + (T - T / 2) → ∀ Lrn : Learner n, ∃ x y : Fin n → ℝ,
      (∀ t, |y t| ≤ 1) ∧ lbound (level T) (T / 2) (T - T / 2) ≤ regret Lrn x y := by
    rintro n rfl Lrn
    exact core hL hm (by omega) Lrn
  obtain ⟨x, y, hy, h⟩ := key T (by omega) Lrn
  exact ⟨x, y, hy, hb.trans h⟩

/-- **The lower bound `LowerBound`.** -/
theorem lowerBound : LowerBound := by
  intro B hB ε hε
  filter_upwards [lowerBound_one hε] with T hT
  intro Lrn
  obtain ⟨x, y, hy, h⟩ := hT (rescale Lrn B)
  refine ⟨x, fun t => B * y t, fun t => ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hB]
    nlinarith [hy t]
  · rw [regret_rescale Lrn hB.ne' x y]
    calc (3 - ε) * B ^ 2 * log T = B ^ 2 * ((3 - ε) * log T) := by ring
      _ ≤ B ^ 2 * regret (rescale Lrn B) x y := mul_le_mul_of_nonneg_left h (sq_nonneg B)

end RegretKappa.Lower
