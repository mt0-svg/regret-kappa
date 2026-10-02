import RegretKappa.Lower.Assembly
import RegretKappa.Corollaries.Transfer
import RegretKappa.Corollaries.Expectation

/-!
# The adversary of `Lower` as a finite mixture of plays

The adversary of `RegretKappa.Lower` at level `L` on `m + k` rounds ignores the predictions, and
its play `(xA ξ, yA ξ η)` is a function of the phase-1 signs `ξ` and the phase-2 signs `η` only.
The expected regret `avg m (expReg L Lrn)` of a learner is the average of its regrets on these
plays, weighted by `wt L (ξ, η) = 2^{-m} ∫_{-2}^{2} prior z lik(η | z) dz` (`avg_expReg_eq`); the
weights are nonnegative (`wt_nonneg`) and sum to `1` (`sum_wt`), and the first half of the proof
of `Lower.core` bounds the average below by `lbound L m k` (`lbound_le_avg`).

The features are nonnegative (`xA_nonneg`) and the outcomes are signs (`yA_mem`), so `transfer`
moves the bound to plays with features in `[0, 1]` and outcomes in `{-B, 0, B}`: for every learner
the weighted regret on these plays is at least `B ^ 2 lbound L m k` (`mixture`), and with
`eventually_lbound` and `le_advRegret` this proves the paper's Corollary 5.1, the adversary
(`boundedFeaturesAdv`).
-/

namespace RegretKappa.Corollaries

open MeasureTheory Filter RegretKappa.Lower

universe u

/-- The average over the phase-1 signs of an interval integral of a finite sum over the phase-2
signs is a finite weighted sum over both. -/
theorem avg_integral_sum {m k : ℕ} (g : (Fin m → Bool) → (Fin k → Bool) → ℝ → ℝ)
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
  rw [hsum]
  have hRHS : (∑ p : (Fin m → Bool) × (Fin k → Bool), (∫ z in (-2 : ℝ)..2, g p.1 p.2 z) / 2 ^ m * r p.1 p.2) =
      (∑ p : (Fin m → Bool) × (Fin k → Bool), ((∫ z in (-2 : ℝ)..2, g p.1 p.2 z) * r p.1 p.2) / 2 ^ m) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_mul_eq_mul_div]
  rw [hRHS, Finset.sum_div]

/-- The features of the adversary of `Lower` are nonnegative. -/
theorem xA_nonneg (L r : ℝ) {m : ℕ} (k : ℕ) (ξ : Fin m → Bool) (t : Fin (m + k)) :
    0 ≤ xA L r k ξ t := by
  have hx1 : ∀ n : ℕ, 0 ≤ x1 L (ext ξ) n := by
    intro n
    cases n with
    | zero => simp [x1]
    | succ n => simp [x1]
  have heps : ∀ (k' : ℕ) (r' : ℝ) (i : Fin k'), 0 ≤ eps k' r' i := by
    intro k' r' i
    unfold eps
    exact Real.sqrt_nonneg _
  refine Fin.addCases (fun i => ?_) (fun j => ?_) t
  · -- i : Fin m, t = Fin.castAdd k i
    have := hx1 (i : ℕ)
    simpa [xA, Fin.append] using this
  · -- j : Fin k, t = Fin.natAdd m j
    have h1 : 0 ≤ eps k r j := heps k r j
    have h2 : 0 ≤ √(VF L ξ) := Real.sqrt_nonneg _
    have := mul_nonneg h1 h2
    simpa [xA, Fin.append] using this

/-- The outcomes of the adversary of `Lower` are signs. -/
theorem yA_mem {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) (t : Fin (m + k)) :
    yA ξ η t = 1 ∨ yA ξ η t = -1 := by
  have hs : ∀ b : Bool, sgn b = 1 ∨ sgn b = -1 := fun b => by
    cases b <;> simp [sgn]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) t
  · simp only [yA, Fin.append_left]
    exact hs _
  · simp only [yA, Fin.append_right]
    exact hs _

/-- The probability of the play `(xA ξ, yA ξ η)` under the adversary of `Lower` at level `L`. -/
noncomputable def wt (L : ℝ) {m k : ℕ} (p : (Fin m → Bool) × (Fin k → Bool)) : ℝ :=
  (∫ z in (-2 : ℝ)..2,
    prior z * lik (fun l => rhoF L p.1 * eps k (rad L) l) (fun l => eps k (rad L) l) p.2 z) / 2 ^ m

theorem continuous_wt_integrand (L : ℝ) {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) :
    Continuous fun z =>
      prior z * lik (fun l => rhoF L ξ * eps k (rad L) l) (fun l => eps k (rad L) l) η z :=
  continuous_prior.mul (continuous_lik _ _ η)

theorem wt_nonneg {L : ℝ} (hL : 0 < L) {m k : ℕ} (p : (Fin m → Bool) × (Fin k → Bool)) :
    0 ≤ wt L p :=
  div_nonneg (intervalIntegral.integral_nonneg (by norm_num) fun _ hz =>
    weight_nonneg hL p.1 p.2 hz) (by positivity)

/-- The expected regret against the adversary of `Lower` is the weighted average of the regrets on
its plays. -/
theorem avg_expReg_eq (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) :
    avg m (expReg L Lrn) =
      ∑ p : (Fin m → Bool) × (Fin k → Bool),
        wt L p * regret Lrn (xA L (rad L) k p.1) (yA p.1 p.2) :=
  avg_integral_sum _ (continuous_wt_integrand L) _

theorem sum_wt (L : ℝ) (m k : ℕ) : ∑ p : (Fin m → Bool) × (Fin k → Bool), wt L p = 1 := by
  have h := avg_integral_sum _ (continuous_wt_integrand (m := m) (k := k) L) fun _ _ => 1
  simp only [mul_one] at h
  have h1 : ∀ ξ : Fin m → Bool, ∫ z in (-2 : ℝ)..2, ∑ η : Fin k → Bool,
      prior z * lik (fun l => rhoF L ξ * eps k (rad L) l) (fun l => eps k (rad L) l) η z = 1 :=
    fun ξ => by simpa only [mul_one] using integral_weights (k := k) _ _ 1
  simp only [h1, avg_const] at h
  exact h.symm

/-- The first half of the proof of `Lower.core`: the expected regret against the adversary of
`Lower` is at least `lbound L m k`. -/
theorem lbound_le_avg {L : ℝ} (hL : 0 < L) {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (Lrn : Learner (m + k)) : lbound L m k ≤ avg m (expReg L Lrn) := by
  have hrad : 0 < rad L := by unfold rad; positivity
  have hcf := closedForm hk hrad
  have h1 := avg_mono fun ξ => expReg_ge hL (by omega : 1 ≤ m) Lrn ξ
  rw [avg_add, avg_add, avg_const] at h1
  have h2 := avg_P1_nonneg L Lrn
  have h3 := avg_rhoF_sq hL hm
  unfold lbound
  linarith

/-- **The bound at a fixed horizon, against a finite mixture of plays.** -/
theorem mixture {L : ℝ} (hL : 0 < L) {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) {B : ℝ} (hB : 0 < B) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin (m + k) → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ Lrn : Learner (m + k), B ^ 2 * lbound L m k ≤ ∑ i, w i * regret Lrn (x i) (y i) := by
  have hy : ∀ (p : (Fin m → Bool) × (Fin k → Bool)) (t : Fin (m + k)),
      yA p.1 p.2 t ∈ ({-1, 0, 1} : Set ℝ) := fun p t => by
    rcases yA_mem p.1 p.2 t with h | h <;> simp [h]
  obtain ⟨x, y, hx, hy, h⟩ := transfer (wt L) (fun p => xA L (rad L) k p.1) (fun p => yA p.1 p.2)
    (fun p t => xA_nonneg _ _ _ p.1 t) hy
    (fun Lrn => (lbound_le_avg hL hm hk Lrn).trans_eq (avg_expReg_eq L Lrn)) hB
  exact ⟨_, inferInstance, wt L, x, y, wt_nonneg hL, sum_wt L m k, hx, hy, h⟩

/-- **The paper, Corollary 5.1, the adversary.** -/
theorem boundedFeaturesAdv : BoundedFeaturesAdv.{u} := by
  intro B hB ε hε
  filter_upwards [eventually_lbound hε] with T ⟨hm, hL, hb⟩
  have key : ∀ n, n = T / 2 + (T - T / 2) →
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin n → ℝ),
        (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
        (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
        ∀ Lrn : Learner n, B ^ 2 * lbound (level T) (T / 2) (T - T / 2) ≤
          ∑ i, w i * regret Lrn (x i) (y i) := by
    rintro n rfl
    exact mixture hL hm (by omega) hB
  obtain ⟨ι, hι, w, x, y, hw, hs, hx, hy, h⟩ := key T (by omega)
  refine ⟨ι, hι, w, x, y, hw, hs, hx, hy, fun Ω _ μ L hL' => ?_⟩
  have := hL'.1
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (le_advRegret μ L w hw x y _ fun ω => h (L ω))
  calc (3 - ε) * B ^ 2 * Real.log T = B ^ 2 * ((3 - ε) * Real.log T) := by ring
    _ ≤ B ^ 2 * lbound (level T) (T / 2) (T - T / 2) := mul_le_mul_of_nonneg_left hb (sq_nonneg B)

end RegretKappa.Corollaries
