import RegretKappa.Lower.Hitting
import RegretKappa.Lower.ClosedForm
import RegretKappa.Lower.Identity

/-!
# Lower bound: the adversary and its play

The adversary of the paper, Section 4.2, with the simplifications of this library, on
`m + k` rounds: phase 1 is rounds `0, ..., m - 1`, phase 2 is rounds `m, ..., m + k - 1`.

* Phase 1, signs `ξ : Fin m → Bool`, `ζ = ext ξ`. Round `0`: feature `1`, outcome `sgn ξ₀`. Round
  `t + 1`: with `s = smv L ρ_t` (the move stopped at level `L`), feature
  `x_{t+1} = √(V_t s / (1 - s))` and outcome `sgn ξ_{t+1}`. Then `V_{t+1} = V_t / (1 - s)` and
  `ρ_{t+1} = sstep L ρ_t ξ_{t+1}` (Lemma 4.2 of the paper): `S_t = ρ_t √V_t` (`sum_x1_mul`) and
  `V_t = ∑_{s ≤ t} x_s²` (`sum_x1_sq`). Once `ρ² ≥ L` the move is `0`: the feature is `0` and the
  state stays put, which replaces the stopping time of the paper.
* Phase 2, signs `η : Fin k → Bool`, round `m + i`: feature `ε_i √V` (`ε_i = eps k r i`,
  `V = V_{m-1}`), outcome `sgn η_i`. Their law (`lik` of `Lower/Model.lean`, the prior of
  `Lower/VanTrees.lean`) enters only in `Lower/Assembly.lean`.

`regret_ge` is the regret identity in the form used: for every `z`,
`Regret ≥ ∑_{t < m} (ŷ_t² - 2 ŷ_t y_t) + ρ² - z² + ∑_i ((ŷ_{m+i} - y_{m+i})² - ((ρ + z) ε_i - y_{m+i})²)`
(Lemmas 2.2 and 4.8 of the paper with `θ* √V = ρ + z`, the term `V_T (θ* - θ̂_T)² ≥ 0` dropped).
The causality lemmas say which signs each prediction sees.
-/

namespace RegretKappa.Lower

open Finset Real

/-- The phase-1 statistic `ρ_t = S_t / √V_t` after round `t`, from the signs `ζ`. -/
noncomputable def rho1 (L : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => sgn (ζ 0)
  | t + 1 => sstep L (rho1 L ζ t) (ζ (t + 1))

/-- `V_t`, the sum of the squared features up to round `t`. -/
noncomputable def V1 (L : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | t + 1 => V1 L ζ t / (1 - smv L (rho1 L ζ t))

/-- The phase-1 feature of round `t`. -/
noncomputable def x1 (L : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | t + 1 => √(V1 L ζ t * smv L (rho1 L ζ t) / (1 - smv L (rho1 L ζ t)))

theorem V1_pos (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) : 0 < V1 L ζ t := by
  induction t with
  | zero => simp [V1]
  | succ t ih =>
    simp only [V1]
    have := smv_le L (rho1 L ζ t)
    exact div_pos ih (by linarith)

-- TARGET

theorem sum_x1_sq (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) :
    ∑ s ∈ range (t + 1), x1 L ζ s ^ 2 = V1 L ζ t := by
  induction' t with t ih
  · simp [x1, V1]
  · rw [Finset.sum_range_succ, ih]
    have hVpos : 0 < V1 L ζ t := V1_pos L ζ t
    have hsn : 0 ≤ smv L (rho1 L ζ t) := smv_nonneg L _
    have hsl : smv L (rho1 L ζ t) ≤ 1 / 4 := smv_le L _
    have h_denom_pos : 0 < 1 - smv L (rho1 L ζ t) := by linarith
    have h_arg_nonneg : 0 ≤ V1 L ζ t * smv L (rho1 L ζ t) / (1 - smv L (rho1 L ζ t)) := by
      positivity
    rw [x1]
    rw [Real.sq_sqrt h_arg_nonneg]
    rw [V1]
    field_simp [h_denom_pos.ne.symm]
    ring

-- TARGET

/-- Lemma 4.2 of the paper: `S_t = ρ_t √V_t`. -/
theorem sum_x1_mul (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) :
    ∑ s ∈ range (t + 1), x1 L ζ s * sgn (ζ s) = rho1 L ζ t * √(V1 L ζ t) := by
  induction t with
  | zero =>
    simp [x1, rho1, V1]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp [x1, rho1, V1, sstep]
    have hV : 0 ≤ V1 L ζ t := (V1_pos L ζ t).le
    have hs_nonneg : 0 ≤ smv L (rho1 L ζ t) := smv_nonneg L (rho1 L ζ t)
    have hs_lt_one : smv L (rho1 L ζ t) < 1 := by
      have hle := smv_le L (rho1 L ζ t)
      linarith
    have h_one_minus_s_pos : 0 < 1 - smv L (rho1 L ζ t) := by linarith
    have h_one_minus_s_nonneg : 0 ≤ 1 - smv L (rho1 L ζ t) := by linarith
    set ρ := rho1 L ζ t
    set V := V1 L ζ t
    set s := smv L ρ
    set b := ζ (t + 1)
    have hsqrtV : √V * √(1 - s) = √(V * (1 - s)) := by
      rw [Real.sqrt_mul hV]
    have hsqrtVdiv : √(V / (1 - s)) * √(1 - s) = √V := by
      calc
        √(V / (1 - s)) * √(1 - s) = √(1 - s) * √(V / (1 - s)) := by rw [mul_comm]
        _ = √((1 - s) * (V / (1 - s))) := by rw [Real.sqrt_mul h_one_minus_s_nonneg]
        _ = √(V / (1 - s) * (1 - s)) := by rw [mul_comm]
        _ = √V := by field_simp [h_one_minus_s_pos.ne']
    have hsqrtVdiv_s : √(V / (1 - s)) * √s = √(V * s / (1 - s)) := by
      calc
        √(V / (1 - s)) * √s = √s * √(V / (1 - s)) := by rw [mul_comm]
        _ = √(s * (V / (1 - s))) := by rw [Real.sqrt_mul hs_nonneg]
        _ = √(V * s / (1 - s)) := by ring_nf
    calc
      ρ * √V + √(V * s / (1 - s)) * sgn b
          = ρ * (√(V / (1 - s)) * √(1 - s)) + (√(V / (1 - s)) * √s) * sgn b := by
        rw [hsqrtVdiv, hsqrtVdiv_s]
      _ = (ρ * √(1 - s) + sgn b * √s) * √(V / (1 - s)) := by ring

theorem rho1_eq_chainOf (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) :
    rho1 L ζ t = chainOf (sstep L) (sgn (ζ 0)) (fun i => ζ (i + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [rho1, ih]; rfl

theorem rho1_sq_lt {L : ℝ} (hL : 0 < L) (ζ : ℕ → Bool) (t : ℕ) : rho1 L ζ t ^ 2 < L + 1 := by
  induction t with
  | zero => simp only [rho1, sgn_sq]; linarith
  | succ t ih => exact sstep_sq_lt ih _

/-- `ρ_t` and `V_t` depend on the signs up to `t` only. -/
theorem rho1_V1_congr (L : ℝ) {ζ ζ' : ℕ → Bool} {t : ℕ} (h : ∀ i ≤ t, ζ i = ζ' i) :
    rho1 L ζ t = rho1 L ζ' t ∧ V1 L ζ t = V1 L ζ' t := by
  induction t with
  | zero => exact ⟨by simp [rho1, h 0 le_rfl], rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (by omega)
    refine ⟨?_, ?_⟩
    · simp only [rho1, h1, h (t + 1) le_rfl]
    · simp only [V1, h1, h2]

/-- The feature of round `t` depends on the signs before `t` only. -/
theorem x1_congr (L : ℝ) {ζ ζ' : ℕ → Bool} {t : ℕ} (h : ∀ i < t, ζ i = ζ' i) :
    x1 L ζ t = x1 L ζ' t := by
  cases t with
  | zero => rfl
  | succ t =>
    obtain ⟨h1, h2⟩ := rho1_V1_congr L (t := t) fun i hi => h i (by omega)
    simp only [x1, h1, h2]

/-- The final phase-1 statistic `ρ = ρ_{m-1}`. -/
noncomputable def rhoF (L : ℝ) {m : ℕ} (ξ : Fin m → Bool) : ℝ := rho1 L (ext ξ) (m - 1)

/-- The final `V = V_{m-1}`. -/
noncomputable def VF (L : ℝ) {m : ℕ} (ξ : Fin m → Bool) : ℝ := V1 L (ext ξ) (m - 1)

/-- The features of the play: phase 1, then phase 2. They do not depend on the phase-2 signs. -/
noncomputable def xA (L r : ℝ) {m : ℕ} (k : ℕ) (ξ : Fin m → Bool) : Fin (m + k) → ℝ :=
  Fin.append (fun t : Fin m => x1 L (ext ξ) t) (fun i : Fin k => eps k r i * √(VF L ξ))

/-- The outcomes of the play: the phase-1 signs, then the phase-2 signs. -/
noncomputable def yA {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) : Fin (m + k) → ℝ :=
  Fin.append (fun t : Fin m => sgn (ξ t)) (fun i : Fin k => sgn (η i))

theorem append_of_lt {α : Type*} {m k : ℕ} (u : Fin m → α) (v : Fin k → α) (s : Fin (m + k))
    (h : s.val < m) : Fin.append u v s = u ⟨s.val, h⟩ := by
  have e := Fin.append_left u v ⟨s.val, h⟩
  rwa [show Fin.castAdd k ⟨s.val, h⟩ = s from Fin.ext rfl] at e

theorem append_of_ge {α : Type*} {m k : ℕ} (u : Fin m → α) (v : Fin k → α) (s : Fin (m + k))
    (h : m ≤ s.val) : Fin.append u v s = v ⟨s.val - m, by omega⟩ := by
  have e := Fin.append_right u v ⟨s.val - m, by omega⟩
  rwa [show Fin.natAdd m ⟨s.val - m, by omega⟩ = s from Fin.ext (by simp; omega)] at e

theorem abs_yA {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) (t : Fin (m + k)) :
    |yA ξ η t| ≤ 1 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) t
  · simp [yA, abs_sgn]
  · simp [yA, abs_sgn]

/-- The prediction of the learner on the play. -/
noncomputable def pred (L r : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (t : Fin (m + k)) : ℝ :=
  Lrn.prediction (xA L r k ξ) (yA ξ η) t

/-- A phase-1 prediction ignores the phase-2 signs. -/
theorem pred_castAdd_congr (L r : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η η' : Fin k → Bool) (t : Fin m) :
    pred L r Lrn ξ η (Fin.castAdd k t) = pred L r Lrn ξ η' (Fin.castAdd k t) := by
  refine prediction_congr Lrn _ (fun s _ => rfl) fun s hs => ?_
  have hs' : s.val < m := lt_of_lt_of_le (Fin.lt_def.1 hs) (by simp [t.isLt.le])
  simp only [yA, append_of_lt _ _ s hs']

/-- A phase-1 prediction in round `t` ignores the sign of round `t`. -/
theorem pred_castAdd_flipAt (L r : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (t : Fin m) :
    pred L r Lrn (flipAt t ξ) η (Fin.castAdd k t) = pred L r Lrn ξ η (Fin.castAdd k t) := by
  refine prediction_congr Lrn _ (fun s hs => ?_) fun s hs => ?_
  · have hs1 : s.val ≤ t.val := by simpa [Fin.le_def] using hs
    have hs' : s.val < m := by omega
    simp only [xA, append_of_lt _ _ s hs']
    exact x1_congr L fun i hi => ext_flipAt_ne t ξ (by omega)
  · have hs1 : s.val < t.val := by simpa [Fin.lt_def] using hs
    have hs' : s.val < m := by omega
    simp only [yA, append_of_lt _ _ s hs']
    rw [flipAt_ne]
    intro e
    rw [← e] at hs1
    exact lt_irrefl _ hs1

/-- A phase-2 prediction in round `m + i` sees the phase-2 signs before `i` only. -/
theorem pred_natAdd_congr (L r : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (i : Fin k) {η η' : Fin k → Bool} (h : ∀ l : Fin k, l.val < i.val → η l = η' l) :
    pred L r Lrn ξ η (Fin.natAdd m i) = pred L r Lrn ξ η' (Fin.natAdd m i) := by
  refine prediction_congr Lrn _ (fun s _ => rfl) fun s hs => ?_
  have hs1 : s.val < m + i.val := by simpa [Fin.lt_def] using hs
  rcases lt_or_ge s.val m with h1 | h1
  · simp only [yA, append_of_lt _ _ s h1]
  · simp only [yA, append_of_ge _ _ s h1]
    rw [h _ (by simp; omega)]

/-- The pointwise algebra of the comparator: with `X = ∑ ε_i²`, `Y = ∑ ε_i y_i`,
`∑ (ŷ_i² - 2 ŷ_i y_i) + (ρ + Y)² / (1 + X) ≥ ρ² - z² + ∑ ((ŷ_i - y_i)² - ((ρ + z) ε_i - y_i)²)`. -/
theorem comparator_alg {k : ℕ} (ρ z : ℝ) (e yh y : Fin k → ℝ) :
    ρ ^ 2 - z ^ 2 + ∑ i, ((yh i - y i) ^ 2 - ((ρ + z) * e i - y i) ^ 2) ≤
      ∑ i, (yh i ^ 2 - 2 * yh i * y i) +
        (ρ + ∑ i, e i * y i) ^ 2 / (1 + ∑ i, e i ^ 2) := by
  set X := ∑ i : Fin k, e i ^ 2 with hX
  set Y := ∑ i : Fin k, e i * y i with hY
  set u := ρ + z with hu
  have hX_nonneg : 0 ≤ X := Finset.sum_nonneg (λ i _ => sq_nonneg (e i))
  have h_denom_pos : 0 < 1 + X := by linarith
  have h_denom_ne_zero : 1 + X ≠ 0 := by linarith
  have h_pointwise (i : Fin k) : ((yh i - y i) ^ 2 - ((u * e i - y i) ^ 2)) =
      ((yh i ^ 2 - 2 * yh i * y i) - ((u ^ 2 * e i ^ 2 - 2 * u * e i * y i))) := by
    ring
  have h_sum : (∑ i : Fin k, ((yh i - y i) ^ 2 - ((u * e i - y i) ^ 2))) =
      (∑ i : Fin k, (yh i ^ 2 - 2 * yh i * y i)) - (u ^ 2 * X - 2 * u * Y) := by
    calc
      (∑ i : Fin k, ((yh i - y i) ^ 2 - ((u * e i - y i) ^ 2))) =
          (∑ i : Fin k, ((yh i ^ 2 - 2 * yh i * y i) - ((u ^ 2 * e i ^ 2 - 2 * u * e i * y i)))) := by
        apply Finset.sum_congr rfl (λ i hi => h_pointwise i)
      _ = (∑ i : Fin k, (yh i ^ 2 - 2 * yh i * y i)) - (∑ i : Fin k, (u ^ 2 * e i ^ 2 - 2 * u * e i * y i)) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin k, (yh i ^ 2 - 2 * yh i * y i)) - (u ^ 2 * (∑ i : Fin k, e i ^ 2) - 2 * u * (∑ i : Fin k, e i * y i)) := by
        rw [sub_right_inj]
        simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = (∑ i : Fin k, (yh i ^ 2 - 2 * yh i * y i)) - (u ^ 2 * X - 2 * u * Y) := rfl
  rw [h_sum, hu]
  -- Goal: ρ^2 - z^2 + S - (u^2*X - 2*u*Y) ≤ S + (ρ+Y)^2/(1+X) where S = ∑ (yh i^2 - 2*yh i*y i)
  -- Cancel S from both sides; need: ρ^2 - z^2 - u^2*X + 2*u*Y ≤ (ρ+Y)^2/(1+X)
  have h_main : ρ ^ 2 - z ^ 2 - u ^ 2 * X + 2 * u * Y ≤ (ρ + Y) ^ 2 / (1 + X) := by
    have h_nonneg_sq : 0 ≤ (1 + X) * (u - (ρ + Y) / (1 + X)) ^ 2 := by
      have : 0 ≤ (u - (ρ + Y) / (1 + X)) ^ 2 := sq_nonneg _
      nlinarith
    have h_eq : (ρ + Y) ^ 2 / (1 + X) - (ρ ^ 2 - z ^ 2 - u ^ 2 * X + 2 * u * Y) =
        (1 + X) * (u - (ρ + Y) / (1 + X)) ^ 2 := by
      field_simp [h_denom_ne_zero]
      nlinarith [hu]
    linarith
  linarith

/-- **The regret identity on the play** (Lemmas 2.2 and 4.8 of the paper, `θ* √V = ρ + z`). -/
theorem regret_ge (L r : ℝ) {m k : ℕ} (hm : 1 ≤ m) (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (z : ℝ) :
    ∑ t : Fin m, (pred L r Lrn ξ η (Fin.castAdd k t) ^ 2 -
        2 * pred L r Lrn ξ η (Fin.castAdd k t) * sgn (ξ t)) + rhoF L ξ ^ 2 +
      (-z ^ 2 + ∑ i : Fin k, ((pred L r Lrn ξ η (Fin.natAdd m i) - sgn (η i)) ^ 2 -
        ((rhoF L ξ + z) * eps k r i - sgn (η i)) ^ 2)) ≤
      regret Lrn (xA L r k ξ) (yA ξ η) := by
  have hV : 0 < VF L ξ := V1_pos L (ext ξ) (m - 1)
  have hS : ∑ t : Fin m, x1 L (ext ξ) t * sgn (ξ t) = rhoF L ξ * √(VF L ξ) := by
    have h := sum_x1_mul L (ext ξ) (m - 1)
    rw [Nat.sub_add_cancel hm, ← Fin.sum_univ_eq_sum_range] at h
    simp only [rhoF, VF]
    simpa only [ext_fin] using h
  have hQ : ∑ t : Fin m, x1 L (ext ξ) t ^ 2 = VF L ξ := by
    have h := sum_x1_sq L (ext ξ) (m - 1)
    rwa [Nat.sub_add_cancel hm, ← Fin.sum_univ_eq_sum_range] at h
  have hS2 : ∑ i : Fin k, eps k r i * √(VF L ξ) * sgn (η i) =
      √(VF L ξ) * ∑ i : Fin k, eps k r i * sgn (η i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hQ2 : ∑ i : Fin k, (eps k r i * √(VF L ξ)) ^ 2 = VF L ξ * ∑ i : Fin k, eps k r i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt hV.le]; ring
  have hfrac : (rhoF L ξ * √(VF L ξ) + √(VF L ξ) * ∑ i : Fin k, eps k r i * sgn (η i)) ^ 2 /
      (VF L ξ + VF L ξ * ∑ i : Fin k, eps k r i ^ 2) =
      (rhoF L ξ + ∑ i : Fin k, eps k r i * sgn (η i)) ^ 2 / (1 + ∑ i : Fin k, eps k r i ^ 2) := by
    have hX : 0 ≤ ∑ i : Fin k, eps k r i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [show rhoF L ξ * √(VF L ξ) + √(VF L ξ) * ∑ i : Fin k, eps k r i * sgn (η i) =
      √(VF L ξ) * (rhoF L ξ + ∑ i : Fin k, eps k r i * sgn (η i)) by ring, mul_pow,
      Real.sq_sqrt hV.le, show VF L ξ + VF L ξ * ∑ i : Fin k, eps k r i ^ 2 =
      VF L ξ * (1 + ∑ i : Fin k, eps k r i ^ 2) by ring]
    exact mul_div_mul_left _ _ hV.ne'
  unfold pred
  rw [regret_eq, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  have h := comparator_alg (rhoF L ξ) z (fun i => eps k r i)
    (fun i => Lrn.prediction (xA L r k ξ) (yA ξ η) (Fin.natAdd m i)) (fun i => sgn (η i))
  simp only [xA, yA, Fin.append_left, Fin.append_right] at h ⊢
  rw [hS, hQ, hS2, hQ2, hfrac]
  linarith

end RegretKappa.Lower
