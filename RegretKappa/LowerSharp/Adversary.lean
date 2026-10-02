import RegretKappa.LowerSharp.Hitting
import RegretKappa.Lower.ClosedForm
import RegretKappa.Lower.Identity

/-!
# Sharp lower bound: the adversary and its play

The adversary of the paper, Section 4.2, with phase 2 at the fixed round `m = T₁`, on `m + k`
rounds: phase 1 is rounds `0, ..., m - 1`, phase 2 is rounds `m, ..., m + k - 1`.

* Phase 1, signs `ξ : Fin m → Bool`, `ζ = ext ξ`: the chain `rhoS`, `VS`, `xS` of
  `LowerSharp/Chain.lean`, outcome `sgn ξ_t`. Once `ρ² ≥ L` the move is `0`: the feature is `0`,
  the outcome a fair sign, and the state stays put, so `ρ_F = ρ_{m-1}` is the paper's `ρ_{T₁}`.
* Success, `L ≤ ρ_F²`: round `m + i` plays the feature `ε_i √V` (`ε_i = eps k r i`,
  `r = |ρ_F| + 2`, `V = V_{m-1}`) and the outcome `sgn η_i`. Failure: phase 2 plays `x = y = 0`.

`regret_succ` is the regret on a play of the paper (Lemma 4.8, from Lemma 2.2, with
`θ* √V = ρ + z`), with the comparator term `V_T (θ* - θ̂_T)²` kept; `regret_fail` the bound on the
failure branch. The causality lemmas say which signs each prediction sees.
-/

namespace RegretKappa.LowerSharp

open Finset Real RegretKappa.Lower

theorem fappend_lt {α : Type*} {m k : ℕ} (u : Fin m → α) (v : Fin k → α) (s : Fin (m + k))
    (h : s.val < m) : Fin.append u v s = u ⟨s.val, h⟩ := by
  have e := Fin.append_left u v ⟨s.val, h⟩
  rwa [show Fin.castAdd k ⟨s.val, h⟩ = s from Fin.ext rfl] at e

theorem fappend_ge {α : Type*} {m k : ℕ} (u : Fin m → α) (v : Fin k → α) (s : Fin (m + k))
    (h : m ≤ s.val) : Fin.append u v s = v ⟨s.val - m, by omega⟩ := by
  have e := Fin.append_right u v ⟨s.val - m, by omega⟩
  rwa [show Fin.natAdd m ⟨s.val - m, by omega⟩ = s from Fin.ext (by simp; omega)] at e

/-- The phase-2 radius `r = |ρ_F| + 2`. -/
noncomputable def rr (L : ℝ) {m : ℕ} (ξ : Fin m → Bool) : ℝ := |rhoF L ξ| + 2

/-- The features of the play. -/
noncomputable def xA (L : ℝ) {m : ℕ} (k : ℕ) (ξ : Fin m → Bool) : Fin (m + k) → ℝ :=
  Fin.append (fun t : Fin m => xS L (ext ξ) t)
    (fun i : Fin k => if L ≤ rhoF L ξ ^ 2 then eps k (rr L ξ) i * √(VF L ξ) else 0)

/-- The outcomes of the play. -/
noncomputable def yA (L : ℝ) {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) : Fin (m + k) → ℝ :=
  Fin.append (fun t : Fin m => sgn (ξ t))
    (fun i : Fin k => if L ≤ rhoF L ξ ^ 2 then sgn (η i) else 0)

theorem xA_nonneg (L : ℝ) {m : ℕ} (k : ℕ) (ξ : Fin m → Bool) (t : Fin (m + k)) :
    0 ≤ xA L k ξ t := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) t
  · simp only [xA, Fin.append_left]; exact xS_nonneg L _ _
  · simp only [xA, Fin.append_right]
    split_ifs
    · exact mul_nonneg (eps_nonneg _ _ _) (Real.sqrt_nonneg _)
    · exact le_rfl

theorem yA_mem (L : ℝ) {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) (t : Fin (m + k)) :
    yA L ξ η t ∈ ({-1, 0, 1} : Set ℝ) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) t
  · simp only [yA, Fin.append_left]; cases ξ i <;> simp [sgn]
  · simp only [yA, Fin.append_right]
    split_ifs
    · cases η j <;> simp [sgn]
    · simp

theorem abs_yA_le (L : ℝ) {m k : ℕ} (ξ : Fin m → Bool) (η : Fin k → Bool) (t : Fin (m + k)) :
    |yA L ξ η t| ≤ 1 := by
  have h := yA_mem L ξ η t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-- The prediction of the learner on the play. -/
noncomputable def pred (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (t : Fin (m + k)) : ℝ :=
  Lrn.prediction (xA L k ξ) (yA L ξ η) t

/-- A phase-1 prediction ignores the phase-2 signs. -/
theorem pred_castAdd_congr (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η η' : Fin k → Bool) (t : Fin m) :
    pred L Lrn ξ η (Fin.castAdd k t) = pred L Lrn ξ η' (Fin.castAdd k t) := by
  refine prediction_congr Lrn _ (fun s _ => rfl) fun s hs => ?_
  have hs' : s.val < m := lt_of_lt_of_le (Fin.lt_def.1 hs) (by simp [t.isLt.le])
  simp only [yA, fappend_lt _ _ s hs']

/-- A phase-1 prediction in round `t` ignores the sign of round `t`. -/
theorem pred_castAdd_flipAt (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (t : Fin m) :
    pred L Lrn (flipAt t ξ) η (Fin.castAdd k t) = pred L Lrn ξ η (Fin.castAdd k t) := by
  refine prediction_congr Lrn _ (fun s hs => ?_) fun s hs => ?_
  · have hs1 : s.val ≤ t.val := by simpa [Fin.le_def] using hs
    have hs' : s.val < m := by omega
    simp only [xA, fappend_lt _ _ s hs']
    exact xS_congr L fun i hi => ext_flipAt_ne t ξ (by omega)
  · have hs1 : s.val < t.val := by simpa [Fin.lt_def] using hs
    have hs' : s.val < m := by omega
    simp only [yA, fappend_lt _ _ s hs']
    rw [flipAt_ne]
    intro e
    rw [← e] at hs1
    exact lt_irrefl _ hs1

/-- A phase-2 prediction in round `m + i` sees the phase-2 signs before `i` only. -/
theorem pred_natAdd_congr (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (i : Fin k) {η η' : Fin k → Bool} (h : ∀ l : Fin k, l.val < i.val → η l = η' l) :
    pred L Lrn ξ η (Fin.natAdd m i) = pred L Lrn ξ η' (Fin.natAdd m i) := by
  refine prediction_congr Lrn _ (fun s _ => rfl) fun s hs => ?_
  have hs1 : s.val < m + i.val := by simpa [Fin.lt_def] using hs
  rcases lt_or_ge s.val m with h1 | h1
  · simp only [yA, fappend_lt _ _ s h1]
  · simp only [yA, fappend_ge _ _ s h1]
    rw [h _ (by simp; omega)]

/-- The pointwise algebra of the comparator, the identity of the paper's Lemma 4.8:
with `X = ∑ ε_i²`, `Y = ∑ ε_i y_i`, `u = ρ + z`,
`∑ (ŷ_i² - 2 ŷ_i y_i) + (ρ + Y)²/(1 + X)
  = ρ² - z² + ∑ ((ŷ_i - y_i)² - (u ε_i - y_i)²) + (1 + X) ((ρ + Y)/(1 + X) - ρ - z)²`. -/
theorem comparator_eq {k : ℕ} (ρ z : ℝ) (e yh y : Fin k → ℝ) :
    ∑ i, (yh i ^ 2 - 2 * yh i * y i) + (ρ + ∑ i, e i * y i) ^ 2 / (1 + ∑ i, e i ^ 2) =
      ρ ^ 2 + (-z ^ 2 + ∑ i, ((yh i - y i) ^ 2 - ((ρ + z) * e i - y i) ^ 2) +
        (1 + ∑ i, e i ^ 2) * ((ρ + ∑ i, e i * y i) / (1 + ∑ i, e i ^ 2) - ρ - z) ^ 2) := by
  have hX : 0 ≤ ∑ i, e i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD : (1 + ∑ i, e i ^ 2) ≠ 0 := by linarith
  have hs : ∑ i, ((yh i - y i) ^ 2 - ((ρ + z) * e i - y i) ^ 2) =
      ∑ i, (yh i ^ 2 - 2 * yh i * y i) - ((ρ + z) ^ 2 * ∑ i, e i ^ 2 -
        2 * (ρ + z) * ∑ i, e i * y i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  set X := ∑ i, e i ^ 2
  set Y := ∑ i, e i * y i
  field_simp
  ring

/-- The phase-1 part of the regret, `∑_{t<m} (ŷ_t² - 2 ŷ_t y_t)`. -/
noncomputable def P1 (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool) : ℝ :=
  ∑ t : Fin m, (pred L Lrn ξ (fun _ => false) (Fin.castAdd k t) ^ 2 -
    2 * pred L Lrn ξ (fun _ => false) (Fin.castAdd k t) * sgn (ξ t))

theorem sum_P1_eq (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) :
    ∑ t : Fin m, (pred L Lrn ξ η (Fin.castAdd k t) ^ 2 -
      2 * pred L Lrn ξ η (Fin.castAdd k t) * sgn (ξ t)) = P1 L Lrn ξ := by
  unfold P1
  exact Finset.sum_congr rfl fun t _ => by
    rw [pred_castAdd_congr L Lrn ξ η (fun _ => false) t]

/-- `S_{m-1} = ρ_F √V` and `V_{m-1} = V` on the phase-1 rounds. -/
theorem sum_phase1 (L : ℝ) {m : ℕ} (hm : 1 ≤ m) (ξ : Fin m → Bool) :
    ∑ t : Fin m, xS L (ext ξ) t * sgn (ξ t) = rhoF L ξ * √(VF L ξ) ∧
      ∑ t : Fin m, xS L (ext ξ) t ^ 2 = VF L ξ := by
  constructor
  · have h := sum_xS_mul L (ext ξ) (m - 1)
    rw [Nat.sub_add_cancel hm, ← Fin.sum_univ_eq_sum_range] at h
    simp only [rhoF, VF]
    simpa only [ext_fin] using h
  · have h := sum_xS_sq L (ext ξ) (m - 1)
    rwa [Nat.sub_add_cancel hm, ← Fin.sum_univ_eq_sum_range] at h

/-- **The regret identity on a successful play** (the paper, Lemma 4.8, from Lemma 2.2,
`θ* √V = ρ + z`, comparator term kept). -/
theorem regret_succ (L : ℝ) {m k : ℕ} (hm : 1 ≤ m) (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (z : ℝ) (hs : L ≤ rhoF L ξ ^ 2) :
    regret Lrn (xA L k ξ) (yA L ξ η) = P1 L Lrn ξ + rhoF L ξ ^ 2 +
      (-z ^ 2 + ∑ i : Fin k, ((pred L Lrn ξ η (Fin.natAdd m i) - sgn (η i)) ^ 2 -
        ((rhoF L ξ + z) * eps k (rr L ξ) i - sgn (η i)) ^ 2) +
        (1 + ∑ i : Fin k, eps k (rr L ξ) i ^ 2) *
          ((rhoF L ξ + ∑ i : Fin k, eps k (rr L ξ) i * sgn (η i)) /
            (1 + ∑ i : Fin k, eps k (rr L ξ) i ^ 2) - rhoF L ξ - z) ^ 2) := by
  have hV : 0 < VF L ξ := VS_pos L (ext ξ) (m - 1)
  obtain ⟨hS, hQ⟩ := sum_phase1 L hm ξ
  set e : Fin k → ℝ := fun i => eps k (rr L ξ) i with he
  have hS2 : ∑ i : Fin k, e i * √(VF L ξ) * sgn (η i) = √(VF L ξ) * ∑ i : Fin k, e i * sgn (η i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hQ2 : ∑ i : Fin k, (e i * √(VF L ξ)) ^ 2 = VF L ξ * ∑ i : Fin k, e i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt hV.le]; ring
  have hfrac : (rhoF L ξ * √(VF L ξ) + √(VF L ξ) * ∑ i : Fin k, e i * sgn (η i)) ^ 2 /
      (VF L ξ + VF L ξ * ∑ i : Fin k, e i ^ 2) =
      (rhoF L ξ + ∑ i : Fin k, e i * sgn (η i)) ^ 2 / (1 + ∑ i : Fin k, e i ^ 2) := by
    rw [show rhoF L ξ * √(VF L ξ) + √(VF L ξ) * ∑ i : Fin k, e i * sgn (η i) =
      √(VF L ξ) * (rhoF L ξ + ∑ i : Fin k, e i * sgn (η i)) by ring, mul_pow,
      Real.sq_sqrt hV.le, show VF L ξ + VF L ξ * ∑ i : Fin k, e i ^ 2 =
      VF L ξ * (1 + ∑ i : Fin k, e i ^ 2) by ring]
    exact mul_div_mul_left _ _ hV.ne'
  have h := comparator_eq (rhoF L ξ) z e (fun i => pred L Lrn ξ η (Fin.natAdd m i))
    (fun i => sgn (η i))
  rw [← sum_P1_eq L Lrn ξ η]
  unfold pred at h ⊢
  rw [regret_eq, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [xA, yA, Fin.append_left, Fin.append_right, hs, ite_true] at h ⊢
  rw [hS, hQ, hS2, hQ2, hfrac]
  simp only [he] at h ⊢
  linarith

/-- On a failed play, the regret is at least the phase-1 part. -/
theorem regret_fail (L : ℝ) {m k : ℕ} (Lrn : Learner (m + k)) (ξ : Fin m → Bool)
    (η : Fin k → Bool) (hf : ¬ L ≤ rhoF L ξ ^ 2) :
    P1 L Lrn ξ ≤ regret Lrn (xA L k ξ) (yA L ξ η) := by
  rw [← sum_P1_eq L Lrn ξ η]
  unfold pred
  rw [regret_eq, Fin.sum_univ_add]
  simp only [xA, yA, Fin.append_left, Fin.append_right, hf, ite_false, mul_zero, sub_zero]
  have h1 : 0 ≤ ∑ i : Fin k, Lrn.prediction (xA L k ξ) (yA L ξ η) (Fin.natAdd m i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ (∑ t, xA L k ξ t * yA L ξ η t) ^ 2 / ∑ t, xA L k ξ t ^ 2 :=
    div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun t _ => sq_nonneg _)
  simp only [xA, yA, hf, ite_false] at h1 h2
  linarith

end RegretKappa.LowerSharp
