import RegretKappa.LowerSharp.Prior
import RegretKappa.LowerSharp.ClosedForm
import RegretKappa.Lower.Phase2

/-!
# Sharp lower bound: the excess of phase 2

The paper, Lemma 4.11, steps (i) to (iii), in normalized coordinates, for the prior of
`LowerSharp/Prior.lean` (`g²`, information `J = π²/4`, second moment `4/3 - 8/π²`). Phase 2 has `k`
rounds and radius `r` with `|ρ| + 2 ≤ r`; given the prior variable `z ∈ [-2, 2]`
(`θ* √V = ρ + z`), the outcome of round `i` is a sign with mean `(ρ + z) ε_i`, `ε_i = eps k r i`.

* `round_vanTreesP` (step (ii)): round `i` averages to at least `ε_i² / W_i`, by the van Trees
  inequality on the model cut at `i` (as `Lower.round_vanTrees`);
* `comparator_vanTreesP` (step (iii)): for every estimator `ψ` from all `k` signs,
  `E[c (ψ - z)²] ≥ c / W_k`;
* `phase2S`: the bracket of Lemma 4.11,
  `-z² + ∑_i ((ŷ_i - y_i)² - ((ρ + z) ε_i - y_i)²) + (1 + X) (ψ - z)²` with `X = ∑ ε_i²` and
  `ψ = (ρ + ∑ ε_i y_i)/(1 + X) - ρ` (the term `V_T (θ* - θ̂_T)²`), averages to at least
  `β = -(4/3 - 8/π²) + ∑_i ε_i² / W_i + (1 + X)/W_k`.
-/

namespace RegretKappa.LowerSharp

open Finset Real RegretKappa.Lower

theorem wInfoJ_eq_cut (J : ℝ) {k : ℕ} (r : ℝ) (i : Fin k) :
    J + ∑ l : Fin k, cut (i : ℕ) (fun l : Fin k => eps k r l) l ^ 2 / (1 - √(nu2 k l) ^ 2) =
      wInfoJ J k r i := by
  have h := wInfo_eq_cut r i
  unfold wInfo at h
  unfold wInfoJ
  linarith

theorem wInfoJ_full (J : ℝ) (k : ℕ) (r : ℝ) :
    J + ∑ l : Fin k, eps k r l ^ 2 / (1 - √(nu2 k l) ^ 2) = wInfoJ J k r k := by
  unfold wInfoJ
  rw [Fin.sum_univ_eq_sum_range (fun l => eps k r l ^ 2 / (1 - √(nu2 k l) ^ 2)) k]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [Real.sq_sqrt (nu2_nonneg k l)]

theorem sqrt_nu2_lt_one {k : ℕ} (l : Fin k) : √(nu2 k l) < 1 :=
  (Real.sqrt_lt' one_pos).2 (by linarith [nu2_le_half l.isLt])

/-- One round of phase 2: the van Trees bound `ε_i² / W_i` (Lemma 4.11 (ii)). -/
theorem round_vanTreesP {k : ℕ} {r ρ : ℝ} (hr : |ρ| + 2 ≤ r) (i : Fin k)
    (yh : (Fin k → Bool) → ℝ)
    (hyh : ∀ η η' : Fin k → Bool, (∀ l : Fin k, l.val < i.val → η l = η' l) → yh η = yh η') :
    eps k r i ^ 2 / wInfoJ Jc k r i ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        ((yh η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) := by
  have hr0 : 0 < r := by linarith [abs_nonneg ρ]
  have he0 : 0 < eps k r i := by
    unfold eps
    exact Real.sqrt_pos.2 (by have := Fin.pos i; positivity)
  have hflip : ∀ η, yh (flipAt i η) = yh η := fun η =>
    hyh _ _ fun l hl => flipAt_ne (fun e => by rw [e] at hl; exact lt_irrefl _ hl) η
  have hpt : ∀ z, ∑ η, gP z ^ 2 * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        ((yh η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) =
      eps k r i ^ 2 * ∑ η, gP z ^ 2 * lik (cut i (fun l => ρ * eps k r l))
        (cut i (fun l : Fin k => eps k r l)) η z * ((yh η / eps k r i - ρ) - z) ^ 2 := by
    intro z
    have h1 := sum_lik_round (fun l => ρ * eps k r l) (fun l => eps k r l) z i yh hflip
    have h2 := sum_lik_cut (fun l => ρ * eps k r l) (fun l => eps k r l) z i
      (fun η => ((yh η / eps k r i - ρ) - z) ^ 2) (fun η η' h => by simp only [hyh η η' h])
    have h3 : ∀ η, (yh η - (ρ * eps k r i + eps k r i * z)) ^ 2 =
        eps k r i ^ 2 * ((yh η / eps k r i - ρ) - z) ^ 2 := fun η => by
      field_simp
      ring
    calc ∑ η, gP z ^ 2 * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
          ((yh η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2)
        = gP z ^ 2 * ∑ η, lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
          ((yh η - sgn (η i)) ^ 2 - (ρ * eps k r i + eps k r i * z - sgn (η i)) ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by ring
      _ = gP z ^ 2 * (eps k r i ^ 2 * ∑ η, lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
          ((yh η / eps k r i - ρ) - z) ^ 2) := by
          rw [h1]
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by rw [h3]; ring
      _ = _ := by
          rw [h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by ring
  have hcut : ∀ l : Fin k, ∀ z ∈ Set.Icc (-2 : ℝ) 2,
      |cut i (fun l => ρ * eps k r l) l + cut i (fun l : Fin k => eps k r l) l * z| ≤
        √(nu2 k l) := by
    intro l z hz
    unfold cut
    split_ifs with hl
    · rw [show ρ * eps k r l + eps k r l * z = (ρ + z) * eps k r l by ring]
      exact abs_mean_le hr l hz
    · simp
  have hvt := vanTreesP (cut i (fun l => ρ * eps k r l)) (cut i (fun l : Fin k => eps k r l))
    (fun l => √(nu2 k l)) sqrt_nu2_lt_one hcut (fun η => yh η / eps k r i - ρ)
  rw [wInfoJ_eq_cut Jc r i] at hvt
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hvt (sq_nonneg _)

/-- The comparator term (Lemma 4.11 (iii)): `E[c (ψ - z)²] ≥ c / W_k` for every estimator `ψ`
from all `k` signs. -/
theorem comparator_vanTreesP {k : ℕ} {r ρ : ℝ} (hr : |ρ| + 2 ≤ r) {c : ℝ} (hc : 0 ≤ c)
    (ψ : (Fin k → Bool) → ℝ) :
    c / wInfoJ Jc k r k ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        (c * (ψ η - z) ^ 2) := by
  have hcut : ∀ l : Fin k, ∀ z ∈ Set.Icc (-2 : ℝ) 2,
      |ρ * eps k r l + eps k r l * z| ≤ √(nu2 k l) := by
    intro l z hz
    rw [show ρ * eps k r l + eps k r l * z = (ρ + z) * eps k r l by ring]
    exact abs_mean_le hr l hz
  have hvt := vanTreesP (fun l => ρ * eps k r l) (fun l : Fin k => eps k r l)
    (fun l => √(nu2 k l)) sqrt_nu2_lt_one hcut ψ
  rw [wInfoJ_full] at hvt
  have e : ∀ z, ∑ η, gP z ^ 2 * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
      (c * (ψ η - z) ^ 2) = c * ∑ η, gP z ^ 2 *
        lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z * (ψ η - z) ^ 2 := fun z => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun η _ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hvt hc

/-- **Excess of phase 2** (the paper, Lemma 4.11, first claim). -/
theorem phase2S {k : ℕ} {r ρ : ℝ} (hr : |ρ| + 2 ≤ r) (yh : Fin k → (Fin k → Bool) → ℝ)
    (hyh : ∀ (i : Fin k) (η η' : Fin k → Bool), (∀ l : Fin k, l.val < i.val → η l = η' l) →
      yh i η = yh i η') :
    -(4 / 3 - 8 / π ^ 2) + ∑ i ∈ range k, eps k r i ^ 2 / wInfoJ Jc k r i +
        (1 + ∑ i ∈ range k, eps k r i ^ 2) / wInfoJ Jc k r k ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, gP z ^ 2 *
        lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        (-z ^ 2 + ∑ i, ((yh i η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) +
          (1 + ∑ i : Fin k, eps k r i ^ 2) *
            ((ρ + ∑ i : Fin k, eps k r i * sgn (η i)) / (1 + ∑ i : Fin k, eps k r i ^ 2) - ρ - z) ^ 2) := by
  set α : Fin k → ℝ := fun l => ρ * eps k r l with hα
  set β : Fin k → ℝ := fun l => eps k r l with hβ
  set X := ∑ i : Fin k, eps k r i ^ 2 with hX
  have hX0 : 0 ≤ 1 + X := by have : 0 ≤ X := Finset.sum_nonneg fun i _ => sq_nonneg _; linarith
  set ψ : (Fin k → Bool) → ℝ := fun η => (ρ + ∑ i : Fin k, eps k r i * sgn (η i)) / (1 + X) - ρ
    with hψ
  set F : Fin k → ℝ → ℝ := fun i z => ∑ η, gP z ^ 2 * lik α β η z *
    ((yh i η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) with hF
  set C : ℝ → ℝ := fun z => ∑ η, gP z ^ 2 * lik α β η z * ((1 + X) * (ψ η - z) ^ 2) with hC
  have hpt : ∀ z, ∑ η, gP z ^ 2 * lik α β η z *
      (-z ^ 2 + ∑ i, ((yh i η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) +
        (1 + X) * ((ρ + ∑ i : Fin k, eps k r i * sgn (η i)) / (1 + X) - ρ - z) ^ 2) =
      -(z ^ 2 * gP z ^ 2) + ∑ i, F i z + C z := by
    intro z
    have hs := sum_lik α β z
    simp only [hF, hC, hψ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun η i => _)]
    congr 1
    congr 1
    calc ∑ η, gP z ^ 2 * lik α β η z * -z ^ 2 = -(z ^ 2 * gP z ^ 2) * ∑ η, lik α β η z := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun η _ => by ring
      _ = -(z ^ 2 * gP z ^ 2) := by rw [hs, mul_one]
  have hcont : ∀ i, Continuous (F i) := fun i => by
    simp only [hF]
    fun_prop
  have hCc : Continuous C := by
    simp only [hC]
    fun_prop
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun z => -(z ^ 2 * gP z ^ 2)) MeasureTheory.volume (-2) 2 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun z => ∑ i, F i z) MeasureTheory.volume (-2) 2 :=
    Continuous.intervalIntegrable (continuous_finsetSum _ fun i _ => hcont i) _ _
  rw [intervalIntegral.integral_add (hi1.add hi2) (hCc.intervalIntegrable _ _),
    intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_neg, integral_sq_gP_sq,
    intervalIntegral.integral_finsetSum fun i _ => (hcont i).intervalIntegrable _ _,
    ← Fin.sum_univ_eq_sum_range (fun i => eps k r i ^ 2 / wInfoJ Jc k r i) k,
    ← Fin.sum_univ_eq_sum_range (fun i => eps k r i ^ 2) k]
  have h1 := Finset.sum_le_sum fun (i : Fin k) (_ : i ∈ Finset.univ) =>
    round_vanTreesP hr i (yh i) (hyh i)
  have h2 := comparator_vanTreesP hr hX0 ψ
  simp only [hF, hC] at h1 h2 ⊢
  linarith

end RegretKappa.LowerSharp
