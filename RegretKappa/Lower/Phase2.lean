import RegretKappa.Lower.VanTrees
import RegretKappa.Lower.ClosedForm

/-!
# Lower bound: the excess of phase 2

The paper, Lemma 4.11, steps (i) and (ii), in normalized coordinates. Phase 2 has `k`
rounds; the past of phase 1 enters only through `ρ` (with `|ρ| + 2 ≤ r`). Given the prior variable
`z ∈ [-2, 2]` (`θ* √V = ρ + z`), the outcome of round `i` is a sign with mean
`a_i(z) = (ρ + z) ε_i`, `ε_i = eps k r i`; the learner's prediction `yh i η` in round `i` depends
on the signs of the rounds before `i` only. The comparator excess of the paper is
`-z² + ∑_i ((ŷ_i - y_i)² - (a_i - y_i)²)` (the term `V_T (θ* - θ̂_T)² ≥ 0` is dropped), and its
expectation is at least `-4/7 + ∑_i ε_i² / W_i`:

* `-4/7 = -∫ z² prior` (`integral_sq_prior`);
* round `i` averages to `(ŷ_i - a_i)²` (`sum_lik_round`, step (i)) and, with `ψ = ŷ_i / ε_i - ρ`,
  to `ε_i² (ψ - z)²`; the van Trees inequality on the model cut at `i` (`sum_lik_cut`, `vanTrees`)
  gives at least `ε_i² / W_i` (step (ii)).
-/

namespace RegretKappa.Lower

open Finset Real

-- TARGET

/-- The second moment of the prior: `∫ z² (15/512) (4 - z²)² = 4/7`. -/
theorem integral_sq_prior : ∫ z in (-2 : ℝ)..2, z ^ 2 * prior z = 4 / 7 := by
  unfold prior
  have h_expand : (fun (z : ℝ) => z ^ 2 * (15 / 512 * (4 - z ^ 2) ^ 2)) =
      (fun z => 15/512 * (16*z^2 - 8*z^4 + z^6)) := by
    ext z; ring
  rw [h_expand]
  rw [intervalIntegral.integral_const_mul]
  have h_int : ∫ z in (-2 : ℝ)..2, (16*z^2 - 8*z^4 + z^6) = 2048/105 := by
    have hint2 : IntervalIntegrable (fun (z : ℝ) => (16 : ℝ)*z^2) MeasureTheory.volume (-2) 2 :=
      ((continuous_id.pow 2).const_mul (16 : ℝ)).intervalIntegrable _ _
    have hint4 : IntervalIntegrable (fun (z : ℝ) => (8 : ℝ)*z^4) MeasureTheory.volume (-2) 2 :=
      ((continuous_id.pow 4).const_mul (8 : ℝ)).intervalIntegrable _ _
    have hint6 : IntervalIntegrable (fun (z : ℝ) => z^6) MeasureTheory.volume (-2) 2 :=
      (continuous_id.pow 6).intervalIntegrable _ _
    have hint_sub : IntervalIntegrable (fun (z : ℝ) => (16 : ℝ)*z^2 - (8 : ℝ)*z^4) MeasureTheory.volume (-2) 2 :=
      hint2.sub hint4
    calc
      ∫ z in (-2 : ℝ)..2, (16*z^2 - 8*z^4 + z^6)
          = (∫ z in (-2 : ℝ)..2, (16*z^2 - 8*z^4)) + (∫ z in (-2 : ℝ)..2, z^6) := by
        rw [intervalIntegral.integral_add hint_sub hint6]
      _ = ((∫ z in (-2 : ℝ)..2, (16*z^2)) - (∫ z in (-2 : ℝ)..2, (8*z^4))) + (∫ z in (-2 : ℝ)..2, z^6) := by
        rw [intervalIntegral.integral_sub hint2 hint4]
      _ = (16 * (∫ z in (-2 : ℝ)..2, z^2) - 8 * (∫ z in (-2 : ℝ)..2, z^4)) + (∫ z in (-2 : ℝ)..2, z^6) := by
        simp [intervalIntegral.integral_const_mul]
      _ = (16 * ((2^3 - (-2)^3) / ((2:ℝ)+1)) - 8 * ((2^5 - (-2)^5) / ((4:ℝ)+1))) + ((2^7 - (-2)^7) / ((6:ℝ)+1)) := by
        simp [integral_pow]
      _ = 2048/105 := by norm_num
  rw [h_int]
  norm_num

/-- The bound of the phase-2 means: `|(ρ + z) ε_l| ≤ √ν_l²` for `z ∈ [-2, 2]`. -/
theorem abs_mean_le {k : ℕ} {r ρ : ℝ} (hr : |ρ| + 2 ≤ r) (l : ℕ) {z : ℝ}
    (hz : z ∈ Set.Icc (-2 : ℝ) 2) : |(ρ + z) * eps k r l| ≤ √(nu2 k l) := by
  rcases hz with ⟨hzl, hzr⟩
  have hz_abs : |z| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h_r_nonneg : 0 ≤ r := by
    have h_abs_nonneg : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have h_abs_add_le_r : |ρ + z| ≤ r := by
    calc
      |ρ + z| ≤ |ρ| + |z| := abs_add_le _ _
      _ ≤ |ρ| + 2 := by gcongr
      _ ≤ r := hr
  have h_eps_nonneg : 0 ≤ eps k r l := eps_nonneg k r l
  have h_r_eps_nonneg : 0 ≤ r * eps k r l := mul_nonneg h_r_nonneg h_eps_nonneg
  have h_sq_eq : (r * eps k r l) ^ 2 = nu2 k l := by
    by_cases hk : k = 0
    · subst hk
      simp [eps, nu2]
    · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hr_ne_zero : r ≠ 0 := by
        have h_abs_nonneg : 0 ≤ |ρ| := abs_nonneg _
        linarith
      calc
        (r * eps k r l) ^ 2 = r ^ 2 * (eps k r l) ^ 2 := by ring
        _ = r ^ 2 * ((l + 1 : ℝ) / (2 * (k : ℝ) * r ^ 2)) := by rw [eps_sq l]
        _ = (l + 1 : ℝ) / (2 * (k : ℝ)) := by
          field_simp [hr_ne_zero, hk']
        _ = nu2 k l := rfl
  calc
    |(ρ + z) * eps k r l| = |ρ + z| * |eps k r l| := abs_mul _ _
    _ = |ρ + z| * eps k r l := by rw [abs_of_nonneg h_eps_nonneg]
    _ ≤ r * eps k r l := by gcongr
    _ = √((r * eps k r l) ^ 2) := by rw [Real.sqrt_sq h_r_eps_nonneg]
    _ = √(nu2 k l) := by rw [h_sq_eq]

-- TARGET

/-- The information of the model cut at round `i` is the information `wInfo` before round `i`. -/
theorem wInfo_eq_cut {k : ℕ} (r : ℝ) (i : Fin k) :
    5 / 2 + ∑ l : Fin k, cut (i : ℕ) (fun l : Fin k => eps k r l) l ^ 2 / (1 - √(nu2 k l) ^ 2) =
      wInfo k r i := by
  unfold wInfo cut
  have h_sqrt_sq : ∀ l : Fin k, √(nu2 k l) ^ 2 = nu2 k l := by
    intro l
    rw [Real.sq_sqrt (nu2_nonneg k l.val)]
  simp_rw [h_sqrt_sq]
  -- Goal: 5/2 + ∑ l : Fin k, (if l.val < (i : ℕ) then eps k r l else 0)^2 / (1 - nu2 k l)
  --     = 5/2 + ∑ l ∈ range (i : ℕ), eps k r l ^ 2 / (1 - nu2 k l)
  set g : ℕ → ℝ := fun n => if n < (i : ℕ) then eps k r n ^ 2 / (1 - nu2 k n) else 0 with hg
  have h_sum_eq : ∑ l : Fin k, (if l.val < (i : ℕ) then eps k r l else 0) ^ 2 / (1 - nu2 k l) =
      ∑ l ∈ range (i : ℕ), eps k r l ^ 2 / (1 - nu2 k l) := by
    calc
      ∑ l : Fin k, (if l.val < (i : ℕ) then eps k r l else 0) ^ 2 / (1 - nu2 k l)
          = ∑ l : Fin k, (if l.val < (i : ℕ) then (eps k r l) ^ 2 else (0 : ℝ) ^ 2) / (1 - nu2 k l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> norm_num
      _ = ∑ l : Fin k, (if l.val < (i : ℕ) then (eps k r l) ^ 2 else 0) / (1 - nu2 k l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> norm_num
      _ = ∑ l : Fin k, (if l.val < (i : ℕ) then (eps k r l) ^ 2 / (1 - nu2 k l) else 0) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp
      _ = ∑ l : Fin k, g (l.val) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        dsimp [g]
      _ = ∑ l ∈ range k, g l := by rw [Fin.sum_univ_eq_sum_range]
      _ = ∑ l ∈ range k, (if l < (i : ℕ) then eps k r l ^ 2 / (1 - nu2 k l) else 0) := by rfl
      _ = ∑ l ∈ (range k).filter (· < (i : ℕ)), eps k r l ^ 2 / (1 - nu2 k l) := by rw [Finset.sum_filter]
      _ = ∑ l ∈ range (i : ℕ), eps k r l ^ 2 / (1 - nu2 k l) := by
        have h_eq : (range k).filter (· < (i : ℕ)) = range (i : ℕ) := by
          ext n
          constructor
          · intro h
            rcases Finset.mem_filter.mp h with ⟨_, hn_lt⟩
            exact Finset.mem_range.mpr hn_lt
          · intro h
            rcases Finset.mem_range.mp h with hn_lt
            have hn_lt_k : n < k := lt_trans hn_lt i.is_lt
            refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn_lt_k, hn_lt⟩
        rw [h_eq]
  rw [h_sum_eq]

/-- One round of phase 2: the van Trees bound `ε_i² / W_i`. -/
theorem round_vanTrees {k : ℕ} {r ρ : ℝ} (hr : |ρ| + 2 ≤ r) (i : Fin k)
    (yh : (Fin k → Bool) → ℝ)
    (hyh : ∀ η η' : Fin k → Bool, (∀ l : Fin k, l.val < i.val → η l = η' l) → yh η = yh η') :
    eps k r i ^ 2 / wInfo k r i ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        ((yh η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) := by
  have hk : 0 < k := Fin.pos i
  have hr0 : 0 < r := by linarith [abs_nonneg ρ]
  have he0 : 0 < eps k r i := by
    unfold eps
    exact Real.sqrt_pos.2 (by positivity)
  have hflip : ∀ η, yh (flipAt i η) = yh η := fun η =>
    hyh _ _ fun l hl => flipAt_ne (fun e => by rw [e] at hl; exact lt_irrefl _ hl) η
  have hpt : ∀ z, ∑ η, prior z * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        ((yh η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) =
      eps k r i ^ 2 * ∑ η, prior z * lik (cut i (fun l => ρ * eps k r l))
        (cut i (fun l : Fin k => eps k r l)) η z * ((yh η / eps k r i - ρ) - z) ^ 2 := by
    intro z
    have h1 := sum_lik_round (fun l => ρ * eps k r l) (fun l => eps k r l) z i yh hflip
    have h2 := sum_lik_cut (fun l => ρ * eps k r l) (fun l => eps k r l) z i
      (fun η => ((yh η / eps k r i - ρ) - z) ^ 2) (fun η η' h => by simp only [hyh η η' h])
    have h3 : ∀ η, (yh η - (ρ * eps k r i + eps k r i * z)) ^ 2 =
        eps k r i ^ 2 * ((yh η / eps k r i - ρ) - z) ^ 2 := fun η => by
      field_simp
      ring
    calc ∑ η, prior z * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
          ((yh η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2)
        = prior z * ∑ η, lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
          ((yh η - sgn (η i)) ^ 2 - (ρ * eps k r i + eps k r i * z - sgn (η i)) ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by ring
      _ = prior z * (eps k r i ^ 2 * ∑ η, lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
          ((yh η / eps k r i - ρ) - z) ^ 2) := by
          rw [h1]
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by rw [h3]; ring
      _ = _ := by
          rw [h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by ring
  have hc : ∀ l : Fin k, √(nu2 k l) < 1 := fun l =>
    (Real.sqrt_lt' one_pos).2 (by linarith [nu2_le_half l.isLt])
  have hcut : ∀ l : Fin k, ∀ z ∈ Set.Icc (-2 : ℝ) 2,
      |cut i (fun l => ρ * eps k r l) l + cut i (fun l : Fin k => eps k r l) l * z| ≤ √(nu2 k l) := by
    intro l z hz
    unfold cut
    split_ifs with hl
    · rw [show ρ * eps k r l + eps k r l * z = (ρ + z) * eps k r l by ring]
      exact abs_mean_le hr l hz
    · simp
  have hvt := vanTrees (cut i (fun l => ρ * eps k r l)) (cut i (fun l : Fin k => eps k r l))
    (fun l => √(nu2 k l)) hc hcut (fun η => yh η / eps k r i - ρ)
  rw [wInfo_eq_cut r i] at hvt
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hvt (sq_nonneg _)

/-- **Excess of phase 2** (the paper, Lemma 4.11 (i) and (ii), comparator term
dropped). -/
theorem phase2 {k : ℕ} {r ρ : ℝ} (hr : |ρ| + 2 ≤ r) (yh : Fin k → (Fin k → Bool) → ℝ)
    (hyh : ∀ (i : Fin k) (η η' : Fin k → Bool), (∀ l : Fin k, l.val < i.val → η l = η' l) →
      yh i η = yh i η') :
    -(4 / 7) + ∑ i ∈ range k, eps k r i ^ 2 / wInfo k r i ≤
      ∫ z in (-2 : ℝ)..2, ∑ η, prior z * lik (fun l => ρ * eps k r l) (fun l => eps k r l) η z *
        (-z ^ 2 + ∑ i, ((yh i η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2)) := by
  set α : Fin k → ℝ := fun l => ρ * eps k r l with hα
  set β : Fin k → ℝ := fun l => eps k r l with hβ
  set F : Fin k → ℝ → ℝ := fun i z => ∑ η, prior z * lik α β η z *
    ((yh i η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2) with hF
  have hpt : ∀ z, ∑ η, prior z * lik α β η z *
      (-z ^ 2 + ∑ i, ((yh i η - sgn (η i)) ^ 2 - ((ρ + z) * eps k r i - sgn (η i)) ^ 2)) =
      -(z ^ 2 * prior z) + ∑ i, F i z := by
    intro z
    have hs := sum_lik α β z
    simp only [hF, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun η i => _)]
    congr 1
    calc ∑ η, prior z * lik α β η z * -z ^ 2 = -(z ^ 2 * prior z) * ∑ η, lik α β η z := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun η _ => by ring
      _ = -(z ^ 2 * prior z) := by rw [hs, mul_one]
  have hcont : ∀ i, Continuous (F i) := fun i => by
    simp only [hF]
    fun_prop
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun z => -(z ^ 2 * prior z)) MeasureTheory.volume (-2) 2 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun z => ∑ i, F i z) MeasureTheory.volume (-2) 2 :=
    Continuous.intervalIntegrable (continuous_finsetSum _ fun i _ => hcont i) _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_neg, integral_sq_prior,
    intervalIntegral.integral_finsetSum fun i _ => (hcont i).intervalIntegrable _ _,
    ← Fin.sum_univ_eq_sum_range (fun i => eps k r i ^ 2 / wInfo k r i) k]
  have := Finset.sum_le_sum fun (i : Fin k) (_ : i ∈ Finset.univ) =>
    round_vanTrees hr i (yh i) (hyh i)
  simp only [hF]
  linarith

end RegretKappa.Lower
