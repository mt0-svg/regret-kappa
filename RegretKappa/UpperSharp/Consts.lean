import Mathlib

/-!
# Theorem 3.1 with the paper's constants: rational enclosures of the constants

`e^{-1/2}`, `e^{-1/6}`, `log 3`, `√(2π)` between rationals, and the chord bound of `-log(1 - s)` on
`[0, 2/3]` (the paper, proof of Lemma 3.10).
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set Finset Filter Topology

theorem exp_neg_half_bounds : 0.6065306597 ≤ exp (-1 / 2) ∧ exp (-1 / 2) ≤ 0.6065306598 := by
  have h := Real.exp_bound (by norm_num : |(-1/2 : ℝ)| ≤ 1) (by norm_num : 0 < (14 : ℕ))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

theorem exp_neg_sixth_le : exp (-1 / 6) ≤ 0.8464817249 := by
  have hx : |(-1 : ℝ) / 6| ≤ 1 := by
    rw [abs_div, abs_neg, abs_one]
    norm_num
  have hn : 0 < (10 : ℕ) := by norm_num
  have hbound := Real.exp_bound hx hn
  have h := (abs_le.mp hbound).right
  -- h : exp (-1/6) - sum ≤ |(-1/6)|^10 * (↑(10.succ) / (↑(10.factorial) * ↑10))
  have h_total : exp (-1 / 6) ≤
      (∑ m ∈ range 10, ((-1 : ℝ) / 6) ^ m / (m.factorial : ℝ)) +
      |(-1 : ℝ) / 6| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * (10 : ℝ))) := by
    linarith
  have h_rhs : (∑ m ∈ range 10, ((-1 : ℝ) / 6) ^ m / (m.factorial : ℝ)) +
      |(-1 : ℝ) / 6| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * (10 : ℝ))) ≤
      0.8464817249 := by
    norm_num
  linarith

theorem log_three_lt : log 3 < 1.0986123 := by
  have hpos3 : 0 < (3 : ℝ) := by norm_num
  rw [Real.log_lt_iff_lt_exp hpos3]
  have hsplit : Real.exp (1.0986123) = Real.exp 1 * Real.exp (0.0986123) := by
    calc
      Real.exp (1.0986123) = Real.exp ((1 : ℝ) + 0.0986123) := by norm_num
      _ = Real.exp 1 * Real.exp (0.0986123) := by rw [Real.exp_add]
  rw [hsplit]
  have hexp1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hx_nonneg : 0 ≤ (0.0986123 : ℝ) := by norm_num
  have hexpsum : ∑ i ∈ Finset.range 6, (0.0986123 : ℝ) ^ i / (i.factorial : ℝ) ≤ Real.exp (0.0986123) :=
    Real.sum_le_exp_of_nonneg hx_nonneg 6
  have hpos_sum : 0 < ∑ i ∈ Finset.range 6, (0.0986123 : ℝ) ^ i / (i.factorial : ℝ) := by
    refine Finset.sum_pos (fun i hi => ?_) ?_
    · positivity
    · exact ⟨0, Finset.mem_range.mpr (by norm_num)⟩
  have hpos_exp1 : 0 ≤ Real.exp 1 := by linarith [Real.exp_pos 1]
  have h_mul_lt : (2.7182818283 : ℝ) * (∑ i ∈ Finset.range 6, (0.0986123 : ℝ) ^ i / (i.factorial : ℝ)) <
      Real.exp 1 * Real.exp (0.0986123) :=
    mul_lt_mul hexp1 hexpsum hpos_sum hpos_exp1
  have h_three_lt_prod : (3 : ℝ) < (2.7182818283 : ℝ) * (∑ i ∈ Finset.range 6, (0.0986123 : ℝ) ^ i / (i.factorial : ℝ)) := by
    norm_num
  linarith

theorem sqrt_two_pi_bounds : 2.506628 ≤ √(2 * π) ∧ √(2 * π) ≤ 2.506629 := by
  have hpos_low : (0 : ℝ) ≤ 2.506628 := by norm_num
  have hpos_high : (0 : ℝ) ≤ 2.506629 := by norm_num
  have hpos_pi : (0 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_pos]
  have h_low_sq : 2.506628 ^ 2 ≤ 2 * π := by
    have : 2.506628 ^ 2 < 2 * (3.141592 : ℝ) := by norm_num
    have hpi : 2 * (3.141592 : ℝ) < 2 * π := by nlinarith [Real.pi_gt_d6]
    nlinarith
  have h_high_sq : 2 * π ≤ 2.506629 ^ 2 := by
    have hpi : 2 * π < 2 * (3.141593 : ℝ) := by nlinarith [Real.pi_lt_d6]
    have : 2 * (3.141593 : ℝ) < 2.506629 ^ 2 := by norm_num
    nlinarith
  have h_low : 2.506628 ≤ √(2 * π) := by
    rwa [Real.le_sqrt hpos_low hpos_pi]
  have h_high : √(2 * π) ≤ 2.506629 := by
    rwa [Real.sqrt_le_left hpos_high]
  exact And.intro h_low h_high

theorem chord_log {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 2 / 3) : -log (1 - s) ≤ 3 / 2 * log 3 * s := by
  set L := 3 / 2 * log 3 with hL
  have hlog3pos : 0 < log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hLpos : 0 ≤ L := by nlinarith
  -- Define φ(s) = L*s + log(1-s), we want φ(s) ≥ 0
  set φ := fun (x : ℝ) => L * x + log (1 - x) with hφ
  have hφ0 : φ 0 = 0 := by
    simp [φ, hL]
  have hφ23 : φ (2/3 : ℝ) = 0 := by
    dsimp [φ, L]
    have hlogdiv : log ((1 : ℝ) / 3) = -log 3 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0), Real.log_one, zero_sub]
    calc
      ((3 / 2 * log 3) * (2/3 : ℝ)) + log (1 - (2/3 : ℝ))
          = log 3 + log ((1 : ℝ) / 3) := by ring_nf
      _ = log 3 + (-log 3) := by rw [hlogdiv]
      _ = 0 := by ring
  -- The affine map g(x) = 1 - x
  let g : ℝ →ᵃ[ℝ] ℝ :=
    AffineMap.mk (fun x => 1 - x) (-LinearMap.id) (by
      intro p v
      simp [vadd_eq_add]
      ring)
  have hg_apply (x : ℝ) : g x = 1 - x := rfl
  have h_concave_log : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have h_concave_log_comp : ConcaveOn ℝ (g ⁻¹' (Set.Ioi (0 : ℝ))) (Real.log ∘ g) :=
    h_concave_log.comp_affineMap g
  -- Note: g ⁻¹' (Set.Ioi 0) = {x | 1 - x > 0} = (-∞, 1)
  -- And Set.Icc 0 (2/3) ⊆ g ⁻¹' (Set.Ioi 0)
  have h_subset : Set.Icc (0 : ℝ) (2/3 : ℝ) ⊆ g ⁻¹' (Set.Ioi (0 : ℝ)) := by
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    have hgx : g x = 1 - x := hg_apply x
    have hpos : 0 < g x := by
      rw [hgx]
      have : x < 1 := by linarith
      linarith
    exact hpos
  have h_concave_log_on_Icc : ConcaveOn ℝ (Set.Icc (0 : ℝ) (2/3 : ℝ)) (Real.log ∘ g) :=
    h_concave_log_comp.subset h_subset (convex_Icc _ _)
  -- Now φ(x) = L*x + (log ∘ g)(x)
  have h_linear_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) (2/3 : ℝ)) (fun (x : ℝ) => L * x) := by
    let f : ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun x => L * x
        map_add' := by intro x y; ring
        map_smul' := by
          intro r x
          simp [smul_eq_mul]
          ring }
    exact (f.concaveOn (convex_Icc _ _))
  have hφ_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) (2/3 : ℝ)) φ := by
    -- φ = (fun x => L*x) + (Real.log ∘ g)
    have : φ = (fun (x : ℝ) => L * x) + (Real.log ∘ g) := by
      ext x
      simp [φ, hg_apply]
    rw [this]
    exact h_linear_concave.add h_concave_log_on_Icc
  -- Now use the chord inequality
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2/3 : ℝ) := by
    constructor <;> norm_num
  have h23_mem : (2/3 : ℝ) ∈ Set.Icc (0 : ℝ) (2/3 : ℝ) := by
    constructor <;> norm_num
  -- Write s = a•0 + b•(2/3) with a = 1 - 3s/2, b = 3s/2
  -- Then a + b = 1, a ≥ 0, b ≥ 0
  set a := 1 - (3/2 : ℝ) * s with ha
  set b := (3/2 : ℝ) * s with hb
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    have : (3/2 : ℝ) * s ≤ 1 := by
      nlinarith
    linarith
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    nlinarith
  have hab_sum : a + b = 1 := by
    dsimp [a, b]
    ring
  have h_comb : a • (0 : ℝ) + b • (2/3 : ℝ) = s := by
    dsimp [a, b]
    simp
    ring
  -- Now apply ConcaveOn.ge_on_segment'
  have h_seg := hφ_concave.ge_on_segment' h0_mem h23_mem ha_nonneg hb_nonneg hab_sum
  -- h_seg : min (φ 0) (φ (2/3)) ≤ φ (a•0 + b•(2/3))
  rw [hφ0, hφ23, h_comb] at h_seg
  -- h_seg : min 0 0 ≤ φ s
  -- i.e., 0 ≤ φ s = L*s + log(1-s)
  -- i.e., -log(1-s) ≤ L*s
  have h_min : min (0 : ℝ) 0 = 0 := by simp
  rw [h_min] at h_seg
  dsimp [φ] at h_seg
  linarith

end RegretKappa.UpperSharp
