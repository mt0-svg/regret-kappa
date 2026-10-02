import RegretKappa.Lower.Identity
import RegretKappa.Corollaries.Scaling

/-!
# Transfer of a lower bound to bounded features, and the outcome scale

`transfer`: let a finite family of plays `(x i, y i)`, with weights `w i`, have nonnegative
features and outcomes in `{-1, 0, 1}`, and let every learner have weighted regret
`∑ w_i Reg(x i, y i) ≥ b` on it. Then for every `B > 0` the plays with the features divided by
`M = 1 + ∑_{i, t} x i t` and the outcomes multiplied by `B` have features in `[0, 1]`, outcomes in
`{-B, 0, B}`, and weighted regret at least `B ^ 2 b` for every learner. The features cost nothing
(`regret_scaleX`) and the outcomes are rescaled by `Lower.rescale` (`Lower.regret_rescale`); the
bound `b` is any real number, so the lemma applies to every lower bound proved through a finite
mixture of plays with nonnegative features.

`regret_rescale_inv`: the learner `rescale L B⁻¹`, which multiplies the predictions of `L` on the
outcomes divided by `B` by `B`, has on `(x, y)` the regret `B ^ 2` times the regret of `L` on
`(x, y / B)`. So an upper bound for outcomes in `[-1, 1]` gives `B ^ 2`
times it for outcomes in `[-B, B]`.
-/

namespace RegretKappa.Corollaries

open RegretKappa.Lower

/-- Nonnegative numbers divided by one plus their sum lie in `[0, 1]`. -/
theorem div_mem_Icc_of_le_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ)
    (hf : ∀ i j, 0 ≤ f i j) (i : ι) (j : κ) :
    f i j / (1 + ∑ i', ∑ j', f i' j') ∈ Set.Icc (0 : ℝ) 1 := by
  have hsum_nonneg : 0 ≤ ∑ i', ∑ j', f i' j' := by
    apply Finset.sum_nonneg
    intro i' hi'
    apply Finset.sum_nonneg
    intro j' hj'
    apply hf i' j'
  have hD_pos : 0 < 1 + ∑ i', ∑ j', f i' j' := by
    linarith
  have hD_nonneg : 0 ≤ 1 + ∑ i', ∑ j', f i' j' := by linarith
  have hnum_le_D : f i j ≤ 1 + ∑ i', ∑ j', f i' j' := by
    have h1 : f i j ≤ ∑ j', f i j' := by
      apply Finset.single_le_sum (s := Finset.univ) (f := fun (k : κ) => f i k)
      · intro k hk
        apply hf i k
      · exact Finset.mem_univ j
    have h2 : ∑ j', f i j' ≤ ∑ i', ∑ j', f i' j' := by
      apply Finset.single_le_sum (s := Finset.univ) (f := fun (i' : ι) => ∑ j', f i' j')
      · intro i' hi'
        apply Finset.sum_nonneg
        intro j' hj'
        apply hf i' j'
      · exact Finset.mem_univ i
    linarith
  constructor
  · apply div_nonneg (hf i j) hD_nonneg
  · rw [div_le_one hD_pos]
    exact hnum_le_D

/-- **Transfer of a lower bound through a finite mixture of plays to bounded features.** -/
theorem transfer {T : ℕ} {ι : Type*} [Fintype ι] (w : ι → ℝ) (x y : ι → Fin T → ℝ)
    (hx : ∀ i t, 0 ≤ x i t) (hy : ∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) {b : ℝ}
    (hb : ∀ L : Learner T, b ≤ ∑ i, w i * regret L (x i) (y i)) {B : ℝ} (hB : 0 < B) :
    ∃ x' y' : ι → Fin T → ℝ,
      (∀ i t, x' i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y' i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ L : Learner T, B ^ 2 * b ≤ ∑ i, w i * regret L (x' i) (y' i) := by
  set M := 1 + ∑ i, ∑ t, x i t with hMdef
  have hM : 0 < M := add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun t _ => hx i t)
  refine ⟨fun i t => x i t / M, fun i t => B * y i t,
    fun i t => div_mem_Icc_of_le_sum x hx i t, fun i t => ?_, fun L => ?_⟩
  · show B * y i t ∈ ({-B, 0, B} : Set ℝ)
    rcases hy i t with h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [Set.mem_singleton_iff.1 h]; simp
  · have key : ∀ i, regret L (fun t => x i t / M) (fun t => B * y i t) =
        B ^ 2 * regret (scaleX M (rescale L B)) (x i) (y i) := fun i => by
      rw [regret_rescale L hB.ne', regret_scaleX _ hM.ne']
    simp_rw [key]
    calc B ^ 2 * b
        ≤ B ^ 2 * ∑ i, w i * regret (scaleX M (rescale L B)) (x i) (y i) :=
          mul_le_mul_of_nonneg_left (hb _) (sq_nonneg B)
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring

/-- Rescaling by `B⁻¹` and then by `B` gives back the learner, for `B ≠ 0`. -/
theorem rescale_rescale_inv {T : ℕ} (L : Learner T) {B : ℝ} (hB : B ≠ 0) :
    rescale (rescale L B⁻¹) B = L := by
  cases L with | mk p =>
    simp [rescale, hB]

/-- The regret of `rescale L B⁻¹` on `(x, y)` is `B ^ 2` times the regret of `L` on
`(x, y / B)`. -/
theorem regret_rescale_inv {T : ℕ} (L : Learner T) {B : ℝ} (hB : B ≠ 0) (x y : Fin T → ℝ) :
    regret (rescale L B⁻¹) x y = B ^ 2 * regret L x (fun t => y t / B) := by
  have h_mul_div : (fun t : Fin T => B * (y t / B)) = y := by
    ext t
    field_simp [hB]
  calc
    regret (rescale L B⁻¹) x y = regret (rescale L B⁻¹) x (fun t => B * (y t / B)) := by
      simp [h_mul_div]
    _ = B ^ 2 * regret (rescale (rescale L B⁻¹) B) x (fun t => y t / B) := by
      rw [regret_rescale (rescale L B⁻¹) hB x (fun t => y t / B)]
    _ = B ^ 2 * regret L x (fun t => y t / B) := by rw [rescale_rescale_inv L hB]

end RegretKappa.Corollaries
