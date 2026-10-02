import RegretKappa.Upper.Identity

/-!
# The sums of the state

A play on `Fin T` extended by `0` to `ℕ` (`ext`), the partial sums `S_n = ∑_{i<n} x_i y_i` and
`V_n = ∑_{i<n} x_i²` (`Ssum`, `Vsum`), and the bound `ρ_n² ≤ n` on the state `ρ_n = S_n/√V_n`
for outcomes in `[-1, 1]` (`rho_sq_le`, the paper, Lemma 2.3 (a)). The learner of Theorem 3.1
(`RegretKappa/UpperSharp/Assembly.lean`) is written with them.
-/

namespace RegretKappa.Upper

open Real Finset Filter

/-- A sequence on `Fin T` extended by `0` to `ℕ`. -/
noncomputable def ext {T : ℕ} (x : Fin T → ℝ) (i : ℕ) : ℝ := if h : i < T then x ⟨i, h⟩ else 0

/-- `S_n = ∑_{i<n} x_i y_i`. -/
noncomputable def Ssum {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, ext x i * ext y i

/-- `V_n = ∑_{i<n} x_i²`. -/
noncomputable def Vsum {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, ext x i ^ 2

theorem ext_val {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : ext x t = x t := by
  simp [ext, t.isLt]

theorem abs_ext_le {T : ℕ} {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1) (i : ℕ) : |ext y i| ≤ 1 := by
  unfold ext
  split_ifs with h
  · exact hy _
  · simp

theorem Ssum_univ {T : ℕ} (x y : Fin T → ℝ) : ∑ t, x t * y t = Ssum x y T := by
  unfold Ssum
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext x i * ext y i) T]
  simp [ext_val]

theorem Vsum_univ {T : ℕ} (x : Fin T → ℝ) : ∑ t, x t ^ 2 = Vsum x T := by
  unfold Vsum
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext x i ^ 2) T]
  simp [ext_val]

theorem Vsum_nonneg {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : 0 ≤ Vsum x n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem Ssum_sq_le {T : ℕ} (x : Fin T → ℝ) {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1) (n : ℕ) :
    Ssum x y n ^ 2 ≤ n * Vsum x n :=
  sq_sum_mul_le (ext x) (ext y) (abs_ext_le hy) n

theorem rho_sq_le {T : ℕ} (x : Fin T → ℝ) {y : Fin T → ℝ} (hy : ∀ t, |y t| ≤ 1) (n : ℕ) :
    (Ssum x y n / √(Vsum x n)) ^ 2 ≤ n := by
  rcases eq_or_lt_of_le (Vsum_nonneg x n) with h | h
  · rw [← h, Real.sqrt_zero, div_zero]
    simp
  · rw [div_pow, Real.sq_sqrt h.le, div_le_iff₀ h]
    exact Ssum_sq_le x hy n

end RegretKappa.Upper
