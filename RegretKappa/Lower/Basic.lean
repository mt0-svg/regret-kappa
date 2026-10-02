import Mathlib

/-!
# Lower bound: signs and uniform averages over sign vectors

The adversary of the lower bound draws its outcomes from fair or biased signs. Its randomness is
finite in phase 1 (uniform sign vectors) and its phase-2 prior is one real variable, so the
probability space is kept explicit: a uniform average `avg n F` over the `2 ^ n` vectors
`Fin n → Bool`, and, for phase 2, a weighted sum and an interval integral (`Lower/Model.lean`,
`Lower/VanTrees.lean`).

* `sgn b`, the outcome `±1` of a sign;
* `ext ξ`, a finite sign vector extended by `false`, so that the adversary is defined on `ℕ → Bool`;
* `ncons`, prepending a sign; `flipAt t`, flipping coordinate `t`;
* `avg n F` and its rules: constants, linearity, monotonicity, the existence of a vector at least
  the average, the decomposition by the first sign and invariance under a flip.
-/

namespace RegretKappa.Lower

open Finset

/-- The outcome `±1` of a sign. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_true : sgn true = 1 := rfl

theorem sgn_false : sgn false = -1 := rfl

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> norm_num [sgn]

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> norm_num [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> norm_num [sgn]

/-- A finite sign vector extended by `false` to all of `ℕ`. -/
def ext {n : ℕ} (ξ : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then ξ ⟨i, h⟩ else false

theorem ext_of_lt {n : ℕ} (ξ : Fin n → Bool) {i : ℕ} (h : i < n) : ext ξ i = ξ ⟨i, h⟩ := by
  simp [ext, h]

theorem ext_fin {n : ℕ} (ξ : Fin n → Bool) (i : Fin n) : ext ξ i = ξ i := by
  simp [ext]

/-- Prepend a sign to a sign sequence. -/
def ncons (b : Bool) (ζ : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | i + 1 => ζ i

theorem ext_cons {n : ℕ} (b : Bool) (ξ : Fin n → Bool) :
    ext (Fin.cons b ξ : Fin (n + 1) → Bool) = ncons b (ext ξ) := by
  funext i
  cases i with
  | zero => simp [ext, ncons]
  | succ i =>
    by_cases h : i < n
    · have h' : i + 1 < n + 1 := by omega
      simp only [ext, ncons, h, h', dite_true]
      exact Fin.cons_succ (α := fun _ => Bool) b ξ ⟨i, h⟩
    · have h' : ¬ i + 1 < n + 1 := by omega
      simp [ext, ncons, h, h']

/-- Flip the sign at coordinate `t`. -/
def flipAt {n : ℕ} (t : Fin n) (ξ : Fin n → Bool) : Fin n → Bool := Function.update ξ t (!ξ t)

theorem flipAt_self {n : ℕ} (t : Fin n) (ξ : Fin n → Bool) : flipAt t ξ t = !ξ t := by
  simp [flipAt]

theorem flipAt_ne {n : ℕ} {t s : Fin n} (h : s ≠ t) (ξ : Fin n → Bool) : flipAt t ξ s = ξ s := by
  simp [flipAt, h]

theorem flipAt_flipAt {n : ℕ} (t : Fin n) (ξ : Fin n → Bool) : flipAt t (flipAt t ξ) = ξ := by
  funext s
  by_cases h : s = t
  · subst h; simp [flipAt]
  · simp [flipAt, h]

/-- Flipping coordinate `t` does not change the extended vector at another index. -/
theorem ext_flipAt_ne {n : ℕ} (t : Fin n) (ξ : Fin n → Bool) {i : ℕ} (h : i ≠ t.val) :
    ext (flipAt t ξ) i = ext ξ i := by
  unfold ext
  split_ifs with hi
  · exact flipAt_ne (fun e => h (by rw [← e])) ξ
  · rfl

/-- The average over the `2 ^ n` sign vectors of length `n`. -/
noncomputable def avg (n : ℕ) (F : (Fin n → Bool) → ℝ) : ℝ := (∑ ξ, F ξ) / 2 ^ n

theorem avg_const (n : ℕ) (c : ℝ) : avg n (fun _ => c) = c := by
  unfold avg
  simp [Finset.card_univ, Fintype.card_bool]

theorem avg_add (n : ℕ) (F G : (Fin n → Bool) → ℝ) :
    avg n (fun ξ => F ξ + G ξ) = avg n F + avg n G := by
  unfold avg
  rw [Finset.sum_add_distrib, add_div]

theorem avg_sub (n : ℕ) (F G : (Fin n → Bool) → ℝ) :
    avg n (fun ξ => F ξ - G ξ) = avg n F - avg n G := by
  unfold avg
  rw [Finset.sum_sub_distrib, sub_div]

theorem avg_mul_left (n : ℕ) (c : ℝ) (F : (Fin n → Bool) → ℝ) :
    avg n (fun ξ => c * F ξ) = c * avg n F := by
  unfold avg
  rw [← Finset.mul_sum, mul_div_assoc]

theorem avg_sum {ι : Type*} (s : Finset ι) (n : ℕ) (F : ι → (Fin n → Bool) → ℝ) :
    avg n (fun ξ => ∑ i ∈ s, F i ξ) = ∑ i ∈ s, avg n (F i) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]

theorem avg_mono {n : ℕ} {F G : (Fin n → Bool) → ℝ} (h : ∀ ξ, F ξ ≤ G ξ) : avg n F ≤ avg n G := by
  unfold avg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ξ _ => h ξ) (by positivity)

theorem avg_nonneg {n : ℕ} {F : (Fin n → Bool) → ℝ} (h : ∀ ξ, 0 ≤ F ξ) : 0 ≤ avg n F := by
  unfold avg
  exact div_nonneg (Finset.sum_nonneg fun ξ _ => h ξ) (by positivity)

/-- Some sign vector is at least the average. -/
theorem exists_avg_le (n : ℕ) (F : (Fin n → Bool) → ℝ) : ∃ ξ, avg n F ≤ F ξ := by
  obtain ⟨ξ, -, hξ⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n → Bool)) F
    Finset.univ_nonempty
  exact ⟨ξ, (avg_mono fun η => hξ η (Finset.mem_univ η)).trans_eq (avg_const n (F ξ))⟩

/-- The average decomposed by the first sign. -/
theorem avg_cons (n : ℕ) (F : (Fin (n + 1) → Bool) → ℝ) :
    avg (n + 1) F =
      (avg n (fun ξ => F (Fin.cons true ξ)) + avg n (fun ξ => F (Fin.cons false ξ))) / 2 := by
  unfold avg
  have h : ∑ ξ, F ξ = ∑ ξ, F (Fin.cons true ξ) + ∑ ξ, F (Fin.cons false ξ) := by
    rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp F, Fintype.sum_prod_type, Fintype.sum_bool]
    rfl
  rw [h, pow_succ]
  field_simp

/-- The average is invariant under flipping one coordinate. -/
theorem avg_flipAt {n : ℕ} (t : Fin n) (F : (Fin n → Bool) → ℝ) :
    avg n (fun ξ => F (flipAt t ξ)) = avg n F := by
  unfold avg
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (flipAt_flipAt t)) F

/-- A function that changes sign under a flip has average `0`. -/
theorem avg_eq_zero_of_flipAt {n : ℕ} (t : Fin n) (F : (Fin n → Bool) → ℝ)
    (h : ∀ ξ, F (flipAt t ξ) = -F ξ) : avg n F = 0 := by
  have h1 := avg_flipAt t F
  have h2 : avg n (fun ξ => F (flipAt t ξ)) = -avg n F := by
    simp_rw [h]
    unfold avg
    rw [Finset.sum_neg_distrib, neg_div]
  linarith

end RegretKappa.Lower
