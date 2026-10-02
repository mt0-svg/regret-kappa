import RegretKappa.Corollaries.Statement

/-!
# Section 4.1: quantities and theorems

We formalize the quantities `j₀`, `L`, `c₁`, `b(T)` from Section 4.1 of PROBLEM.txt,
and the statements of Theorem 4.1, its simplified forms, the main theorem, and
Corollary 5.1 (bounded features).

All logarithms are natural logarithms (`Real.log`). The horizon `T` is a natural number;
rounds are indexed by `Fin T` (round `t` here is round `t+1` of the paper).
-/

namespace IndepL

open Real
open Filter
open MeasureTheory
open Set
open Topology

/-! ### Quantities of Section 4.1 -/

/-- `j₀ = ⌈log(3 log T)⌉` as a natural number. For `T ≥ 355713`, `log T > 0`, so `3 log T > 0`
and the logarithm is defined (it is `0` at `0` by Mathlib convention, but here the argument
is positive). -/
noncomputable def j0 (T : ℕ) : ℕ :=
  ⌈Real.log (3 * Real.log (T : ℝ))⌉₊

/-- `L = 2 log(T / (20 e j₀))`. For `T ≥ 355713` the argument of the logarithm is positive. -/
noncomputable def L (T : ℕ) : ℝ :=
  2 * Real.log ((T : ℝ) / (20 * Real.exp 1 * (j0 T : ℝ)))

/-- The constant `c₁ = 1/2 + 4/3 - 8/π² + log(π²) + (J - 2)/(π² e²)` where `J = π²/4`.
This is `3.3186327...`. -/
noncomputable def c1 : ℝ :=
  1/2 + 4/3 - 8 / (π ^ 2) + Real.log (π ^ 2) + ((π ^ 2 / 4) - 2) / ((π ^ 2) * (Real.exp 1) ^ 2)

/-- `T₁ = ⌊T/2⌋`. -/
def T1 (T : ℕ) : ℕ :=
  T / 2

/-- `k₀ = T - T₁ = ⌈T/2⌉`. -/
def k0 (T : ℕ) : ℕ :=
  T - T1 T

/-- `a = √L`. -/
noncomputable def a (T : ℕ) : ℝ :=
  Real.sqrt (L T)

/-- `b(T) = (1 - e^{-j₀}) [L + log(k₀ / (a + 2)²) - c₁ - log(k₀)/(2k₀) - 1/k₀]`.
For `T ≥ 355713` all terms are well-defined: `L ≥ 0` (so its square root is real),
`k₀ > 0`, and `a + 2 > 0`. -/
noncomputable def b (T : ℕ) : ℝ :=
  (1 - Real.exp (-(j0 T : ℝ))) *
    (L T + Real.log ((k0 T : ℝ) / ((a T + 2) ^ 2)) - c1 -
      Real.log (k0 T : ℝ) / (2 * (k0 T : ℝ)) - 1 / (k0 T : ℝ))

/-! ### Lemma: well-definedness for `T ≥ 355713` -/

lemma log_T_gt_third {T : ℕ} (hT : 355713 ≤ T) : 1 / 3 < Real.log (T : ℝ) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (show 0 < T from by omega)
  have h_exp_lt : Real.exp (1/3) < (T : ℝ) := by
    calc
      Real.exp (1/3) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num : (1/3 : ℝ) < 1)
      _ < 3 := Real.exp_one_lt_three
      _ ≤ (T : ℝ) := by
        have : (3 : ℕ) ≤ T := by omega
        exact_mod_cast this
  have h := (Real.log_lt_log_iff (Real.exp_pos _) hTpos).mpr h_exp_lt
  simpa [Real.log_exp (1/3)] using h

lemma j0_pos {T : ℕ} (hT : 355713 ≤ T) : 0 < Real.log (3 * Real.log (T : ℝ)) := by
  have hlog_gt_third : 1 / 3 < Real.log (T : ℝ) := log_T_gt_third hT
  have h3log : 1 < 3 * Real.log (T : ℝ) := by linarith
  exact Real.log_pos h3log

lemma k0_pos {T : ℕ} (_hT : 355713 ≤ T) : 0 < k0 T := by
  unfold k0 T1
  have hT' : 0 < T := by omega
  have : T / 2 ≤ T := Nat.div_le_self T 2
  omega

lemma a_add_two_pos {T : ℕ} (_hT : 355713 ≤ T) : 0 < a T + 2 := by
  unfold a
  have hsq : 0 ≤ Real.sqrt (L T) := Real.sqrt_nonneg _
  linarith

/-! ### Theorem 4.1, first inequality: the adversary (deterministic learners, B = 1) -/

/-- **Theorem 4.1, first inequality** (B = 1, deterministic learners): for every `T ≥ 355713`
there is an adversary with finitely many plays, each with nonnegative features and outcomes
in `{-1, 0, 1}`, drawn at random with fixed probabilities, against which every deterministic
learner has expected regret at least `b(T)`. -/
def Adversary : Prop :=
  ∀ T : ℕ, 355713 ≤ T →
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, 0 ≤ x i t) ∧
      (∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) ∧
      ∀ L : RegretKappa.Learner T, b T ≤ ∑ i, w i * RegretKappa.regret L (x i) (y i)

/-! ### Theorem 4.1, last sentence: one play with regret at least `B² b(T)` -/

/-- **Theorem 4.1, last sentence**: for every `B > 0` and `T ≥ 355713`, every deterministic
learner has a play with outcomes in `[-B, B]` and regret at least `B² b(T)`. -/
def OnePlay : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ, 355713 ≤ T →
    ∀ L : RegretKappa.Learner T, ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ B ^ 2 * b T ≤ RegretKappa.regret L x y

/-! ### Simplified forms of Theorem 4.1 -/

/-- **Simplified forms** of Theorem 4.1: the two lower bounds for `b(T)` that hold for every
`T ≥ 355713`. -/
def Simplified : Prop :=
  (∀ T : ℕ, 355713 ≤ T → 3 * Real.log T - Real.log (Real.log T) - 2 * Real.log (Real.log (Real.log T) + 2.1) - 14.6 ≤ b T) ∧
  (∀ T : ℕ, 355713 ≤ T → 3 * Real.log T - 2 * Real.log (Real.log T) - 15.2 ≤ b T)

/-! ### Main theorem -/

/-- The explicit upper bound `U(T)` for the minimax regret: `U(T) = 2 log(e² + (√T + 1)(3T + 2e^{-1/2}) / √(2π))`. -/
noncomputable def U (T : ℕ) : ℝ :=
  2 * Real.log (Real.exp 2 + (Real.sqrt (T : ℝ) + 1) * (3 * (T : ℝ) + 2 * Real.exp (-1 / 2)) / Real.sqrt (2 * π))

/-- **Main theorem** (Section 4.1): for every `B > 0` and `T ≥ 355713`,

`B²(3 log T - 2 log log T - 15.2) ≤ B² b(T) ≤ Reg*_T(B) ≤ B² U(T)`

and consequently `Reg*_T(B) / (B² log T) → 3` as `T → ∞`, in `EReal`. -/
def Main : Prop :=
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, 355713 ≤ T →
    ((B ^ 2 * (3 * Real.log T - 2 * Real.log (Real.log T) - 15.2) : ℝ) : EReal) ≤ ((B ^ 2 * b T : ℝ) : EReal) ∧
    ((B ^ 2 * b T : ℝ) : EReal) ≤ RegretKappa.minimaxRegret T B ∧
    RegretKappa.minimaxRegret T B ≤ ((B ^ 2 * U T : ℝ) : EReal)) ∧
  (∀ B : ℝ, 0 < B → Tendsto (fun T : ℕ => RegretKappa.minimaxRegret T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop (𝓝 3))

/-! ### Corollary 5.1: bounded features -/

/-- **Corollary 5.1** (bounded features): for every `B > 0` and `T ≥ 355713`,

1. There is an adversary with finitely many plays, each with features in `[0, 1]` and outcomes
   in `{-B, 0, B}`, drawn at random with fixed probabilities, against which every randomized
   learner has expected regret at least `B² b(T)`.
2. The chain of inequalities over bounded features:

`B²(3 log T - 2 log log T - 15.2) ≤ B² b(T) ≤ Reg*_T(B; [0,1], {-B,0,B}) ≤ Reg*_T(B; [0,1], [-B,B]) ≤ B² U(T)`. -/
def Bounded : Prop :=
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, 355713 ≤ T →
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → RegretKappa.Learner T),
        RegretKappa.Corollaries.IsRandLearner μ L →
          ((b T * B ^ 2 : ℝ) : EReal) ≤ RegretKappa.Corollaries.advRegret μ L w x y) ∧
  (∀ B : ℝ, 0 < B → ∀ T : ℕ, 355713 ≤ T →
    ((B ^ 2 * (3 * Real.log T - 2 * Real.log (Real.log T) - 15.2) : ℝ) : EReal) ≤ ((b T * B ^ 2 : ℝ) : EReal) ∧
    ((b T * B ^ 2 : ℝ) : EReal) ≤ RegretKappa.Corollaries.minimaxRegretBF T B ∧
    RegretKappa.Corollaries.minimaxRegretBF T B ≤ RegretKappa.Corollaries.minimaxRegretBFI T B ∧
    RegretKappa.Corollaries.minimaxRegretBFI T B ≤ ((B ^ 2 * U T : ℝ) : EReal))

end IndepL
