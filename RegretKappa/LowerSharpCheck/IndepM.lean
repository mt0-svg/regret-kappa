import RegretKappa.Corollaries.Statement

/-!
# Independence of the minimax regret: Theorem 1.1 and Corollary 5.1

Formal definitions of Theorem 1.1 (the two explicit inequalities for every `T ≥ 355713`)
and Corollary 5.1 (the adversary and the chain of minimax regrets over bounded features),
stated as propositions in `EReal`.
-/

namespace IndepM

open Set
open MeasureTheory

universe u

/-- For `T ≥ 355713` we have `T > e`, so `log T > 1` and consequently `log (log T) > 0`. -/
lemma log_log_pos {T : ℕ} (hT : 355713 ≤ T) : 0 < Real.log (Real.log (T : ℝ)) := by
  have hT_one : (1 : ℝ) < (T : ℝ) := by
    have : (1 : ℕ) < 355713 := by norm_num
    exact_mod_cast (Nat.lt_of_lt_of_le this hT)
  have h_exp_one_lt_T : Real.exp 1 < (T : ℝ) := by
    have h_exp_lt_355713 : Real.exp 1 < (355713 : ℝ) := by
      have h3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      linarith
    have h355713_le_T : (355713 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    exact lt_of_lt_of_le h_exp_lt_355713 h355713_le_T
  have hlog_pos : 0 < Real.log (T : ℝ) := Real.log_pos hT_one
  have hlog_gt_one : 1 < Real.log (T : ℝ) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ < Real.log (T : ℝ) := Real.log_lt_log (Real.exp_pos 1) h_exp_one_lt_T
  exact Real.log_pos hlog_gt_one

/-- **Theorem 1.1** (main theorem). For every `B > 0` and every integer `T ≥ 355713`,
the minimax regret satisfies
`B² (3 log T - 2 log log T - 15.2) ≤ Reg*_T(B) ≤ B² (3 log T + 0.37)`
in `EReal`, together with the limit statement `KappaEqThree`. -/
def Main : Prop :=
  (∀ (B : ℝ) (_hB : 0 < B) (T : ℕ) (_hT : 355713 ≤ T),
    ((B ^ 2 * (3 * Real.log (T : ℝ) - 2 * Real.log (Real.log (T : ℝ)) - 15.2) : ℝ) : EReal) ≤
      RegretKappa.minimaxRegret T B ∧
    RegretKappa.minimaxRegret T B ≤ ((B ^ 2 * (3 * Real.log (T : ℝ) + 0.37) : ℝ) : EReal)) ∧
  RegretKappa.KappaEqThree

/-- **Corollary 5.1** (bounded features). For every `B > 0` and every integer `T ≥ 355713`:

1. **Adversary lower bound.** There exists a finite type `ι` with weights `w` and plays
`(x, y)` with features in `[0, 1]` and outcomes in `{-B, 0, B}` such that every randomized
learner has expected regret at least `B² (3 log T - 2 log log T - 15.2)`.

2. **Chain of minimax regrets.**
`B² (3 log T - 2 log log T - 15.2) ≤ Reg*_T(B; [0, 1], {-B, 0, B}) ≤
` `Reg*_T(B; [0, 1], [-B, B]) ≤ B² (3 log T + 0.37)`.
-/
def Bounded : Prop :=
  (∀ (B : ℝ) (_hB : 0 < B) (T : ℕ) (_hT : 355713 ≤ T),
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → RegretKappa.Learner T),
        RegretKappa.Corollaries.IsRandLearner μ L →
          (((B ^ 2 * (3 * Real.log (T : ℝ) - 2 * Real.log (Real.log (T : ℝ)) - 15.2) : ℝ) : EReal) ≤
            RegretKappa.Corollaries.advRegret μ L w x y)) ∧
  (∀ (B : ℝ) (_hB : 0 < B) (T : ℕ) (_hT : 355713 ≤ T),
    ((B ^ 2 * (3 * Real.log (T : ℝ) - 2 * Real.log (Real.log (T : ℝ)) - 15.2) : ℝ) : EReal) ≤
      RegretKappa.Corollaries.minimaxRegretBF T B ∧
    RegretKappa.Corollaries.minimaxRegretBF T B ≤ RegretKappa.Corollaries.minimaxRegretBFI T B ∧
    RegretKappa.Corollaries.minimaxRegretBFI T B ≤ ((B ^ 2 * (3 * Real.log (T : ℝ) + 0.37) : ℝ) : EReal))

end IndepM
