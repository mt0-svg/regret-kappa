import RegretKappa.Statement

/-!
# Bounded-features version of the theorem (kappa = 3)

Restrict the plays to features `x_t ∈ [0, 1]` and outcomes `y_t ∈ {-B, 0, B}`.
Let `minimaxBF T B` be the minimax regret over these plays. Then for every `B > 0`,
`minimaxBF T B / (B ^ 2 log T) → 3` as `T → ∞`. Equivalently: upper half, lower half.
-/

namespace Indep51u

open Set
open Filter
open Topology
open RegretKappa

/-- A play with features in `[0, 1]` and outcomes in `{-B, 0, B}` exists for every `T`. -/
lemma nonempty_play (T : ℕ) (B : ℝ) : ∃ (x y : Fin T → ℝ),
    (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
  · intro t; exact ⟨by norm_num, by norm_num⟩
  · intro t; simp

/-- The denominator `B ^ 2 * log T` is positive for `B > 0` and `T ≥ 2`. -/
lemma denom_pos {B : ℝ} (hB : 0 < B) {T : ℕ} (hT : 2 ≤ T) : 0 < B ^ 2 * Real.log T :=
  mul_pos (pow_pos hB 2) (Real.log_pos (by exact_mod_cast (by omega : 1 < T)))

/-- The minimax regret over plays with features in `[0, 1]` and outcomes in `{-B, 0, B}`. -/
noncomputable def minimaxBF (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ)
    (_ : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (_ : ∀ t, y t ∈ ({-B, 0, B} : Set ℝ)),
    (regret L x y : EReal)

/-- `KappaBF`: for every `B > 0`, `minimaxBF T B / (B ^ 2 log T)` tends to `3` as `T → ∞`. -/
def KappaBF : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxBF T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop (𝓝 3)

/-- `UpperBF`: for every `B > 0` and `ε > 0`, for every large `T` there is a learner whose
regret is at most `(3 + ε) B ^ 2 log T` on every play with features in `[0, 1]`
and outcomes in `{-B, 0, B}`. -/
def UpperBF : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T,
    ∀ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) →
      regret L x y ≤ (3 + ε) * B ^ 2 * Real.log T

/-- `LowerBF`: for every `B > 0` and `ε > 0`, for every large `T` and every learner
there is a play with features in `[0, 1]` and outcomes in `{-B, 0, B}` on which its regret
is at least `(3 - ε) B ^ 2 log T`. -/
def LowerBF : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
      (3 - ε) * B ^ 2 * Real.log T ≤ regret L x y

end Indep51u
