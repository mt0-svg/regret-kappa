import Mathlib

open Real
open Set
open Filter
open Topology
open BigOperators

namespace Indep

/-!
# Doubly uniform regret for online linear regression in dimension 1

We formalize the minimax regret for online linear regression in dimension 1.
At each round `t = 1, …, T`, the adversary reveals `x_t ∈ ℝ` (unbounded),
the learner predicts `ŷ_t` causally (depending only on `x_1,…,x_t, y_1,…,y_{t-1}`),
then the adversary reveals `y_t` with `|y_t| ≤ B`.

The regret is the learner's cumulative square loss minus that of the best fixed
linear predictor `θ x` in hindsight (with no bound on `θ`).
`Reg*_T` is the causal minimax regret (inf over learners, sup over adversaries).

We define three statements:
* `KappaThree`: the limit of `Reg*_T / (B² log T)` is 3.
* `UpperBound`: `Reg*_T ≤ (3 + o(1)) B² log T`.
* `LowerBound`: `Reg*_T ≥ (3 - o(1)) B² log T`.
-/

/-- Squared error at a single round. -/
def sqErr (y yhat : ℝ) : ℝ := (y - yhat)^2

/-- Cumulative squared error over `T` rounds. -/
def cumSqErr (y yhat : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, sqErr (y t) (yhat t)

/-- The best fixed linear predictor's cumulative loss:
    `inf_{θ ∈ ℝ} Σ_{t=1}^T (y_t - θ x_t)^2`.
    This is always well-defined as a real number (the set is nonempty and bounded below). -/
noncomputable def bestLinLoss (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  sInf (Set.range (λ θ : ℝ => ∑ t ∈ Finset.range T, (y t - θ * x t)^2))

/-- Regret for a specific play `(x, y, yhat)` over `T` rounds:
    cumulative squared error of learner minus best fixed linear predictor's loss. -/
noncomputable def regret (x y yhat : ℕ → ℝ) (T : ℕ) : ℝ :=
  cumSqErr y yhat T - bestLinLoss x y T

/-! ### Causal learners -/

/-- A causal learner for horizon `T`.
    At round `t` (`0 ≤ t < T`), given the history of `x` up to `t` and `y` up to `t-1`,
    produces a prediction. The prediction at time `t` does not depend on future
    information (`x_{t+1},…,x_{T-1}` or `y_t,…,y_{T-1}`).
    We represent the history as functions on `Fin (t+1)` and `Fin t`. -/
def CausalLearner (T : ℕ) : Type :=
  (t : Fin T) → ((Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ)) → ℝ

/-- Convert a causal learner and full sequences `x, y` to a plain `ℕ → ℝ` prediction.
    For `t ≥ T`, we default to `0` (these rounds are not used in the regret over `T` rounds). -/
def evalLearner (f : CausalLearner T) (x y : ℕ → ℝ) : ℕ → ℝ := by
  intro t
  by_cases h : t < T
  · let t' : Fin T := ⟨t, h⟩
    exact f t' (λ i => x i, λ i => y i)
  · exact 0

/-- Regret for a causal learner `f` against sequences `x, y` over `T` rounds. -/
noncomputable def causalRegret (f : CausalLearner T) (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  regret x y (evalLearner f x y) T

/-! ### Minimax regret -/

/-- The set of sequences `y` that are bounded by `B` in absolute value. -/
def boundedY (B : ℝ) : Set (ℕ → ℝ) := { y | ∀ t, |y t| ≤ B }

/-- For a fixed causal learner `f` and bound `B`, the supremum over all adversary
    strategies `(x, y)` with `|y_t| ≤ B` of the regret. -/
noncomputable def learnerRegretSup (f : CausalLearner T) (B : ℝ) : ℝ :=
  sSup (Set.range (λ (x : ℕ → ℝ) =>
    sSup ((boundedY B).image (λ y => causalRegret f x y T))))

/-- The causal minimax regret `Reg*_T(B)`.
    Infimum over all causal learner strategies of the supremum over all adversary
    strategies `(x` unbounded, `y` bounded by `B`) of the regret. -/
noncomputable def minimaxRegret (B : ℝ) (T : ℕ) : ℝ :=
  sInf (Set.range (λ (f : CausalLearner T) => learnerRegretSup f B))

/-! ### Meaningfulness lemmas -/

lemma sqErr_nonneg (y yhat : ℝ) : 0 ≤ sqErr y yhat := by
  unfold sqErr; nlinarith

lemma bestLinLoss_nonneg (x y : ℕ → ℝ) (T : ℕ) : 0 ≤ bestLinLoss x y T := by
  unfold bestLinLoss
  apply sInf_nonneg
  rintro _ ⟨θ, rfl⟩
  apply Finset.sum_nonneg
  intro t _
  have : 0 ≤ (y t - θ * x t)^2 := by nlinarith
  exact this

lemma regret_ge_neg_bestLinLoss (x y yhat : ℕ → ℝ) (T : ℕ) : -bestLinLoss x y T ≤ regret x y yhat T := by
  unfold regret
  have h := sqErr_nonneg
  -- cumSqErr y yhat T ≥ 0
  have hcum : 0 ≤ cumSqErr y yhat T := by
    unfold cumSqErr
    apply Finset.sum_nonneg
    intro t _
    apply sqErr_nonneg
  nlinarith

lemma boundedY_nonempty {B : ℝ} (hB : 0 ≤ B) : (boundedY B).Nonempty := by
  refine ⟨λ _ => 0, λ t => ?_⟩
  simp [hB]

lemma causalLearner_nonempty (T : ℕ) : Nonempty (CausalLearner T) := by
  refine ⟨λ t _ => 0⟩

lemma regret_le_cumSqErr (x y yhat : ℕ → ℝ) (T : ℕ) : regret x y yhat T ≤ cumSqErr y yhat T := by
  unfold regret
  have h := bestLinLoss_nonneg x y T
  nlinarith

lemma cumSqErr_nonneg (y yhat : ℕ → ℝ) (T : ℕ) : 0 ≤ cumSqErr y yhat T := by
  unfold cumSqErr
  apply Finset.sum_nonneg
  intro t _
  apply sqErr_nonneg

/-! ### The three statements -/

/-- `KappaThree`: for every `B > 0`, `Reg*_T / (B^2 log T)` tends to `3` as `T → ∞`. -/
def KappaThree : Prop :=
  ∀ B > 0,
    Filter.Tendsto (λ T : ℕ => minimaxRegret B T / (B^2 * Real.log (T : ℝ)))
      Filter.atTop (𝓝 3)

/-- `UpperBound`: for every `B > 0`, `Reg*_T ≤ (3 + o(1)) B^2 log T`,
    i.e., for every `ε > 0`, eventually `Reg*_T ≤ (3 + ε) B^2 log T`. -/
def UpperBound : Prop :=
  ∀ B > 0, ∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
    minimaxRegret B T ≤ (3 + ε) * B^2 * Real.log (T : ℝ)

/-- `LowerBound`: for every `B > 0`, `Reg*_T ≥ (3 - o(1)) B^2 log T`,
    i.e., for every `ε > 0`, eventually `Reg*_T ≥ (3 - ε) B^2 log T`. -/
def LowerBound : Prop :=
  ∀ B > 0, ∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
    minimaxRegret B T ≥ (3 - ε) * B^2 * Real.log (T : ℝ)

end Indep
