import Mathlib

open Real
open Filter
open Set
open Topology

namespace Indep2

/-!
# Doubly uniform regret for online linear regression in dimension 1

We formalize the conjecture `κ = 3` where `κ = lim_{T→∞} Reg*_T / (B² log T)`.

Model:
- Rounds `t = 1,…,T`. At each round the adversary reveals `x_t ∈ ℝ`, the learner
  predicts `ŷ_t`, then the adversary reveals `y_t` with `|y_t| ≤ B`.
- The learner is deterministic, causal, and knows `B` and `T` in advance.
- Regret = cumulative square loss of learner minus that of the best fixed linear
  predictor `θ·x_t` in hindsight (no bound on `θ` or `x_t`).
- `Reg*_T` = minimax regret over all causal learners.
-/

/-- A causal learner for horizon `T`.
    `predict t x_hist y_hist` gives the prediction at round `t` (0-indexed),
    using only `x_0,…,x_t` and `y_0,…,y_{t-1}`. -/
structure Learner (T : ℕ) where
  predict : (t : Fin T) → ((i : Fin (t.val.succ)) → ℝ) → ((i : Fin t.val) → ℝ) → ℝ

/-- Prefix of `x` up to time `t` (inclusive). -/
def prefixX {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : Fin (t.val.succ) → ℝ :=
  λ i => x ⟨i.val, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt t.2)⟩

/-- Prefix of `y` up to time `t` (exclusive). -/
def prefixY {T : ℕ} (y : Fin T → ℝ) (t : Fin T) : Fin t.val → ℝ :=
  λ i => y ⟨i.val, Nat.lt_of_lt_of_le i.2 (Nat.le_of_lt t.2)⟩

/-- The regret of learner `f` on play `(x, y)`.
    Computed as Σ_t (y_t - ŷ_t)² - inf_θ Σ_t (y_t - θ·x_t)²,
    where the infimum over θ is computed explicitly via the quadratic formula. -/
noncomputable def regret (T : ℕ) (f : Learner T) (x : Fin T → ℝ) (y : Fin T → ℝ) : ℝ :=
  let predictions := λ (t : Fin T) => f.predict t (prefixX x t) (prefixY y t)
  let sq_loss := ∑ t : Fin T, (y t - predictions t) ^ 2
  let sum_x_sq := ∑ t : Fin T, (x t) ^ 2
  let sum_y_sq := ∑ t : Fin T, (y t) ^ 2
  let sum_xy := ∑ t : Fin T, x t * y t
  let best_linear_loss :=
    if sum_x_sq = 0 then sum_y_sq
    else sum_y_sq - (sum_xy) ^ 2 / sum_x_sq
  sq_loss - best_linear_loss

/--
`Reg*_T` = minimax regret, defined as the infimum over learners of the
supremum over plays of the regret.

To avoid the junk-value issue with `sSup` on `ℝ` (which returns `0` for
unbounded sets), we use the equivalent formulation as the infimum of all
upper bounds `v` that work for every play against some learner.

The set is nonempty (the zero predictor gives regret ≤ `T·B²` for all plays
by Cauchy-Schwarz) and bounded below by `-T·B²` (since regret ≥ -Σ y_t² ≥ -T·B²),
so the `sInf` is the genuine infimum, not the junk value `0`.
-/
noncomputable def RegStar (T : ℕ) (B : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (f : Learner T),
    ∀ (x : Fin T → ℝ) (y : Fin T → ℝ), (∀ t, |y t| ≤ B) → regret T f x y ≤ v}

/-! ### The conjecture κ = 3 -/

/-- `κ = 3`: for every `B > 0`,
    `Reg*_T / (B² log T) → 3` as `T → ∞`. -/
def KappaThree : Prop :=
  ∀ (B : ℝ) (_hB : B > 0),
    Filter.Tendsto (λ (T : ℕ) => RegStar T B / ((B ^ 2) * Real.log (T : ℝ)))
      Filter.atTop (nhds 3)

/-- Upper bound: for every `B > 0`, `Reg*_T ≤ (3 + o(1))·B²·log T`.
    Formally: for any `ε > 0`, eventually `Reg*_T ≤ (3 + ε)·B²·log T`. -/
def UpperBound : Prop :=
  ∀ (B : ℝ) (_hB : B > 0),
    ∀ (ε : ℝ) (_hε : ε > 0),
      ∀ᶠ (T : ℕ) in Filter.atTop,
        RegStar T B ≤ (3 + ε) * (B ^ 2) * Real.log (T : ℝ)

/-- Lower bound: for every `B > 0`, `Reg*_T ≥ (3 - o(1))·B²·log T`.
    Formally: for any `ε > 0`, eventually `(3 - ε)·B²·log T ≤ Reg*_T`. -/
def LowerBound : Prop :=
  ∀ (B : ℝ) (_hB : B > 0),
    ∀ (ε : ℝ) (_hε : ε > 0),
      ∀ᶠ (T : ℕ) in Filter.atTop,
        (3 - ε) * (B ^ 2) * Real.log (T : ℝ) ≤ RegStar T B

end Indep2
