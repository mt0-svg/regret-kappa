import RegretKappa.Statement

/-!
# The statement of Theorem 4.1 with its explicit constants

The paper, Theorem 4.1, on the model of `RegretKappa/Statement.lean` (`Learner`,
`regret`). For an integer `T ≥ 3`,

`j_0 = ⌈log(3 log T)⌉`, `L = 2 log(T/(20 e j_0))`, `a = √L`, `T_1 = ⌊T/2⌋`, `k_0 = T - T_1`,
`J = π²/4`, `c_1 = 1/2 + 4/3 - 8/π² + log(π²) + (J - 2)/(π² e²)`,

`b(T) = (1 - e^{-j_0}) [L + log(k_0/(a + 2)²) - c_1 - log(k_0)/(2 k_0) - 1/k_0]`.

For `T ≥ 355713` every quantity is meaningful: `3 log T > 1`, so `j_0 ≥ 1`; `L > 0`; `k_0 ≥ 1`;
no division by zero, logarithm of a nonpositive number or square root of a negative number
occurs, and the truncated subtractions `T / 2` and `T - T / 2` are the floor and `T - ⌊T/2⌋`.

Targets (propositions, proved in other modules of the library):
* `LowerSharpAdv`: for every `T ≥ 355713` there is an adversary that ignores the predictions and
  plays the finitely many plays `(x i, y i)` with probabilities `w i`, every feature `≥ 0` and
  every outcome in `{-1, 0, 1}`, against which every learner has expected regret
  `∑ w_i Regret(x i, y i) ≥ b(T)`: the paper, Theorem 4.1 (a) (the adversary `A_T` of the paper is
  such an adversary), in the form that `RegretKappa.Corollaries.boundedFeatures_of_mixture`
  takes;
* `LowerSharpBound` (Theorem 4.1 (c)): for every `B > 0` and `T ≥ 355713`, every learner has a
  play with `|y t| ≤ B` and regret at least `B² b(T)`;
* `LowerSharpSimplified` (Theorem 4.1 (b)): for `T ≥ 355713`, the two simplified forms
  `b(T) ≥ 3 log T - log log T - 2 log(log log T + 2.1) - 14.6 ≥ 3 log T - 2 log log T - 15.2`.
-/

namespace RegretKappa.LowerSharp

open Real

/-- The least horizon of the theorem, `T_0 = 355713`. -/
def T0 : ℕ := 355713

/-- `j_0 = ⌈log(3 log T)⌉`. -/
noncomputable def j0 (T : ℕ) : ℕ := ⌈log (3 * log T)⌉₊

/-- The level `L = 2 log(T/(20 e j_0))`. -/
noncomputable def level (T : ℕ) : ℝ := 2 * log (T / (20 * exp 1 * j0 T))

/-- The length `T_1 = ⌊T/2⌋` of phase 1 at most. -/
def T1 (T : ℕ) : ℕ := T / 2

/-- `k_0 = T - T_1`, the least length of phase 2. -/
def k0 (T : ℕ) : ℕ := T - T1 T

/-- The Fisher information `J = π²/4` of the prior. -/
noncomputable def Jc : ℝ := π ^ 2 / 4

/-- `c_1 = 1/2 + 4/3 - 8/π² + log(π²) + (J - 2)/(π² e²)`. -/
noncomputable def c1 : ℝ := 1 / 2 + 4 / 3 - 8 / π ^ 2 + log (π ^ 2) + (Jc - 2) / (π ^ 2 * exp 2)

/-- The bound of the paper, Theorem 4.1:
`b(T) = (1 - e^{-j_0}) [L + log(k_0/(√L + 2)²) - c_1 - log(k_0)/(2 k_0) - 1/k_0]`. -/
noncomputable def bT (T : ℕ) : ℝ :=
  (1 - exp (-(j0 T : ℝ))) *
    (level T + log (k0 T / (√(level T) + 2) ^ 2) - c1 - log (k0 T) / (2 * k0 T) - 1 / k0 T)

/-- **The paper, Theorem 4.1 (a), against a finite adversary** (`B = 1`, deterministic learners):
for every `T ≥ 355713` there are finitely many plays `(x i, y i)`, with weights `w i ≥ 0` of sum
`1`, features `≥ 0` and outcomes in `{-1, 0, 1}`, such that every learner has weighted regret
`∑ w_i Regret(x i, y i) ≥ b(T)`. -/
def LowerSharpAdv : Prop :=
  ∀ T : ℕ, T0 ≤ T →
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i t, 0 ≤ x i t) ∧
      (∀ i t, y i t ∈ ({-1, 0, 1} : Set ℝ)) ∧
      ∀ L : Learner T, bT T ≤ ∑ i, w i * regret L (x i) (y i)

/-- **The paper, Theorem 4.1 (c), on one play:** for every `B > 0` and `T ≥ 355713`, every learner
has a play with outcomes in `[-B, B]` on which its regret is at least `B² b(T)`. -/
def LowerSharpBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ, T0 ≤ T → ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ B ^ 2 * bT T ≤ regret L x y

/-- **The paper, Theorem 4.1 (b), the simplified forms:** for `T ≥ 355713`,
`b(T) ≥ 3 log T - log log T - 2 log(log log T + 2.1) - 14.6 ≥ 3 log T - 2 log log T - 15.2`. -/
def LowerSharpSimplified : Prop :=
  ∀ T : ℕ, T0 ≤ T →
    3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 14.6 ≤ bT T ∧
      3 * log T - 2 * log (log T) - 15.2 ≤
        3 * log T - log (log T) - 2 * log (log (log T) + 2.1) - 14.6

end RegretKappa.LowerSharp
