import RegretKappa.Statement
import RegretKappa.UpperSharp.Statement

/-!
# Target statement: regret with the outcome bound `B` and the horizon `T` both unknown

The game of `RegretKappa/Statement.lean` (online linear regression in dimension 1, features
revealed on the fly with no bound, square loss, comparison with every linear predictor `θ * x`,
`θ : ℝ` unbounded; `RegretKappa.Learner`, `RegretKappa.regret`), played by a learner that is told
neither the horizon `T` nor the bound `B` on the outcomes. Rounds are indexed from `0`: round `t`
here is round `t + 1` of the paper.

An anytime learner (`AnytimeLearner`) is one prediction map per round `t : ℕ`, from the features
`x 0, ..., x t` and the outcomes `y 0, ..., y (t - 1)`; it carries no horizon and no bound. For each
`T` its first `T` maps form a learner of horizon `T` (`AnytimeLearner.restrict`), so its prediction
in round `t` is the same in every game of length greater than `t`. In the targets the learner is
chosen first, before `ε`, `T` and `B`.

Targets (propositions, proved in other modules of the library; the implications named below are
in `RegretKappa/UnknownBT/Bridge.lean`):
* `UnknownBT`: one anytime learner such that, for every `ε > 0`, eventually in `T`, for every
  `B > 0` and every play of length `T` with `|y t| ≤ B`, `Regret_T ≤ (3 + ε) B² log T`; that is,
  `sup_{B, play} Regret_T / (B² log T) ≤ 3 + ε_T` with `ε_T → 0` independent of `B` and of the play
  (at `T = 1` no learner can have `Regret_1 ≤ c B² log 1 = 0`, so the bound is asymptotic);
* `UnknownBTEveryT`: the literal form of the question, one anytime learner and one sequence
  `ε_T → 0` with `Regret_T ≤ (3 + ε_T) B² log T` for every `T ≥ 2`, every `B > 0` and every play
  with `|y t| ≤ B`; it implies `UnknownBT` (`unknownBT_of_everyT`), and the converse needs the
  worst ratio of the learner finite at every `T ≥ 2`;
* `UnknownT` (the bound known, the horizon not) and `UnknownB` (the horizon known, the bound not):
  the same with the learner chosen after `B`, respectively after `ε` and `T`; both follow from
  `UnknownBT` (`unknownT_of_unknownBT`, `unknownB_of_unknownBT`);
* `Optimality`: for every `B > 0` and `ε > 0`, eventually in `T`, every anytime learner has a play
  with `|y t| ≤ B` and `Regret_T ≥ (3 - ε) B² log T`; `RegretKappa.LowerBound` (every learner of
  horizon `T`, so the anytime ones too) implies it (`optimality_of_lowerBound`);
* `BestConstantThree`: the answer to the question in one proposition: some anytime learner has
  `worstRatio L T → 3`, where `worstRatio L T = sup_{B > 0, play, |y t| ≤ B} Regret_T / (B² log T)`
  in `EReal`, and every anytime learner has `liminf_T worstRatio L T ≥ 3`; `UnknownBT` and
  `Optimality` give it (`bestConstantThree_of_bounds`), and then `bestConstant`, the infimum over
  anytime learners of `limsup_T worstRatio L T`, is `3` (`bestConstant_eq_three`).

The explicit forms, on two learners written from their formulas (`learnerB`, `learnerBT`):
* `TheoremB` and `TheoremBNum` (`B = 1` known, `T` unknown): for `T ≥ 1` and outcomes in
  `[-1, 1]`, the learner `learnerB` has
  `Regret_T ≤ 3 log T + 4 log log(T + 2) + K + 2 log(1 + 1/√T) + 2 log(1 + 2/T)`, with the constant
  `K = 2 log(3/log 2 + 2e^{-1/2}(1/log 2 - 1/log 3)) - log(2π)` (`constK`), and
  `Regret_T ≤ 3 log T + 4 log log(T + 2) + 1.3706 + 2/√T + 4/T`;
* `ScaleFreeBound c` (`B` and `T` unknown): for `T ≥ 1` and every play, the learner `learnerBT`
  has `Regret_T ≤ M_T² (3 log T + 4 log log(T + 2) + c + 2/√T + 4/T)` with `M_T = max_t |y t|`
  (`runMax`). The constant is a parameter: the proof gives `c = 12`
  (`UB.scaleFreeBound_twelve`); any `c` gives `UnknownBTEveryT` (`everyT_of_scaleFreeBound`), and
  `TheoremBNum` gives `UnknownT` (`unknownT_of_theoremBNum`).

No division by zero or logarithm of a nonpositive number occurs in the explicit forms
(`log((t + 3)/(t + 2)) > 0`, `T ≥ 1`); the conventions of the paper for `V = 0`, `V + x² = 0` and
`x = 0` are written out in `predLam`, as in `RegretKappa.UpperSharp.predU`. In `worstRatio` the
denominator `B² log T` is positive for `T ≥ 2`; at `T ≤ 1` the quotient is the `EReal` junk value
`0`, which no eventual statement sees.
-/

namespace RegretKappa.UnknownBT

open RegretKappa Filter Topology Real

/-! ## Anytime learners -/

/-- An anytime learner. In round `t` it sees the features `x 0, ..., x t` and the outcomes
`y 0, ..., y (t - 1)` and predicts a real number; it is given no horizon and no bound. -/
structure AnytimeLearner where
  /-- The prediction in round `t`, from the features up to round `t` and the earlier outcomes. -/
  predict : (t : ℕ) → (Fin (t + 1) → ℝ) → (Fin t → ℝ) → ℝ

/-- The restriction of an anytime learner to the horizon `T`: in round `t < T` it predicts as `L`
in round `t`. -/
def AnytimeLearner.restrict (L : AnytimeLearner) (T : ℕ) : Learner T where
  predict t xs ys := L.predict t xs ys

/-! ## The targets -/

-- The name repeats the last component of the namespace (`RegretKappa.UnknownBT.UnknownBT`), which
-- the linter `dupNamespace` reports; both stay.
set_option linter.dupNamespace false in
/-- **B and T unknown (target).** One anytime learner, chosen first: for every `ε > 0`, for every
large horizon `T`, for every `B > 0`, its regret is at most `(3 + ε) B² log T` on every play with
`|y t| ≤ B`. -/
def UnknownBT : Prop :=
  ∃ L : AnytimeLearner, ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ B : ℝ, 0 < B →
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret (L.restrict T) x y ≤ (3 + ε) * B ^ 2 * log T

/-- **B and T unknown, every horizon.** One anytime learner and one sequence `ε_T → 0`: for every
`T ≥ 2`, every `B > 0` and every play with `|y t| ≤ B`, its regret is at most `(3 + ε_T) B² log T`. -/
def UnknownBTEveryT : Prop :=
  ∃ L : AnytimeLearner, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ T : ℕ, 2 ≤ T → ∀ B : ℝ, 0 < B →
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret (L.restrict T) x y ≤ (3 + ε T) * B ^ 2 * log T

/-- **T unknown, B known.** For every `B > 0` one anytime learner (it may depend on `B`): for
every `ε > 0`, for every large `T`, its regret is at most `(3 + ε) B² log T` on every play with
`|y t| ≤ B`. -/
def UnknownT : Prop :=
  ∀ B : ℝ, 0 < B → ∃ L : AnytimeLearner, ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret (L.restrict T) x y ≤ (3 + ε) * B ^ 2 * log T

/-- **B unknown, T known.** For every `ε > 0` and every large `T`, one learner of horizon `T` (it
may depend on `ε` and `T`) whose regret is at most `(3 + ε) B² log T` for every `B > 0` and every
play with `|y t| ≤ B`. -/
def UnknownB : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T, ∀ B : ℝ, 0 < B →
    ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) → regret L x y ≤ (3 + ε) * B ^ 2 * log T

/-- **Optimality of the constant 3.** For every `B > 0` and `ε > 0`, for every large `T`, every
anytime learner has a play with `|y t| ≤ B` on which its regret is at least `(3 - ε) B² log T`. -/
def Optimality : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : AnytimeLearner,
    ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧ (3 - ε) * B ^ 2 * log T ≤ regret (L.restrict T) x y

/-- The worst ratio of `L` at the horizon `T`: the supremum over `B > 0` and the plays with
`|y t| ≤ B` of `Regret_T / (B² log T)`, in `EReal`. -/
noncomputable def worstRatio (L : AnytimeLearner) (T : ℕ) : EReal :=
  ⨆ (B : ℝ) (_ : 0 < B) (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B),
    (regret (L.restrict T) x y : EReal) / ((B ^ 2 * log T : ℝ) : EReal)

/-- The best leading constant for learners that know neither `B` nor `T`: the infimum over
anytime learners of `limsup_T worstRatio L T`. -/
noncomputable def bestConstant : EReal :=
  ⨅ L : AnytimeLearner, limsup (worstRatio L) atTop

/-- **The answer (target).** Some anytime learner has worst ratio tending to `3`, and every anytime
learner has worst ratio at least `3 - o(1)`. -/
def BestConstantThree : Prop :=
  (∃ L : AnytimeLearner, Tendsto (worstRatio L) atTop (𝓝 3)) ∧
    ∀ L : AnytimeLearner, (3 : EReal) ≤ liminf (worstRatio L) atTop

/-! ## The explicit forms -/

/-- The prediction of the potential learner at the level `lam`, from `S = ∑_{i<t} x_i y_i`,
`V = ∑_{i<t} x_i²` and the current feature `x`:
`ε clip_{[-1,1]}(½ log((λ + Γ(ρ √(1-s) + √s)) / (λ + Γ(ρ √(1-s) - √s))))` with `ρ = S/√V` (`0` if
`V = 0`), `s = x²/(V + x²)` (`0` if `V + x² = 0`), `ε = sign x` (`1` if `x = 0`); `Γ` is
`RegretKappa.UpperSharp.Gam`. At the level `λ₀ + 3 (T - t - 1)` it is the prediction
`RegretKappa.UpperSharp.predU` of the known-horizon learner. -/
noncomputable def predLam (lam S V x : ℝ) : ℝ :=
  let ρ := if V = 0 then 0 else S / √V
  let s := if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)
  let ε : ℝ := if x < 0 then -1 else 1
  ε * UpperSharp.clip (log ((lam + UpperSharp.Gam (ρ * √(1 - s) + √s)) /
    (lam + UpperSharp.Gam (ρ * √(1 - s) - √s))) / 2)

/-- The level of the learner `learnerB` in round `t`: `λ = 3 log(t + 2) / log((t + 3)/(t + 2))`,
the ratio `a/b` of the weights `a = 3/log(t + 3)`, `b = 1/log(t + 2) - 1/log(t + 3)`. -/
noncomputable def lamB (t : ℕ) : ℝ := 3 * log (t + 2) / log ((t + 3) / (t + 2))

/-- The anytime learner of `TheoremB`, for outcomes in `[-1, 1]`: in round `t` the prediction
`predLam` at the level `lamB t`. -/
noncomputable def learnerB : AnytimeLearner where
  predict t xs ys := predLam (lamB t) (∑ i : Fin t, xs (Fin.castSucc i) * ys i)
    (∑ i : Fin t, xs (Fin.castSucc i) ^ 2) (xs (Fin.last t))

/-- The largest `|y i|` of a finite sequence, `0` for the empty one. -/
noncomputable def runMax {n : ℕ} (y : Fin n → ℝ) : ℝ := Finset.univ.fold max 0 fun i => |y i|

/-- The anytime learner that knows neither `B` nor `T`: in round `t`, with `M = max_{i<t} |y i|`,
it predicts `0` if `M = 0` and otherwise `M` times the prediction of `learnerB` on the outcomes
divided by `M`. -/
noncomputable def learnerBT : AnytimeLearner where
  predict t xs ys :=
    if runMax ys = 0 then 0 else runMax ys * learnerB.predict t xs fun i => ys i / runMax ys

/-- The constant `K = 2 log(3/log 2 + 2e^{-1/2}(1/log 2 - 1/log 3)) - log(2π)` of `TheoremB`. -/
noncomputable def constK : ℝ :=
  2 * log (3 / log 2 + 2 * exp (-1 / 2) * (1 / log 2 - 1 / log 3)) - log (2 * π)

/-- **`TheoremB`**, first form (`B = 1` known, `T` unknown): for `T ≥ 1` and every play with
outcomes in `[-1, 1]`,
`Regret_T ≤ 3 log T + 4 log log(T + 2) + K + 2 log(1 + 1/√T) + 2 log(1 + 2/T)`. -/
def TheoremB : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ 1) →
    regret (learnerB.restrict T) x y ≤
      3 * log T + 4 * log (log (T + 2)) + constK + 2 * log (1 + 1 / √(T : ℝ)) + 2 * log (1 + 2 / T)

/-- **`TheoremB`**, second form: for `T ≥ 1` and every play with outcomes in `[-1, 1]`,
`Regret_T ≤ 3 log T + 4 log log(T + 2) + 1.3706 + 2/√T + 4/T`. -/
def TheoremBNum : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ x y : Fin T → ℝ, (∀ t, |y t| ≤ 1) →
    regret (learnerB.restrict T) x y ≤
      3 * log T + 4 * log (log (T + 2)) + 1.3706 + 2 / √(T : ℝ) + 4 / T

/-- **The scale-free bound with the constant `c`** (`B` and `T` unknown): for `T ≥ 1` and every
play, `Regret_T ≤ M_T² (3 log T + 4 log log(T + 2) + c + 2/√T + 4/T)`, `M_T = max_t |y t|`. -/
def ScaleFreeBound (c : ℝ) : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ x y : Fin T → ℝ,
    regret (learnerBT.restrict T) x y ≤
      runMax y ^ 2 * (3 * log T + 4 * log (log (T + 2)) + c + 2 / √(T : ℝ) + 4 / T)

end RegretKappa.UnknownBT
