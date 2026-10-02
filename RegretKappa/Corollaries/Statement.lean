import RegretKappa.Statement

/-!
# Target statements: randomized learners and bounded features

The paper, Corollary 5.1 and Remark 5.2, in asymptotic form, on the model of
`RegretKappa/Statement.lean` (`Learner`, `regret`; rounds indexed by `Fin T`).

Randomized learners (the paper, Section 2.1). A randomized learner
draws its predictions from laws that depend on the past, with randomness independent of the
adversary's, and conditionally on its randomness it is deterministic. Here it is a probability
space `(Ω, μ)` with a family `L : Ω → Learner T` of deterministic learners, each prediction
measurable in `ω` for each fixed history (`IsRandLearner`). Its own earlier predictions are
functions of `ω` and of the history, so they are not passed. The universe of `Ω` is a parameter
of the statements.

Expected regret. On every play the regret is at least `-∑ y_t ^ 2` (`neg_sum_sq_le_regret`, from
`θ = 0`), so `E Reg = E (Reg + ∑ y ^ 2) - ∑ y ^ 2`, where the first expectation is the lintegral
of a nonnegative function, in `[0, ∞]`. This is `expRegret`, in `EReal`, with no integrability
assumption: it is the Bochner integral of the regret when the regret is integrable
(`expRegret_eq_integral`), and `⊤` when the lintegral is infinite. A deterministic learner is a
randomized learner with a constant family, and its expected regret is its regret
(`isRandLearner_const`, `expRegret_const`).

Adversaries. Against a fixed play `(x, y)` the expected regret is `expRegret μ L x y`. An adversary
that ignores the predictions and plays `(x i, y i)` with probability `w i`, for `i` in a finite
type, is a random play independent of the learner's randomness, one randomized adaptive adversary
in the sense of the paper, Section 2.1. Its expected regret `advRegret μ L w x y` is taken over
`ω` and `i` in the same way: with one play of probability `1` it is `expRegret`
(`advRegret_unique`), and against a deterministic learner it is the average of the regrets on
the plays, weighted by their probabilities (`advRegret_const`).

Targets, in the asymptotic form of `RegretKappa.LowerBound`: the paper's bound `B ^ 2 b(T)` for
`T ≥ T₀` becomes `(3 - ε) B ^ 2 log T` for every `ε > 0` and every large `T`.
* `RandLowerBound` (Remark 5.2, randomized learners, against fixed plays): for every `B > 0` and
  `ε > 0`, for every large `T`, every randomized learner has a play with `|y_t| ≤ B` on which its
  expected regret is at least `(3 - ε) B ^ 2 log T`;
* `BoundedFeatures` (Corollary 5.1, deterministic learners): for every `B > 0` and `ε > 0`, for
  every large `T`, every learner has a play with features in `[0, 1]` and outcomes in `{-B, 0, B}`
  on which its regret is at least `(3 - ε) B ^ 2 log T`;
* `BoundedFeaturesRand` (Corollary 5.1, randomized learners): the same for every randomized learner
  and its expected regret;
* `BoundedFeaturesAdv` (Corollary 5.1, the adversary): for every `B > 0` and `ε > 0`, for every
  large `T`, there is an adversary that ignores the predictions, with finitely many plays, each
  with features in `[0, 1]` and outcomes in `{-B, 0, B}`, against which every randomized learner
  has expected regret at least `(3 - ε) B ^ 2 log T`.

The constant over bounded features, in the form of `RegretKappa.KappaEqThree`:
* `minimaxRegretBF T B`: the minimax regret over the plays with features in `[0, 1]` and outcomes
  in `{-B, 0, B}`, in `EReal`;
* `BoundedFeaturesUpper`: for every `B > 0` and `ε > 0`, for every large `T`, some learner has
  regret at most `(3 + ε) B ^ 2 log T` on every such play;
* `KappaEqThreeBF`: for every `B > 0`, `minimaxRegretBF T B / (B ^ 2 log T)` tends to `3`.

Relations proved here: `BoundedFeaturesRand` implies `RandLowerBound` and `BoundedFeatures`, and
each of these implies `RegretKappa.LowerBound`; `RegretKappa.UpperBound` implies
`BoundedFeaturesUpper`, since those plays have `|y t| ≤ B`; `BoundedFeaturesUpper` and
`BoundedFeatures` imply `KappaEqThreeBF` (`kappaEqThreeBF_of_bounds`, the proof of
`RegretKappa.kappaEqThree_iff`).

The explicit upper half over bounded features: `BoundedFeaturesUpperU`, for every `B > 0` and every
`T`, `minimaxRegretBF T B ≤ B ^ 2 U(T)` with the bound `U(T)` of `RegretKappa.UpperSharp.TheoremU`.

Outcomes in `[-B, B]`: `minimaxRegretBFI T B`, the minimax regret over the plays with features in
`[0, 1]` and outcomes in `[-B, B]`; `KappaEqThreeBFI`, its constant `3`;
`BoundedFeaturesUpperUI`, its bound `B ^ 2 U(T)`. It lies between `minimaxRegretBF T B` and
`RegretKappa.minimaxRegret T B` (`minimaxRegretBF_le_BFI`, `minimaxRegretBFI_le`), so
`KappaEqThreeBF` and `RegretKappa.KappaEqThree` give `KappaEqThreeBFI` (`kappaEqThreeBFI_of`).
-/

namespace RegretKappa.Corollaries

open MeasureTheory Filter

universe u

/-- On every play the regret is at least `-∑ y_t ^ 2`: the loss of the learner is nonnegative, and
the best linear loss is at most the loss of `θ = 0`, which is `∑ y_t ^ 2`. -/
theorem neg_sum_sq_le_regret {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) :
    -∑ t, y t ^ 2 ≤ regret L x y := by
  have h0 := bestLinearLoss_le x y 0
  have h1 : 0 ≤ learnerLoss L x y := by unfold learnerLoss; positivity
  have h2 : linearLoss 0 x y = ∑ t, y t ^ 2 := by simp [linearLoss]
  unfold regret
  linarith

/-- `L` is a randomized learner on `(Ω, μ)`: `μ` is a probability measure, and for each round and
each history the prediction of `L ω` is a measurable function of `ω`. -/
def IsRandLearner {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (t : Fin T) (xs : Fin (t + 1) → ℝ) (ys : Fin t → ℝ),
      Measurable fun ω => (L ω).predict t xs ys

/-- The expected regret of the randomized learner `L` on `(Ω, μ)` on the play `(x, y)`, in
`EReal`: `E (Reg + ∑ y ^ 2) - ∑ y ^ 2`, the first expectation a lintegral in `[0, ∞]`. -/
noncomputable def expRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) (x y : Fin T → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (regret (L ω) x y + ∑ t, y t ^ 2) ∂μ : ENNReal) : EReal) -
    ((∑ t, y t ^ 2 : ℝ) : EReal)

/-- The expected regret of the randomized learner `L` on `(Ω, μ)` against the adversary that
ignores the predictions and plays `(x i, y i)` with probability `w i`, in `EReal`:
`E (Reg + ∑ y ^ 2) - E ∑ y ^ 2` over `ω` and `i`, the first expectation a lintegral in
`[0, ∞]`. -/
noncomputable def advRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) {ι : Type*} [Fintype ι] (w : ι → ℝ) (x y : ι → Fin T → ℝ) : EReal :=
  ((∫⁻ ω, ∑ i, ENNReal.ofReal (w i) *
      ENNReal.ofReal (regret (L ω) (x i) (y i) + ∑ t, y i t ^ 2) ∂μ : ENNReal) : EReal) -
    ((∑ i, w i * ∑ t, y i t ^ 2 : ℝ) : EReal)

/-- **Remark 5.2, randomized learners on one play (target).** For every `B > 0` and `ε > 0`, for
every large horizon `T`, every randomized learner has a play with `|y t| ≤ B` on which its
expected regret is at least `(3 - ε) B ^ 2 log T`. -/
def RandLowerBound : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T), IsRandLearner μ L →
      ∃ x y : Fin T → ℝ, (∀ t, |y t| ≤ B) ∧
        (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤ expRegret μ L x y

/-- **Corollary 5.1, deterministic learners (target).** For every `B > 0` and `ε > 0`, for every
large horizon `T`, every learner has a play with features in `[0, 1]` and outcomes in `{-B, 0, B}`
on which its regret is at least `(3 - ε) B ^ 2 log T`. -/
def BoundedFeatures : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ L : Learner T,
    ∃ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
      (3 - ε) * B ^ 2 * Real.log T ≤ regret L x y

/-- **Corollary 5.1, randomized learners (target).** For every `B > 0` and `ε > 0`, for every
large horizon `T`, every randomized learner has a play with features in `[0, 1]` and outcomes in
`{-B, 0, B}` on which its expected regret is at least `(3 - ε) B ^ 2 log T`. -/
def BoundedFeaturesRand : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T), IsRandLearner μ L →
      ∃ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧
        (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤ expRegret μ L x y

/-- **Corollary 5.1, the adversary (target).** For every `B > 0` and `ε > 0`, for every large
horizon `T`, there is an adversary that ignores the predictions and plays `(x i, y i)` with
probability `w i`, `i` in a finite type, every play with features in `[0, 1]` and outcomes in
`{-B, 0, B}`, against which every randomized learner has expected regret at least
`(3 - ε) B ^ 2 log T`. -/
def BoundedFeaturesAdv : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x y : ι → Fin T → ℝ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      (∀ i t, x i t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i t, y i t ∈ ({-B, 0, B} : Set ℝ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (L : Ω → Learner T),
        IsRandLearner μ L → (((3 - ε) * B ^ 2 * Real.log T : ℝ) : EReal) ≤ advRegret μ L w x y

/-! ### The definitions are the intended ones -/

/-- A deterministic learner, as a constant family on a probability space, is a randomized
learner. -/
theorem isRandLearner_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ℕ} (L : Learner T) : IsRandLearner μ fun _ : Ω => L :=
  ⟨inferInstance, fun _ _ _ => measurable_const⟩

/-- `ofReal` of a nonnegative real, as an extended real, is the real itself. -/
theorem coe_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ((ENNReal.ofReal a : ENNReal) : EReal) = a := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left ha]

/-- The expected regret of a constant family is the regret of the learner. -/
theorem expRegret_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (L : Learner T) (x y : Fin T → ℝ) :
    expRegret μ (fun _ : Ω => L) x y = (regret L x y : EReal) := by
  have h := neg_sum_sq_le_regret L x y
  unfold expRegret
  rw [lintegral_const, measure_univ, mul_one, coe_ofReal_of_nonneg (by linarith),
    ← EReal.coe_sub, add_sub_cancel_right]

/-- When the regret is integrable, the expected regret is its Bochner integral. -/
theorem expRegret_eq_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : ℕ} (L : Ω → Learner T) (x y : Fin T → ℝ)
    (hi : Integrable (fun ω => regret (L ω) x y) μ) :
    expRegret μ L x y = ((∫ ω, regret (L ω) x y ∂μ : ℝ) : EReal) := by
  have hi' : Integrable (fun ω => regret (L ω) x y + ∑ t, y t ^ 2) μ :=
    hi.add (integrable_const _)
  have hnn : 0 ≤ᵐ[μ] fun ω => regret (L ω) x y + ∑ t, y t ^ 2 :=
    Filter.Eventually.of_forall fun ω => by
      have := neg_sum_sq_le_regret (L ω) x y
      simp only [Pi.zero_apply]
      linarith
  unfold expRegret
  rw [← ofReal_integral_eq_lintegral_ofReal hi' hnn,
    coe_ofReal_of_nonneg (integral_nonneg_of_ae hnn), ← EReal.coe_sub,
    integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul,
    add_sub_cancel_right]

/-- Against a deterministic learner, the expected regret of the adversary is the average of the
regrets on its plays, weighted by their probabilities. -/
theorem advRegret_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} (L : Learner T) {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (x y : ι → Fin T → ℝ) :
    advRegret μ (fun _ : Ω => L) w x y = ((∑ i, w i * regret L (x i) (y i) : ℝ) : EReal) := by
  have h : ∀ i, 0 ≤ regret L (x i) (y i) + ∑ t, y i t ^ 2 := fun i => by
    linarith [neg_sum_sq_le_regret L (x i) (y i)]
  have hs : ∑ i, ENNReal.ofReal (w i) * ENNReal.ofReal (regret L (x i) (y i) + ∑ t, y i t ^ 2) =
      ENNReal.ofReal (∑ i, w i * (regret L (x i) (y i) + ∑ t, y i t ^ 2)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hw i) (h i)]
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hw i)).symm
  unfold advRegret
  rw [lintegral_const, measure_univ, mul_one, hs,
    coe_ofReal_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (h i)), ← EReal.coe_sub]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- An adversary with one play, of probability `1`, has the expected regret of that play. -/
theorem advRegret_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (L : Ω → Learner T) (x y : Fin T → ℝ) :
    advRegret μ L (fun _ : Unit => (1 : ℝ)) (fun _ => x) (fun _ => y) = expRegret μ L x y := by
  simp [advRegret, expRegret]

/-! ### Relations between the targets -/

theorem randLowerBound_of_rand (h : BoundedFeaturesRand.{u}) : RandLowerBound.{u} := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  intro Ω _ μ L hL
  obtain ⟨x, y, -, hy, hc⟩ := hT Ω μ L hL
  refine ⟨x, y, fun t => ?_, hc⟩
  rcases hy t with h1 | h1 | h1 <;> rw [h1] <;> simp [abs_of_pos hB, hB.le]

theorem boundedFeatures_of_rand (h : BoundedFeaturesRand.{0}) : BoundedFeatures := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  intro L
  obtain ⟨x, y, hx, hy, hc⟩ := hT Unit (Measure.dirac ()) (fun _ => L)
    (isRandLearner_const _ L)
  rw [expRegret_const] at hc
  exact ⟨x, y, hx, hy, EReal.coe_le_coe_iff.1 hc⟩

theorem lowerBound_of_randLowerBound (h : RandLowerBound.{0}) : LowerBound := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  intro L
  obtain ⟨x, y, hy, hc⟩ := hT Unit (Measure.dirac ()) (fun _ => L) (isRandLearner_const _ L)
  rw [expRegret_const] at hc
  exact ⟨x, y, hy, EReal.coe_le_coe_iff.1 hc⟩

theorem lowerBound_of_boundedFeatures (h : BoundedFeatures) : LowerBound := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T hT
  intro L
  obtain ⟨x, y, -, hy, hc⟩ := hT L
  refine ⟨x, y, fun t => ?_, hc⟩
  rcases hy t with h1 | h1 | h1 <;> rw [h1] <;> simp [abs_of_pos hB, hB.le]

/-! ### The constant over bounded features -/

/-- Outcomes in `{-B, 0, B}` have `|y| ≤ B`. -/
theorem abs_le_of_mem {B y : ℝ} (hB : 0 < B) (hy : y ∈ ({-B, 0, B} : Set ℝ)) : |y| ≤ B := by
  rcases hy with h | h | h <;> rw [h] <;> simp [abs_of_pos hB, hB.le]

/-- The minimax regret at horizon `T` over the plays with features in `[0, 1]` and outcomes in
`{-B, 0, B}`: the infimum over learners of the supremum over these plays of the regret, in
`EReal`. -/
noncomputable def minimaxRegretBF (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1)
    (_ : ∀ t, y t ∈ ({-B, 0, B} : Set ℝ)), (regret L x y : EReal)

/-- **The upper half over bounded features (target).** For every `B > 0` and `ε > 0`, for
every large horizon `T` there is a learner whose regret is at most `(3 + ε) B ^ 2 log T` on every
play with features in `[0, 1]` and outcomes in `{-B, 0, B}`. -/
def BoundedFeaturesUpper : Prop :=
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∃ L : Learner T,
    ∀ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) →
      regret L x y ≤ (3 + ε) * B ^ 2 * Real.log T

/-- **The constant over bounded features (target).** For every `B > 0`,
`minimaxRegretBF T B / (B ^ 2 log T)` tends to `3` as `T → ∞`, in `EReal`. -/
def KappaEqThreeBF : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxRegretBF T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop (nhds 3)

/-- The upper bound over all plays with `|y t| ≤ B` holds over bounded features. -/
theorem boundedFeaturesUpper_of_upperBound (h : UpperBound) : BoundedFeaturesUpper := by
  intro B hB ε hε
  filter_upwards [h B hB ε hε] with T ⟨L, hL⟩
  exact ⟨L, fun x y _ hy => hL x y fun t => abs_le_of_mem hB (hy t)⟩

/-- A learner with regret at most `c` on every play with bounded features bounds the minimax
regret over them by `c`. -/
theorem minimaxRegretBF_le_of_learner {T : ℕ} {B c : ℝ} (L : Learner T)
    (h : ∀ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) →
      regret L x y ≤ c) :
    minimaxRegretBF T B ≤ (c : EReal) :=
  iInf_le_of_le L (iSup₂_le fun x y => iSup₂_le fun hx hy => EReal.coe_le_coe_iff.2 (h x y hx hy))

/-- If every learner has regret at least `c` on some play with bounded features, the minimax
regret over them is at least `c`. -/
theorem le_minimaxRegretBF {T : ℕ} {B c : ℝ}
    (h : ∀ L : Learner T, ∃ x y : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, y t ∈ ({-B, 0, B} : Set ℝ)) ∧ c ≤ regret L x y) :
    (c : EReal) ≤ minimaxRegretBF T B :=
  le_iInf fun L => by
    obtain ⟨x, y, hx, hy, hc⟩ := h L
    exact le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hx (le_iSup_of_le hy
      (EReal.coe_le_coe_iff.2 hc))))

/-- The two bounds over bounded features give the constant `3`. -/
theorem kappaEqThreeBF_of_bounds (hU : BoundedFeaturesUpper) (hL : BoundedFeatures) :
    KappaEqThreeBF := by
  intro B hB
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨r, har, hr3⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hr3' : r < 3 := by rw [← coe_three] at hr3; exact EReal.coe_lt_coe_iff.1 hr3
    filter_upwards [hL B hB (3 - r) (by linarith), eventually_ge_atTop 2] with T hT hT2
    have hD := scale_pos hB hT2
    refine har.trans_le ?_
    rw [EReal.le_div_iff_mul_le (EReal.coe_pos.2 hD) (EReal.coe_ne_top _), ← EReal.coe_mul]
    have hm := le_minimaxRegretBF hT
    refine le_of_eq_of_le ?_ hm
    congr 1
    ring
  · obtain ⟨r, h3r, hra⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have h3r' : 3 < r := by rw [← coe_three] at h3r; exact EReal.coe_lt_coe_iff.1 h3r
    filter_upwards [hU B hB (r - 3) (by linarith), eventually_ge_atTop 2] with T hT hT2
    have hD := scale_pos hB hT2
    refine lt_of_le_of_lt ?_ hra
    rw [EReal.div_le_iff_le_mul (EReal.coe_pos.2 hD) (EReal.coe_ne_top _), ← EReal.coe_mul]
    obtain ⟨L, hL⟩ := hT
    refine (minimaxRegretBF_le_of_learner L hL).trans_eq ?_
    congr 1
    ring

open Real in
/-- **The explicit upper half over bounded features (target).** For every `B > 0` and every
horizon `T`, the minimax regret over the plays with features in `[0, 1]` and outcomes in
`{-B, 0, B}` is at most `B ^ 2 U(T)`, with `U(T) = 2 log(e² + (√T + 1)(3T + 2e^{-1/2})/√(2π))`,
the bound of `RegretKappa.UpperSharp.TheoremU` for outcomes in `[-1, 1]`. -/
def BoundedFeaturesUpperU : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ,
    minimaxRegretBF T B ≤
      ((B ^ 2 * (2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))) : ℝ) :
        EReal)

/-! ### Bounded features with outcomes in `[-B, B]` -/

/-- The minimax regret at horizon `T` over the plays with features in `[0, 1]` and outcomes in
`[-B, B]`, in `EReal`. -/
noncomputable def minimaxRegretBFI (T : ℕ) (B : ℝ) : EReal :=
  ⨅ L : Learner T, ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1)
    (_ : ∀ t, |y t| ≤ B), (regret L x y : EReal)

/-- **The constant over bounded features, outcomes in `[-B, B]` (target).** For every `B > 0`,
`minimaxRegretBFI T B / (B ^ 2 log T)` tends to `3` as `T → ∞`, in `EReal`. -/
def KappaEqThreeBFI : Prop :=
  ∀ B : ℝ, 0 < B →
    Tendsto (fun T : ℕ => minimaxRegretBFI T B / ((B ^ 2 * Real.log T : ℝ) : EReal)) atTop
      (nhds 3)

open Real in
/-- **The explicit upper half over bounded features, outcomes in `[-B, B]` (target).**
For every `B > 0` and every horizon `T`, `minimaxRegretBFI T B ≤ B ^ 2 U(T)`, with `U(T)` as in
`BoundedFeaturesUpperU`. -/
def BoundedFeaturesUpperUI : Prop :=
  ∀ B : ℝ, 0 < B → ∀ T : ℕ,
    minimaxRegretBFI T B ≤
      ((B ^ 2 * (2 * log (exp 2 + (√(T : ℝ) + 1) * (3 * T + 2 * exp (-1 / 2)) / √(2 * π))) : ℝ) :
        EReal)

/-- Outcomes in `{-B, 0, B}` lie in `[-B, B]`, so the supremum over them is smaller. -/
theorem minimaxRegretBF_le_BFI (T : ℕ) {B : ℝ} (hB : 0 < B) :
    minimaxRegretBF T B ≤ minimaxRegretBFI T B :=
  iInf_mono fun _ => iSup_mono fun x => iSup_mono fun y => iSup₂_le fun hx hy =>
    le_iSup₂_of_le (f := fun (_ : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) (_ : ∀ t, |y t| ≤ B) => _) hx
      (fun t => abs_le_of_mem hB (hy t)) le_rfl

/-- Features in `[0, 1]` are real features, so the supremum over them is smaller. -/
theorem minimaxRegretBFI_le (T : ℕ) (B : ℝ) : minimaxRegretBFI T B ≤ minimaxRegret T B :=
  iInf_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_le fun _ => le_rfl

/-- `minimaxRegretBFI` lies between `minimaxRegretBF` and `minimaxRegret`, so it has the constant
`3` when both do. -/
theorem kappaEqThreeBFI_of (hBF : KappaEqThreeBF) (hK : KappaEqThree) : KappaEqThreeBFI := by
  intro B hB
  have hD : ∀ T : ℕ, (0 : EReal) ≤ ((B ^ 2 * Real.log T : ℝ) : EReal) := fun T =>
    EReal.coe_nonneg.2 (mul_nonneg (sq_nonneg B) (Real.log_natCast_nonneg T))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hBF B hB) (hK B hB)
    (fun T => EReal.div_le_div_right_of_nonneg (hD T) (minimaxRegretBF_le_BFI T hB))
    (fun T => EReal.div_le_div_right_of_nonneg (hD T) (minimaxRegretBFI_le T B))

end RegretKappa.Corollaries
