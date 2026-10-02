import RegretKappa.MainStatement
import RegretKappa.LowerSharp.Assembly
import RegretKappa.Corollaries.UpperU
import RegretKappa.Corollaries.Explicit

/-!
# The main theorem

`RegretKappa.main : RegretKappa.MainTheorem` and its companion for bounded features,
`RegretKappa.mainBoundedFeatures : RegretKappa.MainBoundedFeatures`, follow from the forms with
the explicit lower and upper bounds, `RegretKappa.mainChain` and
`RegretKappa.mainBoundedFeaturesChain`, and from `U(T) ≤ 3 log T + 0.37` for `T ≥ 355713`
(`boundU_le`). These come from

* the lower bound: `LowerSharp.lowerSharpBound` (one play, every `B > 0`),
  `LowerSharp.lowerSharpAdv` (the finite adversary, `B = 1`) and `LowerSharp.lowerSharpSimplified`
  (the simplified forms of `b(T)`);
* the upper bound: `Corollaries.regret_rescale_learnerU_le` (the learner of `UpperSharp`
  rescaled to outcomes in `[-B, B]`), `Corollaries.boundedFeaturesUpperUI` and, for the second
  form of `U(T)`, `UpperSharp.ulog_bound`;
* the transfer to bounded features: `Corollaries.boundedFeatures_of_mixture`.

The limit `KappaEqThree` follows from the closed bounds (`closedBounds`) by the squeeze of the
paper: `2 log log T + 15.2 = o(log T)` (`eventually_lower`) and `0.37 = o(log T)`
(`eventually_upper`) give the two halves `UpperBound` and `LowerBound` of
`RegretKappa/Statement.lean`, and its bridge `kappaEqThree_of_bounds` gives the limit
(`kappaEqThree_squeeze`). The randomized lower bound `Corollaries.RandLowerBound` follows from
the bounded-features theorem (`randLowerBound`): some play of the adversary does at least as well as the
adversary.
-/

namespace RegretKappa

universe u
open Filter


/-- `B² (3 log T - 2 log log T - 15.2) ≤ B² b(T)` for `T ≥ 355713`. -/
theorem boundL_le_bT {B : ℝ} {T : ℕ} (hT : LowerSharp.T0 ≤ T) :
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) := by
  obtain ⟨h1, h2⟩ := LowerSharp.lowerSharpSimplified T hT
  exact EReal.coe_le_coe_iff.2
    (mul_le_mul_of_nonneg_left (by unfold boundL; linarith) (sq_nonneg B))

/-- The explicit lower and upper bounds: for `B > 0` and `T ≥ 355713`,
`B² (3 log T - 2 log log T - 15.2) ≤ B² b(T) ≤ Reg*_T(B) ≤ B² U(T)`. -/
theorem chainBounds (B : ℝ) (hB : 0 < B) (T : ℕ) (hT : LowerSharp.T0 ≤ T) :
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ∧
      ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) ≤ minimaxRegret T B ∧
      minimaxRegret T B ≤ ((B ^ 2 * boundU T : ℝ) : EReal) := by
  refine ⟨boundL_le_bT hT, ?_, ?_⟩
  · exact le_minimaxRegret fun L => LowerSharp.lowerSharpBound B hB T hT L
  · exact minimaxRegret_le_of_learner (Lower.rescale (UpperSharp.learnerU T) B⁻¹)
      fun x y hy => Corollaries.regret_rescale_learnerU_le hB T x y hy

/-- **Bounded features, with the explicit lower and upper bounds**
(`RegretKappa.MainBoundedFeaturesChain`). -/
theorem mainBoundedFeaturesChain : MainBoundedFeaturesChain.{u} := by
  intro B hB T hT
  obtain ⟨ι, hι, w, x, y, hw, hs, hx, hy, hb⟩ := LowerSharp.lowerSharpAdv T hT
  obtain ⟨⟨x', y', hx', hy', hadv⟩, -, -, hBF, -⟩ :=
    Corollaries.boundedFeatures_of_mixture.{u} w hw hs x y hx hy hb hB
  exact ⟨⟨ι, hι, w, x', y', hw, hs, hx', hy', hadv⟩, boundL_le_bT hT, hBF,
    Corollaries.minimaxRegretBF_le_BFI T hB, Corollaries.boundedFeaturesUpperUI B hB T⟩

/-- `U(T) ≤ 3 log T + 0.37` for `T ≥ 355713`. -/
theorem boundU_le {T : ℕ} (hT : LowerSharp.T0 ≤ T) : boundU T ≤ 3 * Real.log T + 0.37 := by
  have hT' : (355713 : ℝ) ≤ T := by
    have : ((LowerSharp.T0 : ℕ) : ℝ) ≤ T := by exact_mod_cast hT
    simpa [LowerSharp.T0] using this
  have hu := UpperSharp.ulog_bound (T := (T : ℝ)) (by linarith)
  have hs : (596 : ℝ) ≤ √(T : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  -- `2 log(3/√(2π)) = log(9/(2π)) ≤ 0.366`, since `9/(2π) ≤ 1 + 0.366 + 0.366²/2 ≤ e^{0.366}`
  have hlog : 2 * Real.log (3 / √(2 * Real.pi)) ≤ 0.366 := by
    have hpi := Real.pi_gt_d6
    have hpos : 0 < 3 / √(2 * Real.pi) := by positivity
    have hsq : (3 / √(2 * Real.pi)) ^ 2 = 9 / (2 * Real.pi) := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; norm_num
    rw [show 2 * Real.log (3 / √(2 * Real.pi)) = Real.log ((3 / √(2 * Real.pi)) ^ 2) by
      rw [Real.log_pow]; norm_num, hsq, Real.log_le_iff_le_exp (by positivity)]
    calc 9 / (2 * Real.pi) ≤ 1 + 0.366 + 0.366 ^ 2 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
      _ ≤ Real.exp 0.366 := Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h2 : 2 / √(T : ℝ) ≤ 2 / 596 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h3 : 0.81 / (T : ℝ) ≤ 0.81 / 355713 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT'
  have h4 : 12.35 / ((T : ℝ) * √(T : ℝ)) ≤ 12.35 / (355713 * 596) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul hT' hs (by norm_num) (by positivity))
  unfold boundU
  norm_num at h2 h3 h4
  linarith

/-- The closed bounds: for `B > 0` and `T ≥ 355713`,
`B² (3 log T - 2 log log T - 15.2) ≤ Reg*_T(B) ≤ B² (3 log T + 0.37)`. -/
theorem closedBounds (B : ℝ) (hB : 0 < B) (T : ℕ) (hT : LowerSharp.T0 ≤ T) :
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ minimaxRegret T B ∧
      minimaxRegret T B ≤ ((B ^ 2 * (3 * Real.log T + 0.37) : ℝ) : EReal) := by
  obtain ⟨h1, h2, h3⟩ := chainBounds B hB T hT
  exact ⟨h1.trans h2, h3.trans
    (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left (boundU_le hT) (sq_nonneg B)))⟩

/-- `log T` tends to infinity along the integers. -/
theorem tendsto_log_nat : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- For `ε > 0`, eventually `(3 - ε) log T < 3 log T - 2 log log T - 15.2`, since
`2 log log T + 15.2 = o(log T)`. -/
theorem eventually_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, (3 - ε) * Real.log T < boundL T := by
  have ho := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_log_nat).def
    (show 0 < ε / 4 by positivity)
  filter_upwards [ho, tendsto_log_nat.eventually_gt_atTop (30.4 / ε)] with T h1 h2
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at h1
  have hlog : 0 < Real.log T := lt_of_le_of_lt (by positivity) h2
  rw [abs_of_pos hlog] at h1
  have h3 : 30.4 < ε * Real.log T := by rwa [div_lt_iff₀ hε, mul_comm] at h2
  have h4 := le_abs_self (Real.log (Real.log T))
  unfold boundL
  nlinarith

/-- For `ε > 0`, eventually `3 log T + 0.37 < (3 + ε) log T`. -/
theorem eventually_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, 3 * Real.log T + 0.37 < (3 + ε) * Real.log T := by
  filter_upwards [tendsto_log_nat.eventually_gt_atTop (0.37 / ε)] with T h
  rw [div_lt_iff₀ hε] at h
  linarith

/-- The upper half of the limit (`RegretKappa.UpperBound`), from the closed upper bound. -/
theorem upperBound_squeeze : UpperBound := by
  intro B hB ε hε
  filter_upwards [eventually_ge_atTop LowerSharp.T0, eventually_upper hε] with T hT h
  apply exists_learner_of_minimaxRegret_lt
  refine (closedBounds B hB T hT).2.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
  have hB2 : 0 < B ^ 2 := by positivity
  nlinarith

/-- The lower half of the limit (`RegretKappa.LowerBound`), from the closed lower bound. -/
theorem lowerBound_squeeze : LowerBound := by
  intro B hB ε hε
  filter_upwards [eventually_ge_atTop LowerSharp.T0, eventually_lower hε] with T hT h
  apply exists_play_of_lt_minimaxRegret
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 ?_) (closedBounds B hB T hT).1
  have hB2 : 0 < B ^ 2 := by positivity
  nlinarith

/-- **kappa = 3** (`RegretKappa.KappaEqThree`), from the closed bounds. -/
theorem kappaEqThree_squeeze : KappaEqThree :=
  kappaEqThree_of_bounds upperBound_squeeze lowerBound_squeeze

/-- **The main theorem with the explicit lower and upper bounds** (`RegretKappa.MainTheoremChain`). -/
theorem mainChain : MainTheoremChain := ⟨chainBounds, kappaEqThree_squeeze⟩

/-- **The main theorem** (`RegretKappa.MainTheorem`). -/
theorem main : MainTheorem := ⟨closedBounds, kappaEqThree_squeeze⟩

/-- **Bounded features, with the bounds of the main theorem**
(`RegretKappa.MainBoundedFeatures`). -/
theorem mainBoundedFeatures : MainBoundedFeatures.{u} := by
  intro B hB T hT
  obtain ⟨⟨ι, hι, w, x, y, hw, hs, hx, hy, hadv⟩, hLb, hbBF, hBFI, hU⟩ :=
    mainBoundedFeaturesChain.{u} B hB T hT
  exact ⟨⟨ι, hι, w, x, y, hw, hs, hx, hy, fun Ω _ μ L hL => hLb.trans (hadv Ω μ L hL)⟩,
    hLb.trans hbBF, hBFI,
    hU.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left (boundU_le hT) (sq_nonneg B)))⟩

/-- **The randomized lower bound** (`Corollaries.RandLowerBound`), from bounded features: against a
randomized learner, some play of the adversary of `mainBoundedFeatures` does at least as well as
the adversary, and its outcomes lie in `{-B, 0, B}`. -/
theorem randLowerBound : Corollaries.RandLowerBound.{u} := by
  intro B hB ε hε
  filter_upwards [eventually_ge_atTop LowerSharp.T0, eventually_lower hε] with T hT h
  intro Ω _ μ L hL
  obtain ⟨⟨ι, _, w, x, y, hw, hs, -, hy, hadv⟩, -⟩ := mainBoundedFeatures.{u} B hB T hT
  have hc := hadv Ω μ L hL
  rw [Corollaries.advRegret_eq_sum μ hL.2] at hc
  obtain ⟨i, hi⟩ := Corollaries.exists_le_of_le_sum w hw hs _ _ _ hc
  refine ⟨x i, y i, fun t => Corollaries.abs_le_of_mem hB (hy i t), le_trans ?_ hi⟩
  have hB2 : 0 < B ^ 2 := by positivity
  exact EReal.coe_le_coe_iff.2 (by nlinarith)

end RegretKappa
