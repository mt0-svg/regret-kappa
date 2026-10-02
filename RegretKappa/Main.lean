import RegretKappa.MainStatement
import RegretKappa.LowerSharp.Assembly
import RegretKappa.Kappa
import RegretKappa.Corollaries.UpperU
import RegretKappa.Corollaries.Explicit

/-!
# The main theorem

`RegretKappa.main : RegretKappa.MainTheorem` and its companion for the paper's Corollary 5.1,
`RegretKappa.mainBoundedFeatures : RegretKappa.MainBoundedFeatures`, from

* the paper, Theorem 4.1: `LowerSharp.lowerSharpBound` (one play, every `B > 0`),
  `LowerSharp.lowerSharpAdv` (the finite adversary, `B = 1`) and `LowerSharp.lowerSharpSimplified`
  (the simplified forms of `b(T)`);
* the paper, Theorem 3.1: `Corollaries.regret_rescale_learnerU_le` (the learner of `UpperSharp`
  rescaled to outcomes in `[-B, B]`) and `Corollaries.boundedFeaturesUpperUI`;
* kappa = 3: `RegretKappa.kappaEqThree`;
* the transfer to bounded features: `Corollaries.boundedFeatures_of_mixture`.
-/

namespace RegretKappa

universe u

/-- `B² (3 log T - 2 log log T - 15.2) ≤ B² b(T)` for `T ≥ 355713`. -/
theorem boundL_le_bT {B : ℝ} {T : ℕ} (hT : LowerSharp.T0 ≤ T) :
    ((B ^ 2 * boundL T : ℝ) : EReal) ≤ ((B ^ 2 * LowerSharp.bT T : ℝ) : EReal) := by
  obtain ⟨h1, h2⟩ := LowerSharp.lowerSharpSimplified T hT
  exact EReal.coe_le_coe_iff.2
    (mul_le_mul_of_nonneg_left (by unfold boundL; linarith) (sq_nonneg B))

/-- **The main theorem** (`RegretKappa.MainTheorem`). -/
theorem main : MainTheorem := by
  refine ⟨fun B hB T hT => ⟨boundL_le_bT hT, ?_, ?_⟩, kappaEqThree⟩
  · exact le_minimaxRegret fun L => LowerSharp.lowerSharpBound B hB T hT L
  · exact minimaxRegret_le_of_learner (Lower.rescale (UpperSharp.learnerU T) B⁻¹)
      fun x y hy => Corollaries.regret_rescale_learnerU_le hB T x y hy

/-- **The paper, Corollary 5.1, with the constants of the main theorem**
(`RegretKappa.MainBoundedFeatures`). -/
theorem mainBoundedFeatures : MainBoundedFeatures.{u} := by
  intro B hB T hT
  obtain ⟨ι, hι, w, x, y, hw, hs, hx, hy, hb⟩ := LowerSharp.lowerSharpAdv T hT
  obtain ⟨⟨x', y', hx', hy', hadv⟩, -, -, hBF, -⟩ :=
    Corollaries.boundedFeatures_of_mixture.{u} w hw hs x y hx hy hb hB
  exact ⟨⟨ι, hι, w, x', y', hw, hs, hx', hy', hadv⟩, boundL_le_bT hT, hBF,
    Corollaries.minimaxRegretBF_le_BFI T hB, Corollaries.boundedFeaturesUpperUI B hB T⟩

end RegretKappa
