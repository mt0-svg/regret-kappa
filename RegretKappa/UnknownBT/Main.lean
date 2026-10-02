import RegretKappa.UnknownBT.Bridge
import RegretKappa.UnknownBT.Anytime.TheoremB
import RegretKappa.Main

/-!
# The results on the statement

* `optimality`: the constant `3` cannot be lowered, from the lower bound of regret-kappa
  (`RegretKappa.lowerBound_squeeze`, every learner of horizon `T`).
* `unknownT`: the bound known and the horizon not, from `TheoremBNum`.
* `answer_of_scaleFreeBound`: the explicit scale-free bound with any constant gives every target
  of the statement: `UnknownBTEveryT`, `UnknownBT`, `UnknownT`,
  `UnknownB`, `BestConstantThree` and `bestConstant = 3`.
-/

namespace RegretKappa.UnknownBT

/-- **Optimality of the constant 3** for anytime learners. -/
theorem optimality : Optimality := optimality_of_lowerBound RegretKappa.lowerBound_squeeze

/-- **`B` known, `T` unknown.** -/
theorem unknownT : UnknownT := unknownT_of_theoremBNum theoremBNum

/-- **Every target from the scale-free bound.** -/
theorem answer_of_scaleFreeBound {c : ℝ} (h : ScaleFreeBound c) :
    UnknownBTEveryT ∧ UnknownBT ∧ UnknownT ∧ UnknownB ∧ BestConstantThree ∧ bestConstant = 3 := by
  have h1 := everyT_of_scaleFreeBound h
  have h2 := unknownBT_of_everyT h1
  have h3 := bestConstantThree_of_bounds h2 optimality
  exact ⟨h1, h2, unknownT_of_unknownBT h2, unknownB_of_unknownBT h2, h3, bestConstant_eq_three h3⟩

end RegretKappa.UnknownBT
