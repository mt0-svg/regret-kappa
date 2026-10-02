import RegretKappa.UnknownBT.Main
import RegretKappa.UnknownBT.UnknownB.Main

/-!
# Every target of the statement

`scaleFreeBound_twelve` (the running-maximum bound with the schedule of `TheoremB`) through
`answer_of_scaleFreeBound` gives every target of `RegretKappa.UnknownBT.Statement`: the scale-free
anytime bound, `B` and `T` unknown, `T` unknown, `B` unknown, the best constant `3`.
-/

namespace RegretKappa.UnknownBT.UB

/-- **Every target**, with the constant `12` in the scale-free bound. -/
theorem answer :
    UnknownBTEveryT ∧ UnknownBT ∧ UnknownT ∧ UnknownB ∧ BestConstantThree ∧ bestConstant = 3 :=
  answer_of_scaleFreeBound scaleFreeBound_twelve

end RegretKappa.UnknownBT.UB
