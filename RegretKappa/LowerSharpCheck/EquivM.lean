import RegretKappa.MainStatement
import RegretKappa.LowerSharpCheck.IndepM

/-!
# The main theorem in its closed form against a formalization written separately

`RegretKappa.MainTheorem` and `RegretKappa.MainBoundedFeatures` (`RegretKappa/MainStatement.lean`)
against `RegretKappa/LowerSharpCheck/IndepM.lean`, a separately written formalization of the text
of the main theorem and of Corollary 5.1, with the bounds `B² (3 log T - 2 log log T - 15.2)` and
`B² (3 log T + 0.37)`. The main theorem reads the same in both, up to unfolding `boundL` and `T0`
(`mainM_iff`). For Corollary 5.1 the separate reading quantifies over `B` and `T` once for the
adversary and once for the minimax regrets, ours once for both; the two are equivalent, in every
universe of the learners' probability spaces (`boundedM_iff`).
-/

namespace RegretKappa.LowerSharpCheck

universe u

theorem mainM_iff : MainTheorem ↔ IndepM.Main := Iff.rfl

theorem boundedM_iff : MainBoundedFeatures.{u} ↔ IndepM.Bounded.{u} := by
  constructor
  · intro h
    exact ⟨fun B hB T hT => (h B hB T hT).1, fun B hB T hT => (h B hB T hT).2⟩
  · intro h B hB T hT
    exact ⟨h.1 B hB T hT, h.2 B hB T hT⟩

end RegretKappa.LowerSharpCheck
