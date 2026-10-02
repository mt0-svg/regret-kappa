import RegretKappa.Upper.Assembly
import RegretKappa.Lower.Assembly

/-!
# The limit of Theorem 1.1 of the paper

`RegretKappa.KappaEqThree` of `RegretKappa/Statement.lean`, the limit of Theorem 1.1, from
`kappaEqThree_of_bounds` and the two halves: `RegretKappa.Upper.upperBound` (the learner of
Section 3 of the paper, with cruder constants) and `RegretKappa.Lower.lowerBound` (a simpler
adversary than that of Section 4; Section 7.2 lists the differences). `RegretKappa.main` takes the
limit from here.
-/

namespace RegretKappa

/-- kappa = 3: for every `B > 0`, `minimaxRegret T B / (B ^ 2 log T)` tends to `3`. -/
theorem kappaEqThree : KappaEqThree :=
  kappaEqThree_of_bounds Upper.upperBound Lower.lowerBound

end RegretKappa
