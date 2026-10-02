import RegretKappa.CorollariesCheck.Junk
import RegretKappa.CorollariesCheck.Indep42b

/-!
# The randomized lower bound with the Bochner integral and no measurability: false

`Indep42b` models a randomized learner as a probability space with a family of learners, with no
measurability condition, and its expected regret as the Bochner integral of the regret, which is
the junk value `0` for a regret that is not integrable. The family `famBot T` on `BoolBot` has a
regret that is not constant in `ω` on every play with at least one round and outcomes in
`[-1, 1]`, so it is not integrable and its expected regret is `0` there (`integral_famBot`). Hence
`Indep42b.RandLowerBound` is false (`not_randLowerBound`).
-/

namespace RegretKappa.CorollariesCheck.V42b

open MeasureTheory Filter

theorem not_randLowerBound : ¬Indep42b.RandLowerBound := by
  intro h
  obtain ⟨T, hT, hT2⟩ := ((h 1 one_pos 1 one_pos).and (eventually_ge_atTop 2)).exists
  obtain ⟨x, y, hy, hc⟩ := hT { Ω := BoolBot, μ := muBot, learner := famBot T }
  have h0 : ({ Ω := BoolBot, μ := muBot, learner := famBot T } : Indep42b.RandLearner T).expectedRegret
      x y = 0 := integral_famBot (by omega) x y hy
  rw [h0] at hc
  exact absurd hc (not_le.2 (bound_pos hT2))

end RegretKappa.CorollariesCheck.V42b
