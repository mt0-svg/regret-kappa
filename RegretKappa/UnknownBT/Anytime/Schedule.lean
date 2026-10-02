import RegretKappa.UpperSharp.Statement

/-!
# Potential schedules

The interface between the anytime potential and the running-maximum learner, in 0-indexed rounds
(round `t` here is round `t + 1` of the paper). A schedule is a level `lam t > 0`
and a normalizer `A t > 0` per round with

* (H1) `(lam (t + 1) + 3 + Γ(w)) / A (t + 1) ≤ (lam t + Γ(w)) / A t` for every `t` and `w`;
* (H2) `lam t + 3 + Γ(0) ≤ A t` for every `t`.

The potential after round `t` is `Ψ_t(w) = 2 log((lam t + Γ(w)) / A t)` (`psiOf`). The anytime
instance (`lamB`, `A t = H₀ / b_t`) and the bound on `L_T = sup_{w² ≤ T} (w² - Ψ_{T-1}(w))` are in
`RegretKappa/UnknownBT/Anytime/ScheduleB.lean`.
-/

namespace RegretKappa.UnknownBT

open RegretKappa.UpperSharp Real

/-- A potential schedule: levels `lam`, normalizers `A`, with (H1) and (H2). -/
structure IsSchedule (lam A : ℕ → ℝ) : Prop where
  lam_pos : ∀ t, 0 < lam t
  A_pos : ∀ t, 0 < A t
  /-- (H1): the potential after round `t + 1`, with the increment `3`, is at most the potential
  after round `t`. -/
  h1 : ∀ (t : ℕ) (w : ℝ), (lam (t + 1) + 3 + Gam w) / A (t + 1) ≤ (lam t + Gam w) / A t
  /-- (H2): the normalizer dominates the potential at `0` with the increment. -/
  h2 : ∀ t : ℕ, lam t + 3 + Gam 0 ≤ A t

/-- The potential after round `t`: `Ψ_t(w) = 2 log((lam t + Γ(w)) / A t)`. -/
noncomputable def psiOf (lam A : ℕ → ℝ) (t : ℕ) (w : ℝ) : ℝ := 2 * log ((lam t + Gam w) / A t)

end RegretKappa.UnknownBT
