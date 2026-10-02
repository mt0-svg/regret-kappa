import RegretKappa.UpperSharp.Statement
import RegretKappa.UpperSharpCheck.IndepU

/-!
# The statement of Theorem 3.1 against a formalization written separately

`RegretKappa.UpperSharpCheck.IndepU` (namespace `IndepU`) is a separately written formalization of
the paper's Theorem 3.1, which it calls Theorem U, from the text of the theorem alone (on the model
of `RegretKappa/Statement.lean`), kept verbatim up to its import line. It differs from
`RegretKappa/UpperSharp/Statement.lean` in its writing only:
* the integrand of `Γ` is associated as `(cosh · e^{-θ²/2}) · (1/θ + 2/θ³)`;
* the conventions `ρ = 0` if `V_{t-1} = 0` and `s = 0` if `V_t = 0` are left to Lean's `x / 0 = 0`
  (with `√0 = 0`), where ours writes them with `if`;
* the sign is `1` if `x_t = 0` and `Real.sign x_t` otherwise, ours `-1` if `x_t < 0` and `1`
  otherwise;
* the half is `(1/2) · log`, ours `log / 2`;
* the last term of the second bound is `12.35 / T^{3/2}` with the real power, ours
  `12.35 / (T √T)`.

`Gamma_eq`, `learner_eq` prove that the potential and the learner are the same, and `theoremU_iff`,
`theoremULog_iff` that the two propositions are equivalent to `TheoremU` and `TheoremULog`.
-/

namespace RegretKappa.UpperSharpCheck

open Real MeasureTheory Set

theorem Gamma_eq : IndepU.Gamma = UpperSharp.Gam := by
  funext r
  unfold IndepU.Gamma UpperSharp.Gam
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only
  ring

theorem eps_eq (x : ℝ) : (if x = 0 then 1 else Real.sign x) = (if x < 0 then (-1 : ℝ) else 1) := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [h.ne, h, Real.sign_of_neg h]
  · simp [h]
  · simp [h.ne', not_lt.2 h.le, Real.sign_of_pos h]

theorem rho_eq (S V : ℝ) : S / √V = if V = 0 then 0 else S / √V := by
  split_ifs with h
  · rw [h, Real.sqrt_zero, div_zero]
  · rfl

theorem s_eq (V x : ℝ) : x ^ 2 / (V + x ^ 2) = if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2) := by
  split_ifs with h
  · rw [h, div_zero]
  · rfl

theorem learner_eq (T : ℕ) : IndepU.learner T = UpperSharp.learnerU T := by
  unfold IndepU.learner UpperSharp.learnerU UpperSharp.predU
  congr 1
  funext t x y
  simp only
  rw [Gamma_eq, eps_eq, ← rho_eq, ← s_eq, one_div_mul_eq_div]
  rfl

theorem rpow_three_halves {T : ℝ} (hT : 0 < T) : T ^ (3 / 2 : ℝ) = T * √T := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hT, Real.rpow_one, Real.sqrt_eq_rpow]

theorem theoremU_iff : IndepU.TheoremU ↔ UpperSharp.TheoremU := by
  unfold IndepU.TheoremU UpperSharp.TheoremU
  simp only [learner_eq]

theorem theoremULog_iff : IndepU.TheoremULog ↔ UpperSharp.TheoremULog := by
  unfold IndepU.TheoremULog UpperSharp.TheoremULog
  refine forall_congr' fun T => imp_congr_right fun hT => ?_
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [learner_eq, rpow_three_halves hT']

end RegretKappa.UpperSharpCheck
