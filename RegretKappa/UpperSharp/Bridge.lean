import RegretKappa.UpperSharp.Statement
import RegretKappa.Upper.Gamma

/-!
# Theorem 3.1 with the paper's constants: the learner in the units of `Upper`

`Γ = 2G` (`Gam_eq`), and the prediction `predU` of the statement is the prediction
`Upper.pred (λ/2)` of the library `Upper` at the level `λ/2` (`predU_eq`): the factor `2` cancels
in the ratio, the conventions of the statement for `V = 0` and `V + x² = 0` agree with the
formula of `Upper.pred`, and the sign `ε` of `x` passes into the second argument of `Upper.eta`
because `Upper.eta` is odd in it (`eta_neg`).
-/

namespace RegretKappa.UpperSharp

open Real MeasureTheory Set

/-- `Γ = 2G`. -/
theorem Gam_eq (r : ℝ) : Gam r = 2 * Upper.G r := rfl

/-- The level of round `t` (0-indexed) of a game of horizon `T`: `λ₀ + β (T - t - 1)`. -/
noncomputable def lamU (T t : ℕ) : ℝ := lam0 T + beta * ((T : ℝ) - t - 1)

theorem lam0_pos (T : ℕ) : 0 < lam0 T := by
  unfold lam0 Cst
  positivity

theorem clip_neg (z : ℝ) : Upper.clip (-z) = -Upper.clip z := by
  unfold Upper.clip
  by_cases hz : z ≤ -1
  · -- z ≤ -1 → -z ≥ 1
    have hz' : 1 ≤ -z := by linarith
    have hz1 : z ≤ 1 := by linarith
    -- LHS: max (-1) (min 1 (-z))
    rw [min_eq_left hz', max_eq_right (by linarith : (-1 : ℝ) ≤ 1)]
    -- RHS: -(max (-1) (min 1 z))
    rw [min_eq_right hz1, max_eq_left hz]
    ring
  · -- -1 < z
    rw [not_le] at hz
    by_cases hz1 : z ≤ 1
    · -- -1 < z ≤ 1
      have hz' : -z ≤ 1 := by linarith
      -- LHS: max (-1) (min 1 (-z))
      rw [min_eq_right hz', max_eq_right (by linarith : (-1 : ℝ) ≤ -z)]
      -- RHS: -(max (-1) (min 1 z))
      rw [min_eq_right hz1, max_eq_right (by linarith : (-1 : ℝ) ≤ z)]
    · -- 1 < z → -z < -1
      rw [not_le] at hz1
      have hz' : -z ≤ -1 := by linarith
      -- LHS: max (-1) (min 1 (-z))
      rw [min_eq_right (by linarith : -z ≤ (1 : ℝ)), max_eq_left hz']
      -- RHS: -(max (-1) (min 1 z))
      rw [min_eq_left (by linarith : (1 : ℝ) ≤ z), max_eq_right (by linarith : (-1 : ℝ) ≤ (1 : ℝ))]

theorem eta_neg (lam a b : ℝ) : Upper.eta lam a (-b) = -Upper.eta lam a b := by
  unfold Upper.eta
  have h1 : a + (-b) = a - b := by ring
  have h2 : a - (-b) = a + b := by ring
  rw [h1, h2]
  have h3 : (lam + Upper.G (a - b)) / (lam + Upper.G (a + b)) = ((lam + Upper.G (a + b)) / (lam + Upper.G (a - b)))⁻¹ := by
    rw [← inv_div]
  rw [h3]
  rw [Real.log_inv]
  rw [neg_div]
  rw [clip_neg]

theorem a_eq {S V x : ℝ} (hV : 0 ≤ V) (hSV : V = 0 → S = 0) :
    (if V = 0 then 0 else S / √V) * √(1 - (if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2))) =
      S / √(V + x ^ 2) := by
  by_cases hV0 : V = 0
  · -- Case V = 0
    have hS0 : S = 0 := hSV hV0
    subst hV0
    subst hS0
    simp
  · -- Case V ≠ 0
    have hVpos : V > 0 := by
      by_contra! hle
      apply hV0
      linarith
    have hVxpos : V + x ^ 2 > 0 := by
      nlinarith
    have hVx_ne_zero : V + x ^ 2 ≠ 0 := by linarith
    have hsqrtV_ne_zero : √V ≠ 0 :=
      (Real.sqrt_pos.mpr hVpos).ne.symm
    simp [hV0, hVx_ne_zero]
    have h_inner : 1 - x ^ 2 / (V + x ^ 2) = V / (V + x ^ 2) := by
      field_simp [hVx_ne_zero]
      ring
    rw [h_inner]
    rw [Real.sqrt_div hV]
    field_simp [hVx_ne_zero, hsqrtV_ne_zero]

theorem b_eq {V x : ℝ} (hV : 0 ≤ V) :
    (if x < 0 then (-1 : ℝ) else 1) * √(if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)) =
      x / √(V + x ^ 2) := by
  split_ifs with hx hsum
  · -- hx: x < 0, hsum: V + x^2 = 0
    have hx0 : x = 0 := by nlinarith
    linarith [hx, hx0]
  · -- hx: x < 0, hsum: V + x^2 ≠ 0
    rw [Real.sqrt_div (sq_nonneg x) (V + x ^ 2)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_neg hx]
    ring
  · -- hx: ¬ x < 0, hsum: V + x^2 = 0
    have hx0 : x = 0 := by nlinarith
    simp [hx0]
  · -- hx: ¬ x < 0, hsum: V + x^2 ≠ 0
    rw [Real.sqrt_div (sq_nonneg x) (V + x ^ 2)]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    simp

/-- The clipped half log ratio of the statement, with `Γ`, is `Upper.eta` at the level `λ/2`. -/
theorem eta_Gam (lam a b : ℝ) :
    clip (log ((lam + Gam (a + b)) / (lam + Gam (a - b))) / 2) = Upper.eta (lam / 2) a b := by
  have e : (lam + Gam (a + b)) / (lam + Gam (a - b)) =
      (lam / 2 + Upper.G (a + b)) / (lam / 2 + Upper.G (a - b)) := by
    rw [Gam_eq, Gam_eq, show lam + 2 * Upper.G (a + b) = 2 * (lam / 2 + Upper.G (a + b)) by ring,
      show lam + 2 * Upper.G (a - b) = 2 * (lam / 2 + Upper.G (a - b)) by ring,
      mul_div_mul_left _ _ two_ne_zero]
  rw [e]
  rfl

/-- **The bridge**: on a state with `V = 0 → S = 0`, the prediction of the statement is the
prediction of the library `Upper` at the level `λ/2`. -/
theorem predU_eq (T t : ℕ) {S V x : ℝ} (hV : 0 ≤ V) (hSV : V = 0 → S = 0) :
    predU T t S V x = Upper.pred (lamU T t / 2) S V x := by
  unfold predU Upper.pred lamU
  dsimp only
  rw [a_eq hV hSV, eta_Gam, ← b_eq (x := x) hV]
  generalize √(if V + x ^ 2 = 0 then 0 else x ^ 2 / (V + x ^ 2)) = w
  split_ifs with hx
  · rw [neg_one_mul, neg_one_mul, eta_neg]
  · rw [one_mul, one_mul]

end RegretKappa.UpperSharp
