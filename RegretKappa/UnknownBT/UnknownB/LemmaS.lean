import RegretKappa.UnknownBT.UnknownB.Kappa
import RegretKappa.UpperSharp.Step

/-!
# Unknown `B`: the surprise round

In the units of `RegretKappa.Upper` (`G = Γ/2`, level `l = λ/2`, normalizer `A/2` in place of
`A`). A round in which the new outcome `y` has `|y| = m ≥ 1` (in the units of the old running
maximum) costs at most `KB (m² - 1)` over the one-round inequality:

`η² - 2 η y + m² Ψ((a + b y)/m) ≤ Q(ρ) + KB (m² - 1)`,

with `a = ρ √(1 - b²)`, `η = Upper.eta l a b`, `Ψ(w) = 2 log((l + G w)/A)`,
`Q(w) = 2 log((l + 3/2 + G w)/A)`, `A ≥ l + 3/2 + G 0` (`lemmaS_abstract`), and the same on the state
`(S, V)` and the feature `x` (`lemmaS_state`). The constant is `KB = 1 + kappaB + lipB`: the case
`y = m` (outcome along the state) costs `2 + kappaB`, through the monotonicity of the prediction in
the state (`eta_mono`) and the scale lemma for `Q`; the case `y = -m` costs `1 + kappaB + lipB`,
through the scale lemma for `Ψ` and the Lipschitz bound of `Ψ` on `[-1, 1]`.
-/

namespace RegretKappa.UnknownBT.UB

open Real RegretKappa RegretKappa.UpperSharp

/-- The constant of the surprise round. -/
noncomputable def KB : ℝ := 1 + kappaB + lipB

theorem Dg_one_ge : (exp (-1 / 2) + 2 * K0) / 2 ≤ Dg 1 := by
  have h := le_hasSum (Dg_hasSum one_pos) 0 (fun n _ => Dg_coeff_nonneg zero_le_one n)
  have h1 : Mw 1 = exp (-1 / 2) + 2 * K0 := by rw [Mw_one, mom_one]
  simp only [Nat.cast_zero, zero_add, pow_zero, Nat.factorial, Nat.succ_eq_add_one] at h
  rw [h1] at h
  norm_num at h
  linarith

theorem lipB_ge_one : 1 ≤ lipB := by
  have h := Dg_one_ge
  have hK := K0_nonneg
  have he := exp_pos (-1 / 2 : ℝ)
  unfold lipB
  rw [le_div_iff₀ he]
  linarith

theorem lipB_nonneg : 0 ≤ lipB := le_trans zero_le_one lipB_ge_one

theorem le_KB : 2 + kappaB ≤ KB := by
  unfold KB
  linarith [lipB_ge_one]

theorem lipB_le_KB : lipB ≤ KB := by
  unfold KB
  linarith [kappaB_nonneg]

/-- The potential is nondecreasing in `|w|`. -/
theorem psi_mono {l A x z : ℝ} (hl : 0 ≤ l) (hA : 0 < A) (h : |x| ≤ |z|) :
    2 * log ((l + Upper.G x) / A) ≤ 2 * log ((l + Upper.G z) / A) := by
  have hx := G_pos x
  have hG := Upper.G_mono h
  have : log ((l + Upper.G x) / A) ≤ log ((l + Upper.G z) / A) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hA.le)
  linarith

/-- The one-round inequality in the variables `ρ`, `b`, minus `2 log A`. -/
theorem step_A {l A ρ b y : ℝ} (hl : 0 < l) (hA : 0 < A) (hb : b ^ 2 ≤ 1) (hy : |y| ≤ 1) :
    Upper.eta l (ρ * √(1 - b ^ 2)) b ^ 2 - 2 * Upper.eta l (ρ * √(1 - b ^ 2)) b * y +
        2 * log ((l + Upper.G (ρ * √(1 - b ^ 2) + b * y)) / A) ≤
      2 * log ((l + 3 / 2 + Upper.G ρ) / A) := by
  have h := step_abstract_sharp (ρ := ρ) hl hb hy
  have h1 := G_pos (ρ * √(1 - b ^ 2) + b * y)
  have h2 := G_pos ρ
  rw [Real.log_div (by positivity) hA.ne', Real.log_div (by positivity) hA.ne']
  linarith

/-- The surprise round for `ρ ≥ 0` and `b ≥ 0`. -/
theorem lemmaS_core {l A ρ b y m : ℝ} (hl : 0 < l) (hA : l + 3 / 2 + Upper.G 0 ≤ A) (hρ : 0 ≤ ρ)
    (hb0 : 0 ≤ b) (hb : b ^ 2 ≤ 1) (hm : 1 ≤ m) (hy : y = m ∨ y = -m) :
    Upper.eta l (ρ * √(1 - b ^ 2)) b ^ 2 - 2 * Upper.eta l (ρ * √(1 - b ^ 2)) b * y +
        m ^ 2 * (2 * log ((l + Upper.G ((ρ * √(1 - b ^ 2) + b * y) / m)) / A)) ≤
      2 * log ((l + 3 / 2 + Upper.G ρ) / A) + KB * (m ^ 2 - 1) := by
  have hG0 := G_pos 0
  have hApos : 0 < A := by linarith
  have hm0 : 0 < m := by linarith
  have hm2 : 0 ≤ m ^ 2 - 1 := by nlinarith
  have hκ := kappaB_nonneg
  have hlip := lipB_ge_one
  set c := √(1 - b ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set a := ρ * c with ha
  have ha0 : 0 ≤ a := mul_nonneg hρ hc0
  set η := Upper.eta l a b with hη
  have hη1 : η ≤ 1 := eta_le_one l a b
  rcases hy with hy | hy <;> rw [hy]
  · -- the outcome along the state: the one-round inequality at `ρ/m` with the outcome `1`
    have hs := step_A (ρ := ρ / m) (y := 1) hl hApos hb (by norm_num)
    have e1 : ρ / m * c = a / m := by rw [ha]; ring
    have e2 : (a + b * m) / m = a / m + b * 1 := by field_simp
    rw [e1] at hs
    rw [e2]
    set e := Upper.eta l (a / m) b with he
    have he0 : 0 ≤ e := eta_nonneg hl (div_nonneg ha0 hm0.le) hb0
    have he1 : e ≤ η := eta_mono hl (div_le_self ha0 hm) hb0
    have hcost := cost_bound η e m he0 he1 hη1 hm
    have hsc := scale_lemma (l := l + 3 / 2) (A := A) (by linarith) hA ρ hm
    have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg m)
    have hK := le_KB
    nlinarith
  · -- the outcome against the state: the one-round inequality at `ρ` with the outcome `-1`
    have hs := step_A (ρ := ρ) (y := -1) hl hApos hb (by norm_num)
    rw [← hc, ← ha, ← hη] at hs
    have hA' : l + Upper.G 0 ≤ A := by linarith
    have e2 : (a + b * -m) / m = a / m - b := by field_simp; ring
    rw [e2]
    have e3 : a + b * -1 = a - b := by ring
    rw [e3] at hs
    -- the scale lemma for `Ψ` at `a - b`
    have hsc := scale_lemma (l := l) (A := A) hl.le hA' (a - b) hm
    have e4 : (a - b) / m = a / m - b / m := by ring
    rw [e4] at hsc
    -- the shift from `a/m - b/m` to `a/m - b`
    have hshift : m ^ 2 * (2 * log ((l + Upper.G (a / m - b)) / A)) -
        m ^ 2 * (2 * log ((l + Upper.G (a / m - b / m)) / A)) ≤ lipB * (m ^ 2 - 1) := by
      obtain ⟨hcase1, hcase2⟩ := abs_cases (a / m) b m (div_nonneg ha0 hm0.le) hb0
        (by nlinarith) hm
      rw [← mul_sub]
      rcases le_or_gt b (a / m) with hpb | hpb
      · have := psi_mono (l := l) (A := A) hl.le hApos (hcase1 hpb)
        nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg m), lipB_nonneg]
      · obtain ⟨hx1, hz1, hd⟩ := hcase2 hpb
        rcases le_or_gt |a / m - b / m| |a / m - b| with hzx | hzx
        · have hL := psi_lip (l := l) (A := A) hl.le hApos hx1 hzx
          have hd' : lipB * (|a / m - b| - |a / m - b / m|) ≤ lipB * ((m - 1) / m) :=
            mul_le_mul_of_nonneg_left hd lipB_nonneg
          have hmm : m ^ 2 * (lipB * ((m - 1) / m)) ≤ lipB * (m ^ 2 - 1) := by
            have : m ^ 2 * (lipB * ((m - 1) / m)) = lipB * (m * (m - 1)) := by
              field_simp
            rw [this]
            exact mul_le_mul_of_nonneg_left (by nlinarith) lipB_nonneg
          have := mul_le_mul_of_nonneg_left (hL.trans hd') (sq_nonneg m)
          linarith
        · have := psi_mono (l := l) (A := A) hl.le hApos hzx.le
          nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg m), lipB_nonneg]
    have hη2 : 2 * η * (m - 1) ≤ m ^ 2 - 1 := by nlinarith
    unfold KB
    linarith

/-- **The surprise round** in the variables `ρ`, `b`: the signs of `ρ` and `b` are removed by the symmetries
`(b, y) ↦ (-b, -y)` and `(ρ, y) ↦ (-ρ, -y)`. -/
theorem lemmaS_abstract {l A ρ b y m : ℝ} (hl : 0 < l) (hA : l + 3 / 2 + Upper.G 0 ≤ A)
    (hb : b ^ 2 ≤ 1) (hm : 1 ≤ m) (hy : |y| = m) :
    Upper.eta l (ρ * √(1 - b ^ 2)) b ^ 2 - 2 * Upper.eta l (ρ * √(1 - b ^ 2)) b * y +
        m ^ 2 * (2 * log ((l + Upper.G ((ρ * √(1 - b ^ 2) + b * y) / m)) / A)) ≤
      2 * log ((l + 3 / 2 + Upper.G ρ) / A) + KB * (m ^ 2 - 1) := by
  have hy' : ∀ y : ℝ, |y| = m → y = m ∨ y = -m := fun y h =>
    (abs_eq (by linarith)).1 h
  -- the case `b ≥ 0`, any sign of `ρ`
  have hpos : ∀ ρ b y : ℝ, 0 ≤ b → b ^ 2 ≤ 1 → |y| = m →
      Upper.eta l (ρ * √(1 - b ^ 2)) b ^ 2 - 2 * Upper.eta l (ρ * √(1 - b ^ 2)) b * y +
          m ^ 2 * (2 * log ((l + Upper.G ((ρ * √(1 - b ^ 2) + b * y) / m)) / A)) ≤
        2 * log ((l + 3 / 2 + Upper.G ρ) / A) + KB * (m ^ 2 - 1) := by
    intro ρ b y hb0 hb hy
    rcases le_or_gt 0 ρ with hρ | hρ
    · exact lemmaS_core hl hA hρ hb0 hb hm (hy' y hy)
    · have h := lemmaS_core (ρ := -ρ) (y := -y) hl hA (by linarith) hb0 hb hm
        (by rcases hy' y hy with h | h <;> [right; left] <;> linarith)
      have e1 : -ρ * √(1 - b ^ 2) = -(ρ * √(1 - b ^ 2)) := by ring
      have e2 : (-(ρ * √(1 - b ^ 2)) + b * -y) / m = -((ρ * √(1 - b ^ 2) + b * y) / m) := by ring
      rw [e1, eta_neg_left, e2, Upper.G_neg, Upper.G_neg] at h
      linarith
  rcases le_or_gt 0 b with hb0 | hb0
  · exact hpos ρ b y hb0 hb hy
  · have h := hpos ρ (-b) (-y) (by linarith) (by rwa [neg_sq]) (by rwa [abs_neg])
    rw [neg_sq, eta_neg] at h
    have e : ρ * √(1 - b ^ 2) + -b * -y = ρ * √(1 - b ^ 2) + b * y := by ring
    rw [e] at h
    linarith

/-- **The surprise round** on the state: `S = ∑ x_i y_i` and `V = ∑ x_i²` over the past rounds (in the units of
the old running maximum), the current feature `x` and the outcome `y` with `|y| = m ≥ 1`. -/
theorem lemmaS_state {l A S V x y m : ℝ} (hl : 0 < l) (hA : l + 3 / 2 + Upper.G 0 ≤ A)
    (hV : 0 ≤ V) (hSV : V = 0 → S = 0) (hm : 1 ≤ m) (hy : |y| = m) :
    Upper.pred l S V x ^ 2 - 2 * Upper.pred l S V x * y +
        m ^ 2 * (2 * log ((l + Upper.G ((S + x * y) / √(V + x ^ 2) / m)) / A)) ≤
      2 * log ((l + 3 / 2 + Upper.G (S / √V)) / A) + KB * (m ^ 2 - 1) := by
  unfold Upper.pred
  have hD0 : 0 ≤ V + x ^ 2 := by positivity
  have hb2 : (x / √(V + x ^ 2)) ^ 2 = x ^ 2 / (V + x ^ 2) := by rw [div_pow, Real.sq_sqrt hD0]
  have hb1 : (x / √(V + x ^ 2)) ^ 2 ≤ 1 := by
    rw [hb2]
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h, div_zero]
      norm_num
    · rw [div_le_one h]
      linarith
  have ha : S / √(V + x ^ 2) = S / √V * √(1 - (x / √(V + x ^ 2)) ^ 2) := by
    rcases eq_or_lt_of_le hV with h | h
    · rw [hSV h.symm]
      simp
    · have hDpos : 0 < V + x ^ 2 := by positivity
      have h1 : 1 - (x / √(V + x ^ 2)) ^ 2 = V / (V + x ^ 2) := by
        rw [hb2]
        field_simp
        ring
      have h2 : 0 < √V := Real.sqrt_pos.2 h
      have h3 : 0 < √(V + x ^ 2) := Real.sqrt_pos.2 hDpos
      rw [h1, Real.sqrt_div h.le]
      field_simp
  have hρ' : (S + x * y) / √(V + x ^ 2) =
      S / √V * √(1 - (x / √(V + x ^ 2)) ^ 2) + x / √(V + x ^ 2) * y := by
    rw [add_div, ← ha]
    ring
  rw [hρ', ha]
  exact lemmaS_abstract hl hA hb1 hm hy

end RegretKappa.UnknownBT.UB
