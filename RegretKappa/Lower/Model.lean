import RegretKappa.Lower.Basic

/-!
# Lower bound: the phase-2 outcome model

Phase 2 draws signs `η : Fin n → Bool`, coordinate `l` equal to `true` with probability
`(1 + a_l(z)) / 2`, independently, where `a_l(z) = α_l + β_l z` is affine in the prior variable
`z` (the paper, Section 4.2: `a_l = θ* x_l = (ρ + z) ε_l` in normalized coordinates).

* `lik α β η z`, the probability of `η` given `z`, a polynomial in `z`;
* `score α β η z = ∂_z log lik`, so that `lik · score` is the derivative of `lik` (`hasDerivAt_lik`);
* `sum_lik_mul_coord`, the one rule behind every computation here: a factor that depends on
  coordinate `l` only is averaged against `(1 ± a_l)/2` and leaves the rest of the sum unchanged
  (independence of the coordinates, by the flip of coordinate `l`);
* the total mass `1`, the mean score `0`, the Fisher information `∑ β_l² / (1 - a_l²)` (Lemma 4.11
  (ii) of the paper: informations add over independent outcomes);
* `sum_lik_round`, step (i) of Lemma 4.11: given the past, the excess loss of round `i` over the
  comparator `a_i` averages to `(ŷ - a_i)²`;
* `sum_lik_cut`, marginalization: a function of the first `i` coordinates sees only the model of
  those coordinates (parameters after `i` set to `0`), so the van Trees bound of round `i` uses the
  information of the past outcomes only.
-/

namespace RegretKappa.Lower

open Finset

/-- The probability `(1 ± a) / 2` of a sign with mean `a`. -/
noncomputable def qB (a : ℝ) (b : Bool) : ℝ := (1 + sgn b * a) / 2

/-- The probability of the sign vector `η` given the prior variable `z`. -/
noncomputable def lik {n : ℕ} (α β : Fin n → ℝ) (η : Fin n → Bool) (z : ℝ) : ℝ :=
  ∏ l, qB (α l + β l * z) (η l)

/-- The score `∂_z log lik`. -/
noncomputable def score {n : ℕ} (α β : Fin n → ℝ) (η : Fin n → Bool) (z : ℝ) : ℝ :=
  ∑ l, sgn (η l) * β l / (1 + sgn (η l) * (α l + β l * z))

theorem qB_add (a : ℝ) : qB a true + qB a false = 1 := by
  simp only [qB, sgn_true, sgn_false]
  ring

theorem qB_nonneg {a : ℝ} (ha : |a| ≤ 1) (b : Bool) : 0 ≤ qB a b := by
  have := abs_le.1 ha
  cases b <;> simp only [qB, sgn_true, sgn_false] <;> linarith

theorem qB_pos {a : ℝ} (ha : |a| < 1) (b : Bool) : 0 < qB a b := by
  have := abs_lt.1 ha
  cases b <;> simp only [qB, sgn_true, sgn_false] <;> linarith

theorem lik_nonneg {n : ℕ} {α β : Fin n → ℝ} {z : ℝ} (h : ∀ l, |α l + β l * z| ≤ 1)
    (η : Fin n → Bool) : 0 ≤ lik α β η z :=
  Finset.prod_nonneg fun l _ => qB_nonneg (h l) (η l)

theorem lik_pos {n : ℕ} {α β : Fin n → ℝ} {z : ℝ} (h : ∀ l, |α l + β l * z| < 1)
    (η : Fin n → Bool) : 0 < lik α β η z :=
  Finset.prod_pos fun l _ => qB_pos (h l) (η l)

@[fun_prop]
theorem continuous_lik {n : ℕ} (α β : Fin n → ℝ) (η : Fin n → Bool) : Continuous (lik α β η) := by
  unfold lik qB
  fun_prop

-- TARGET

/-- Independence: a factor of coordinate `l` alone is averaged against `qB`, the rest of the sum
being invariant under the flip of coordinate `l`. -/
theorem sum_lik_mul_coord {n : ℕ} (α β : Fin n → ℝ) (z : ℝ) (l : Fin n) (F : Bool → ℝ)
    (G : (Fin n → Bool) → ℝ) (hG : ∀ η, G (flipAt l η) = G η) :
    ∑ η, lik α β η z * F (η l) * G η =
      (qB (α l + β l * z) true * F true + qB (α l + β l * z) false * F false) *
        ∑ η, lik α β η z * G η := by
  set q := λ b : Bool => qB (α l + β l * z) b with hq
  set R := λ η : Fin n → Bool => ∏ l' ∈ univ.erase l, qB (α l' + β l' * z) (η l') with hR
  have h_lik_eq : ∀ η, lik α β η z = q (η l) * R η := by
    intro η
    rw [lik, hR, hq]
    rw [← Finset.mul_prod_erase (univ : Finset (Fin n)) (λ l' => qB (α l' + β l' * z) (η l')) (Finset.mem_univ l)]
  have h_R_flip : ∀ η, R (flipAt l η) = R η := by
    intro η
    dsimp [R]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_erase] at hx
    rcases hx with ⟨hx_ne, hx_mem⟩
    rw [flipAt_ne hx_ne η]
  have h_flip_involutive : Function.Involutive (flipAt l) := by
    intro η
    exact flipAt_flipAt l η
  let e : Equiv.Perm (Fin n → Bool) := Function.Involutive.toPerm (flipAt l) h_flip_involutive
  have h_sum_flip (f : (Fin n → Bool) → ℝ) : ∑ η, f (flipAt l η) = ∑ η, f η := by
    simpa [e] using (Equiv.sum_comp e f)
  have h_key_symm (b : Bool) : q b * F b + q (!b) * F (!b) = q true * F true + q false * F false := by
    cases b <;> simp [q, add_comm]
  have h_key_one (b : Bool) : q b + q (!b) = 1 := by
    cases b <;> simpa [q, add_comm] using qB_add (α l + β l * z)
  have h_half_sum : (1/2 : ℝ) * ∑ η : Fin n → Bool, R η * G η = ∑ η : Fin n → Bool, q (η l) * R η * G η := by
    have h_eq : ∑ η : Fin n → Bool, q (η l) * R η * G η + ∑ η : Fin n → Bool, q (η l) * R η * G η =
        ∑ η : Fin n → Bool, R η * G η := by
      have h_flip_eq : ∑ η : Fin n → Bool, q (η l) * R η * G η = ∑ η : Fin n → Bool, q (!(η l)) * R η * G η := by
        calc
          ∑ η : Fin n → Bool, q (η l) * R η * G η =
              ∑ η : Fin n → Bool, q ((flipAt l η) l) * R (flipAt l η) * G (flipAt l η) := by
            simpa [e] using ((Equiv.sum_comp e (λ η => q (η l) * R η * G η)).symm)
          _ = ∑ η : Fin n → Bool, q (!(η l)) * R η * G η := by simp [h_R_flip, hG, flipAt_self]
      calc
        ∑ η : Fin n → Bool, q (η l) * R η * G η + ∑ η : Fin n → Bool, q (η l) * R η * G η =
            ∑ η : Fin n → Bool, q (η l) * R η * G η + ∑ η : Fin n → Bool, q (!(η l)) * R η * G η := by
          rw [h_flip_eq]
        _ = ∑ η : Fin n → Bool, (q (η l) * R η * G η + q (!(η l)) * R η * G η) := by rw [Finset.sum_add_distrib]
        _ = ∑ η : Fin n → Bool, R η * G η * (q (η l) + q (!(η l))) := by
          refine Finset.sum_congr rfl (λ η _ => ?_)
          ring
        _ = ∑ η : Fin n → Bool, R η * G η * 1 := by
          refine Finset.sum_congr rfl (λ η _ => ?_)
          rw [h_key_one (η l)]
        _ = ∑ η : Fin n → Bool, R η * G η := by simp
    linarith
  calc
    ∑ η : Fin n → Bool, lik α β η z * F (η l) * G η =
        ∑ η : Fin n → Bool, (q (η l) * R η) * F (η l) * G η := by simp [h_lik_eq]
    _ = ∑ η : Fin n → Bool, R η * G η * q (η l) * F (η l) := by
      refine Finset.sum_congr rfl (λ η _ => ?_)
      ring
    _ = (1/2 : ℝ) * (∑ η : Fin n → Bool, R η * G η * q (η l) * F (η l) +
        ∑ η : Fin n → Bool, R η * G η * q (η l) * F (η l)) := by
      ring
    _ = (1/2 : ℝ) * (∑ η : Fin n → Bool, R η * G η * q (η l) * F (η l) +
        ∑ η : Fin n → Bool, R η * G η * q (!(η l)) * F (!(η l))) := by
      have h_flip_eq : ∑ η : Fin n → Bool, R η * G η * q (η l) * F (η l) =
          ∑ η : Fin n → Bool, R η * G η * q (!(η l)) * F (!(η l)) := by
        calc
          ∑ η : Fin n → Bool, R η * G η * q (η l) * F (η l) =
              ∑ η : Fin n → Bool, R (flipAt l η) * G (flipAt l η) * q ((flipAt l η) l) * F ((flipAt l η) l) := by
            simpa [e] using ((Equiv.sum_comp e (λ η => R η * G η * q (η l) * F (η l))).symm)
          _ = ∑ η : Fin n → Bool, R η * G η * q (!(η l)) * F (!(η l)) := by
            simp [h_R_flip, hG, flipAt_self]
      rw [h_flip_eq]
    _ = (1/2 : ℝ) * ∑ η : Fin n → Bool, (R η * G η * q (η l) * F (η l) +
        R η * G η * q (!(η l)) * F (!(η l))) := by
      rw [Finset.sum_add_distrib]
    _ = (1/2 : ℝ) * ∑ η : Fin n → Bool, R η * G η * (q (η l) * F (η l) + q (!(η l)) * F (!(η l))) := by
      refine congrArg (λ t => (1/2 : ℝ) * t) (Finset.sum_congr rfl (λ η _ => ?_))
      ring
    _ = (1/2 : ℝ) * ∑ η : Fin n → Bool, R η * G η * (q true * F true + q false * F false) := by
      refine congrArg (λ t => (1/2 : ℝ) * t) (Finset.sum_congr rfl (λ η _ => ?_))
      rw [h_key_symm (η l)]
    _ = (1/2 : ℝ) * (q true * F true + q false * F false) * ∑ η : Fin n → Bool, R η * G η := by
      simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = (q true * F true + q false * F false) * ((1/2 : ℝ) * ∑ η : Fin n → Bool, R η * G η) := by ring
    _ = (q true * F true + q false * F false) * ∑ η : Fin n → Bool, q (η l) * R η * G η := by
      rw [h_half_sum]
    _ = (q true * F true + q false * F false) * ∑ η : Fin n → Bool, lik α β η z * G η := by
      simp [h_lik_eq]

/-- The total mass is `1`. -/
theorem sum_lik {n : ℕ} (α β : Fin n → ℝ) (z : ℝ) : ∑ η, lik α β η z = 1 := by
  unfold lik
  rw [← Fintype.prod_sum (fun l b => qB (α l + β l * z) b)]
  simp [qB_add]

-- TARGET

/-- The derivative of the likelihood is `lik · score`. -/
theorem hasDerivAt_lik {n : ℕ} (α β : Fin n → ℝ) (η : Fin n → Bool) {z : ℝ}
    (h : ∀ l, |α l + β l * z| < 1) :
    HasDerivAt (lik α β η) (lik α β η z * score α β η z) z := by
  have hq_deriv (l : Fin n) : HasDerivAt (fun z => qB (α l + β l * z) (η l)) (sgn (η l) * β l / 2) z := by
    -- qB (α l + β l * z) (η l) = (1 + sgn (η l) * (α l + β l * z)) / 2
    -- = (1 + sgn (η l) * α l) / 2 + (sgn (η l) * β l / 2) * z
    -- which is affine in z with slope sgn (η l) * β l / 2
    have h_expr : (fun z : ℝ => qB (α l + β l * z) (η l)) = fun z => ((1 + sgn (η l) * α l) / 2) + (sgn (η l) * β l / 2) * z := by
      ext z
      dsimp [qB, sgn]
      ring
    rw [h_expr]
    have h_const : HasDerivAt (fun _ : ℝ => ((1 + sgn (η l) * α l) / 2 : ℝ)) 0 z := hasDerivAt_const z _
    have h_mul : HasDerivAt (fun z : ℝ => (sgn (η l) * β l / 2) * z) (sgn (η l) * β l / 2) z := by
      simpa [mul_comm] using HasDerivAt.const_mul (sgn (η l) * β l / 2) (hasDerivAt_id z)
    have h_add := HasDerivAt.add h_const h_mul
    -- h_add : HasDerivAt ((fun x => c) + (fun z => m * z)) (0 + m) z
    -- The function part is definitionally equal, so we just need to fix the derivative
    have h_add' : HasDerivAt (fun z => ((1 + sgn (η l) * α l) / 2) + (sgn (η l) * β l / 2) * z) (sgn (η l) * β l / 2) z := by
      convert h_add using 1
      · simp
    exact h_add'
  have h_prod := HasDerivAt.finsetProd (u := Finset.univ) (fun l hl => hq_deriv l)
  have h_lik_eq : lik α β η = fun z => ∏ l : Fin n, qB (α l + β l * z) (η l) := by
    ext z; simp [lik]
  rw [h_lik_eq]
  -- h_prod gives the derivative as a sum. We need to show that sum equals lik * score.
  have h_deriv_eq : (∑ i : Fin n, (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) • (sgn (η i) * β i / 2)) =
      (∏ l : Fin n, qB (α l + β l * z) (η l)) * score α β η z := by
    -- First, convert • to * in ℝ
    have h_smul : (∑ i : Fin n, (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) • (sgn (η i) * β i / 2)) =
        (∑ i : Fin n, (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) * (sgn (η i) * β i / 2)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp [smul_eq_mul]
    rw [h_smul]
    -- Now we need to show: sum_i (prod_erase_i * (sgn β / 2)) = (prod_all) * (sum_i (sgn β / (1 + sgn a)))
    -- Key identity: for each i,
    --   (prod_erase_i) * (sgn(η i) * β i / 2) = (prod_all) * (sgn(η i) * β i / (1 + sgn(η i) * (α i + β i * z)))
    -- This follows from: qB(a) * (sgn β / (1 + sgn a)) = sgn β / 2  where a = α i + β i * z
    -- and prod_all = qB(a_i) * prod_erase_i
    have h_key (i : Fin n) : (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) * (sgn (η i) * β i / 2) =
        (∏ l : Fin n, qB (α l + β l * z) (η l)) * (sgn (η i) * β i / (1 + sgn (η i) * (α i + β i * z))) := by
      have h_erase : (∏ l : Fin n, qB (α l + β l * z) (η l)) =
          qB (α i + β i * z) (η i) * (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) := by
        rw [Finset.mul_prod_erase Finset.univ (fun l => qB (α l + β l * z) (η l)) (mem_univ i)]
      rw [h_erase]
      have hq_eq : qB (α i + β i * z) (η i) * (sgn (η i) * β i / (1 + sgn (η i) * (α i + β i * z))) = sgn (η i) * β i / 2 := by
        dsimp [qB]
        have h_denom_pos : 1 + sgn (η i) * (α i + β i * z) > 0 := by
          have h_abs : |α i + β i * z| < 1 := h i
          have h_sgn_abs : |sgn (η i)| = 1 := abs_sgn (η i)
          -- |sgn (η i) * (α i + β i * z)| = |sgn (η i)| * |α i + β i * z| = |α i + β i * z| < 1
          -- So sgn (η i) * (α i + β i * z) > -1, hence 1 + sgn (η i) * (α i + β i * z) > 0
          have h_mul_abs : |sgn (η i) * (α i + β i * z)| < 1 := by
            rw [abs_mul, abs_sgn (η i), one_mul]
            exact h_abs
          have h_mul_gt_neg_one : sgn (η i) * (α i + β i * z) > -1 := by
            linarith [abs_lt.mp h_mul_abs]
          linarith
        field_simp [ne_of_gt h_denom_pos]
      let A := ∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)
      let q := qB (α i + β i * z) (η i)
      let B := sgn (η i) * β i / 2
      let C := sgn (η i) * β i / (1 + sgn (η i) * (α i + β i * z))
      have hq_eq' : q * C = B := hq_eq
      calc
        A * B = A * (q * C) := by rw [hq_eq']
        _ = (A * q) * C := by ring
        _ = (q * A) * C := by ring
    calc
      (∑ i : Fin n, (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) * (sgn (η i) * β i / 2)) =
          (∑ i : Fin n, (∏ l : Fin n, qB (α l + β l * z) (η l)) * (sgn (η i) * β i / (1 + sgn (η i) * (α i + β i * z)))) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [h_key i]
      _ = (∏ l : Fin n, qB (α l + β l * z) (η l)) * (∑ i : Fin n, sgn (η i) * β i / (1 + sgn (η i) * (α i + β i * z))) := by
        rw [Finset.mul_sum]
      _ = (∏ l : Fin n, qB (α l + β l * z) (η l)) * score α β η z := rfl
  -- The function part: (∏ i, fun z => ...) = (fun z => ∏ l, ...)
  have h_fun_eq : (∏ i : Fin n, fun z => qB (α i + β i * z) (η i)) = (fun z => ∏ l : Fin n, qB (α l + β l * z) (η l)) := by
    ext z
    simp
  -- Rewrite h_prod using h_fun_eq and h_deriv_eq
  rw [h_fun_eq] at h_prod
  have h_deriv_eq' : (∑ i : Fin n, (∏ j ∈ univ.erase i, qB (α j + β j * z) (η j)) * (sgn (η i) * β i / 2)) =
      (∏ l : Fin n, qB (α l + β l * z) (η l)) * score α β η z := by
    simpa [smul_eq_mul] using h_deriv_eq
  exact h_prod.congr_deriv h_deriv_eq'

/-- The mean score is `0`. -/
theorem sum_lik_score {n : ℕ} (α β : Fin n → ℝ) {z : ℝ} (h : ∀ l, |α l + β l * z| < 1) :
    ∑ η, lik α β η z * score α β η z = 0 := by
  unfold score
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hl := abs_lt.1 (h l)
  have hc := sum_lik_mul_coord α β z l
    (fun b => sgn b * β l / (1 + sgn b * (α l + β l * z))) (fun _ => 1) (fun _ => rfl)
  simp only [mul_one] at hc
  rw [hc]
  have h1 : 1 + (α l + β l * z) ≠ 0 := by linarith
  have h2 : 1 + -(α l + β l * z) ≠ 0 := by linarith
  simp only [qB, sgn_true, sgn_false, one_mul, neg_one_mul]
  field_simp
  ring

-- TARGET

/-- The Fisher information of the model: informations add over the coordinates. -/
theorem sum_lik_score_sq {n : ℕ} (α β : Fin n → ℝ) {z : ℝ} (h : ∀ l, |α l + β l * z| < 1) :
    ∑ η, lik α β η z * score α β η z ^ 2 = ∑ l, β l ^ 2 / (1 - (α l + β l * z) ^ 2) := by
  set a := fun l => α l + β l * z with ha
  set u := fun l b => sgn b * β l / (1 + sgn b * a l) with hu
  have ha_abs_lt : ∀ l, -1 < a l ∧ a l < 1 := fun l => abs_lt.mp (h l)
  have h_denom_pos : ∀ l, 1 + a l ≠ 0 := fun l => by
    rcases ha_abs_lt l with ⟨h_left, h_right⟩; linarith
  have h_denom_neg : ∀ l, 1 - a l ≠ 0 := fun l => by
    rcases ha_abs_lt l with ⟨h_left, h_right⟩; linarith
  have h_denom_sq : ∀ l, 1 - a l ^ 2 ≠ 0 := fun l => by
    rcases ha_abs_lt l with ⟨h_left, h_right⟩; nlinarith
  have h_score_eq : ∀ (η : Fin n → Bool), score α β η z = ∑ l, u l (η l) := by
    intro η; simp [score, u, a]
  have h_sq_expand : ∀ (η : Fin n → Bool), (∑ l, u l (η l)) ^ 2 = ∑ l, ∑ l', u l (η l) * u l' (η l') := by
    intro η
    calc
      (∑ l, u l (η l)) ^ 2 = (∑ l, u l (η l)) * (∑ l', u l' (η l')) := by ring
      _ = ∑ l, u l (η l) * (∑ l', u l' (η l')) := by rw [Finset.sum_mul]
      _ = ∑ l, ∑ l', u l (η l) * u l' (η l') := by simp_rw [Finset.mul_sum]
  have h_sum_swap : ∑ η, lik α β η z * score α β η z ^ 2 =
      ∑ l, ∑ l', ∑ η, lik α β η z * (u l (η l) * u l' (η l')) := by
    simp_rw [h_score_eq, h_sq_expand]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_comm]
  -- diagonal sum: l = l'
  have h_diag : ∀ l, ∑ η, lik α β η z * (u l (η l) * u l (η l)) =
      (qB (a l) true * (u l true) ^ 2 + qB (a l) false * (u l false) ^ 2) * ∑ η, lik α β η z := by
    intro l
    have hG : ∀ η, (fun (_ : Fin n → Bool) => (1 : ℝ)) (flipAt l η) = (fun (_ : Fin n → Bool) => (1 : ℝ)) η := by
      intro η; rfl
    have h_eq := sum_lik_mul_coord α β z l (fun b => (u l b) ^ 2) (fun _ => (1 : ℝ)) hG
    -- h_eq: ∑ η, lik * (u l (η l))^2 * 1 = (qB ... * (u l true)^2 + qB ... * (u l false)^2) * ∑ η, lik * 1
    simpa [mul_assoc, sq, u, a] using h_eq
  -- off-diagonal sum: l ≠ l'
  have h_offdiag_factor : ∀ l, qB (a l) true * u l true + qB (a l) false * u l false = 0 := by
    intro l
    have htemp : (1 + a l) / 2 * (β l / (1 + a l)) + (1 - a l) / 2 * (-β l / (1 - a l)) = 0 := by
      field_simp [h_denom_pos l, h_denom_neg l]
      ring
    simpa [qB, u, sgn, sub_eq_add_neg] using htemp
  have h_offdiag : ∀ l l', l ≠ l' → ∑ η, lik α β η z * (u l (η l) * u l' (η l')) = 0 := by
    intro l l' h_ne
    have hG : ∀ η, (fun η' => u l' (η' l')) (flipAt l η) = (fun η' => u l' (η' l')) η := by
      intro η
      dsimp
      rw [flipAt_ne h_ne.symm]
    have h_eq := sum_lik_mul_coord α β z l (u l) (fun η' => u l' (η' l')) hG
    calc
      ∑ η, lik α β η z * (u l (η l) * u l' (η l')) =
          ∑ η, (lik α β η z * u l (η l)) * u l' (η l') := by
        refine Finset.sum_congr rfl (fun η _ => ?_); ring
      _ = (qB (a l) true * u l true + qB (a l) false * u l false) *
          ∑ η, lik α β η z * u l' (η l') := by
        simpa [mul_assoc, u, a] using h_eq
      _ = 0 * ∑ η, lik α β η z * u l' (η l') := by rw [h_offdiag_factor l]
      _ = 0 := by simp
  -- simplify the diagonal term
  have h_diag_simp : ∀ l, qB (a l) true * (u l true) ^ 2 + qB (a l) false * (u l false) ^ 2 =
      β l ^ 2 / (1 - a l ^ 2) := by
    intro l
    have htemp : (1 + a l) / 2 * ((β l / (1 + a l)) ^ 2) + (1 - a l) / 2 * ((-β l / (1 - a l)) ^ 2) =
        β l ^ 2 / (1 - a l ^ 2) := by
      field_simp [h_denom_pos l, h_denom_neg l, h_denom_sq l]
      ring
    simpa [qB, u, sgn, sub_eq_add_neg] using htemp
  -- split each inner sum over l' into l=l' and l≠l'
  have h_split : ∀ l, ∑ l', ∑ η, lik α β η z * (u l (η l) * u l' (η l')) =
      ∑ η, lik α β η z * (u l (η l) * u l (η l)) := by
    intro l
    calc
      ∑ l', ∑ η, lik α β η z * (u l (η l) * u l' (η l')) =
          ∑ l', (if l' = l then ∑ η, lik α β η z * (u l (η l) * u l (η l)) else 0) := by
        refine Finset.sum_congr rfl (fun l' hl' => ?_)
        by_cases h_eq : l' = l
        · subst h_eq; simp
        · rw [h_offdiag l l' (Ne.symm h_eq)]
          simp [h_eq]
      _ = ∑ η, lik α β η z * (u l (η l) * u l (η l)) := by simp
  calc
    ∑ η, lik α β η z * score α β η z ^ 2
        = ∑ l, ∑ l', ∑ η, lik α β η z * (u l (η l) * u l' (η l')) := h_sum_swap
    _ = ∑ l, ∑ η, lik α β η z * (u l (η l) * u l (η l)) := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [h_split l]
    _ = ∑ l, ((qB (a l) true * (u l true) ^ 2 + qB (a l) false * (u l false) ^ 2) * ∑ η, lik α β η z) := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [h_diag l]
    _ = ∑ l, ((β l ^ 2 / (1 - a l ^ 2)) * ∑ η, lik α β η z) := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [h_diag_simp l]
    _ = ∑ l, (β l ^ 2 / (1 - a l ^ 2)) * 1 := by rw [sum_lik α β z]
    _ = ∑ l, β l ^ 2 / (1 - a l ^ 2) := by simp
    _ = ∑ l, β l ^ 2 / (1 - (α l + β l * z) ^ 2) := by simp [a]

/-- The sign of coordinate `i` has mean `a_i` against anything that ignores it. -/
theorem sum_lik_sgn_mul {n : ℕ} (α β : Fin n → ℝ) (z : ℝ) (i : Fin n) (G : (Fin n → Bool) → ℝ)
    (hG : ∀ η, G (flipAt i η) = G η) :
    ∑ η, lik α β η z * sgn (η i) * G η = (α i + β i * z) * ∑ η, lik α β η z * G η := by
  rw [sum_lik_mul_coord α β z i sgn G hG]
  congr 1
  simp only [qB, sgn_true, sgn_false]
  ring

-- TARGET

/-- Step (i) of Lemma 4.11: a prediction `yh` that ignores coordinate `i` has average excess loss
`(yh - a_i)²` over the comparator `a_i`. -/
theorem sum_lik_round {n : ℕ} (α β : Fin n → ℝ) (z : ℝ) (i : Fin n) (yh : (Fin n → Bool) → ℝ)
    (hyh : ∀ η, yh (flipAt i η) = yh η) :
    ∑ η, lik α β η z * ((yh η - sgn (η i)) ^ 2 - (α i + β i * z - sgn (η i)) ^ 2) =
      ∑ η, lik α β η z * (yh η - (α i + β i * z)) ^ 2 := by
  set a := α i + β i * z with ha
  have hsum_lik : ∑ η : Fin n → Bool, lik α β η z = 1 := sum_lik α β z
  have h_diff_zero : (∑ η : Fin n → Bool, lik α β η z * ((yh η - sgn (η i)) ^ 2 - (a - sgn (η i)) ^ 2)) -
                     (∑ η : Fin n → Bool, lik α β η z * (yh η - a) ^ 2) = 0 := by
    have h_pointwise_diff (η : Fin n → Bool) : ((yh η - sgn (η i)) ^ 2 - (a - sgn (η i)) ^ 2) - (yh η - a) ^ 2 = 2 * (yh η - a) * (a - sgn (η i)) := by
      ring
    have hG_sub' : ∀ η : Fin n → Bool, (fun ξ : Fin n → Bool => yh ξ - a) (flipAt i η) = (fun ξ : Fin n → Bool => yh ξ - a) η := by
      intro η; simp [hyh η]
    have hsum_sgn_mul_sub' : ∑ η : Fin n → Bool, lik α β η z * sgn (η i) * (yh η - a) = a * ∑ η : Fin n → Bool, lik α β η z * (yh η - a) :=
      sum_lik_sgn_mul α β z i (fun ξ => yh ξ - a) hG_sub'
    calc
      (∑ η : Fin n → Bool, lik α β η z * ((yh η - sgn (η i)) ^ 2 - (a - sgn (η i)) ^ 2)) -
      (∑ η : Fin n → Bool, lik α β η z * (yh η - a) ^ 2) =
        ∑ η : Fin n → Bool, (lik α β η z * ((yh η - sgn (η i)) ^ 2 - (a - sgn (η i)) ^ 2) - lik α β η z * (yh η - a) ^ 2) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ η : Fin n → Bool, lik α β η z * (((yh η - sgn (η i)) ^ 2 - (a - sgn (η i)) ^ 2) - (yh η - a) ^ 2) := by
        refine Finset.sum_congr rfl fun η _ => ?_
        ring
      _ = ∑ η : Fin n → Bool, lik α β η z * (2 * (yh η - a) * (a - sgn (η i))) := by
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [h_pointwise_diff η]
      _ = 2 * ∑ η : Fin n → Bool, lik α β η z * (yh η - a) * (a - sgn (η i)) := by
        simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      _ = 2 * (∑ η : Fin n → Bool, (lik α β η z * (yh η - a) * a - lik α β η z * (yh η - a) * sgn (η i))) := by
        refine congrArg (fun x => 2 * x) (Finset.sum_congr rfl fun η _ => ?_)
        ring
      _ = 2 * ((∑ η : Fin n → Bool, lik α β η z * (yh η - a) * a) - (∑ η : Fin n → Bool, lik α β η z * (yh η - a) * sgn (η i))) := by
        rw [Finset.sum_sub_distrib]
      _ = 2 * ((a * ∑ η : Fin n → Bool, lik α β η z * (yh η - a)) - (∑ η : Fin n → Bool, lik α β η z * sgn (η i) * (yh η - a))) := by
        simp [Finset.mul_sum, mul_comm, mul_assoc]
      _ = 2 * ((a * ∑ η : Fin n → Bool, lik α β η z * (yh η - a)) - (a * ∑ η : Fin n → Bool, lik α β η z * (yh η - a))) := by
        rw [hsum_sgn_mul_sub']
      _ = 2 * 0 := by ring
      _ = 0 := by ring
  linarith

/-- A sum over sign vectors split by the first sign. -/
theorem sum_cons_bool {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ η, f η = ∑ η, f (Fin.cons true η) + ∑ η, f (Fin.cons false η) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp f, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

/-- The likelihood split by the first sign. -/
theorem lik_cons {n : ℕ} (α β : Fin (n + 1) → ℝ) (b : Bool) (η : Fin n → Bool) (z : ℝ) :
    lik α β (Fin.cons b η) z =
      qB (α 0 + β 0 * z) b * lik (fun l => α l.succ) (fun l => β l.succ) η z := by
  unfold lik
  rw [Fin.prod_univ_succ]
  simp

/-- The parameters of the coordinates before `i`, those after set to `0`. -/
def cut {n : ℕ} (i : ℕ) (α : Fin n → ℝ) : Fin n → ℝ := fun l => if l.val < i then α l else 0

/-- Marginalization: against a function of the first `i` coordinates, the model can be cut at `i`. -/
theorem sum_lik_cut {n : ℕ} (α β : Fin n → ℝ) (z : ℝ) (i : ℕ) (G : (Fin n → Bool) → ℝ)
    (hG : ∀ η η', (∀ l : Fin n, l.val < i → η l = η' l) → G η = G η') :
    ∑ η, lik α β η z * G η = ∑ η, lik (cut i α) (cut i β) η z * G η := by
  induction n generalizing i with
  | zero =>
    simp [lik]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have hc : ∀ η, G η = G (fun _ => false) := fun η => hG _ _ fun l hl => absurd hl (by omega)
      simp_rw [hc, ← Finset.sum_mul, sum_lik]
    · rw [sum_cons_bool, sum_cons_bool]
      simp_rw [lik_cons, mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      have hc0 : ∀ γ : Fin (n + 1) → ℝ, cut i γ 0 = γ 0 := fun γ => by simp [cut, hi]
      have hcs : ∀ γ : Fin (n + 1) → ℝ, (fun l : Fin n => cut i γ l.succ) =
          cut (i - 1) (fun l => γ l.succ) := fun γ => by
        funext l
        simp only [cut, Fin.val_succ]
        congr 1
        exact propext (by omega)
      rw [hc0, hc0, hcs, hcs]
      have key : ∀ b, ∑ η, lik (fun l => α l.succ) (fun l => β l.succ) η z * G (Fin.cons b η) =
          ∑ η, lik (cut (i - 1) fun l => α l.succ) (cut (i - 1) fun l => β l.succ) η z *
            G (Fin.cons b η) := fun b =>
        ih _ _ (i - 1) (fun η => G (Fin.cons b η)) fun η η' h => hG _ _ fun l hl => by
          cases l using Fin.cases with
          | zero => rfl
          | succ l => simpa using h l (by simp at hl; omega)
      rw [key true, key false]

end RegretKappa.Lower
