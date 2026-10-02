import RegretKappa.UnknownBT.UnknownB.LemmaS
import RegretKappa.UnknownBT.Anytime.Learner
import RegretKappa.UnknownBT.Anytime.Schedule

/-!
# The running-maximum learner

The bound on the statement, for every potential schedule
(`IsSchedule lam A`, 0-indexed: round `t` here is round `t + 1` of the paper). The learner
`learnerRM lam` predicts `0` while the running maximum `M = max_{i<t} |y i|` is `0`, and otherwise
`M` times the potential prediction at the level `lam t` on the outcomes divided by `M`;
`learnerBT = learnerRM lamB` (`learnerBT_eq`).

The invariant (`inv_le`): after `n` rounds, the partial loss of the learner (the costs
`ŷ² - 2 ŷ y`) plus `M_n² Ψ_{n-1}(ρ_n / M_n)` is at most `KB M_n²`, where `ρ_n = S_n/√V_n` and
`Ψ_t = psiOf lam A t`. A round with `M` unchanged is the one-round inequality (`stepLam`) and
(H1); a round that raises `M > 0` is the surprise round (`lemmaS_state`) and (H1); the first round
with a nonzero outcome is the Lipschitz bound `psi_lip` and (H2). The end of the play
(`regret_le`) is the regret identity
(`regret_eqRM`) and the terminal bound `w² - Ψ_{T-1}(w) ≤ L` for `w² ≤ T`.
-/

namespace RegretKappa.UnknownBT.UB

open Real Finset RegretKappa RegretKappa.UpperSharp

/-- The running-maximum learner at the levels `lam`: `0` while the outcomes seen are all `0`,
otherwise `M` times the prediction of `learnerLam lam` on the outcomes divided by
`M = max_{i<t} |y i|`. -/
noncomputable def learnerRM (lam : ℕ → ℝ) : AnytimeLearner where
  predict t xs ys :=
    if runMax ys = 0 then 0 else runMax ys * (learnerLam lam).predict t xs fun i => ys i / runMax ys

theorem learnerBT_eq : learnerBT = learnerRM lamB := rfl

/-- The prediction of `learnerRM lam` in round `n`, from the state. -/
noncomputable def yhatRM (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ :=
  if pmax y n = 0 then 0
  else pmax y n * predLam (lam n) (Upper.Ssum x y n / pmax y n) (Upper.Vsum x n) (Upper.ext x n)

theorem predictionRM_eq (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) (t : Fin T) :
    ((learnerRM lam).restrict T).prediction x y t = yhatRM lam x y t := by
  have hX : ∀ i : Fin t, x (Fin.castLE t.isLt (Fin.castSucc i)) = Upper.ext x i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [Upper.ext, hi, ↓reduceDIte]
    rfl
  have hY : ∀ i : Fin t, y (Fin.castLE t.isLt.le i) = Upper.ext y i := fun i => by
    have hi : (i : ℕ) < T := lt_trans i.isLt t.isLt
    simp only [Upper.ext, hi, ↓reduceDIte]
    rfl
  have hL : x (Fin.castLE t.isLt (Fin.last t)) = Upper.ext x t := by
    simp only [Upper.ext, t.isLt, ↓reduceDIte]
    rfl
  have hM : (runMax fun s : Fin (t : ℕ) => Upper.ext y s) = pmax y t := rfl
  unfold Learner.prediction AnytimeLearner.restrict learnerRM learnerLam yhatRM Upper.Ssum Upper.Vsum
  simp only [hX, hY, hL]
  rw [hM]
  rw [Fin.sum_univ_eq_sum_range (fun i => Upper.ext x i * (Upper.ext y i / pmax y t)) t,
    Fin.sum_univ_eq_sum_range (fun i => Upper.ext x i ^ 2) t, Finset.sum_div]
  simp only [mul_div_assoc]

/-- **The regret identity** for `learnerRM lam`: the regret is the sum of the costs plus
`ρ_T²`. -/
theorem regret_eqRM (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) :
    regret ((learnerRM lam).restrict T) x y =
      ∑ i ∈ range T, (yhatRM lam x y i ^ 2 - 2 * yhatRM lam x y i * Upper.ext y i) +
        (Upper.Ssum x y T / √(Upper.Vsum x T)) ^ 2 := by
  unfold regret learnerLoss
  have e1 : ∑ t, (((learnerRM lam).restrict T).prediction x y t - y t) ^ 2 =
      ∑ t : Fin T, (yhatRM lam x y t ^ 2 - 2 * yhatRM lam x y t * Upper.ext y t) +
        ∑ t, y t ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [predictionRM_eq, Upper.ext_val]
    ring
  rw [e1, add_sub_assoc, Upper.sum_sq_sub_bestLinearLoss, Upper.Ssum_univ, Upper.Vsum_univ,
    Fin.sum_univ_eq_sum_range
      (fun i => yhatRM lam x y i ^ 2 - 2 * yhatRM lam x y i * Upper.ext y i) T]

/-! ### Facts about the state -/

theorem pmax_nonneg {T : ℕ} (y : Fin T → ℝ) (n : ℕ) : 0 ≤ pmax y n := by
  unfold pmax runMax
  exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem pmax_le_succ {T : ℕ} (y : Fin T → ℝ) (n : ℕ) : pmax y n ≤ pmax y (n + 1) := by
  rw [pmax_succ]
  exact le_max_left _ _

theorem ext_eq_zero_of_pmax {T : ℕ} {y : Fin T → ℝ} {n : ℕ} (h : pmax y n = 0) {i : ℕ}
    (hi : i < n) : Upper.ext y i = 0 :=
  abs_nonpos_iff.1 (h ▸ le_pmax y n i hi)

theorem Ssum_eq_zero_of_pmax {T : ℕ} (x : Fin T → ℝ) {y : Fin T → ℝ} {n : ℕ}
    (h : pmax y n = 0) : Upper.Ssum x y n = 0 := by
  unfold Upper.Ssum
  exact Finset.sum_eq_zero fun i hi => by
    rw [ext_eq_zero_of_pmax h (Finset.mem_range.1 hi), mul_zero]

/-- `V = 0 → S = 0` for every play. -/
theorem Ssum_eq_zero_of_Vsum' {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) :
    Upper.Vsum x n = 0 → Upper.Ssum x y n = 0 := fun h => by
  unfold Upper.Vsum at h
  have hx := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (Upper.ext x i)).1 h
  unfold Upper.Ssum
  exact Finset.sum_eq_zero fun i hi => by rw [pow_eq_zero_iff two_ne_zero |>.1 (hx i hi), zero_mul]

theorem abs_ext_le_pmax {T : ℕ} (y : Fin T → ℝ) (n : ℕ) : |Upper.ext y n| ≤ pmax y (n + 1) :=
  le_pmax y (n + 1) n (Nat.lt_succ_self n)

/-! ### The invariant -/

/-- The cost of round `i`: `ŷ² - 2 ŷ y`. -/
noncomputable def costRM (lam : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) (i : ℕ) : ℝ :=
  yhatRM lam x y i ^ 2 - 2 * yhatRM lam x y i * Upper.ext y i

/-- The normalized state after `n` rounds: `ρ_n / M_n`. -/
noncomputable def wRM {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ :=
  Upper.Ssum x y n / √(Upper.Vsum x n) / pmax y n

/-- The invariant: the partial loss plus `M_n² Ψ_{n-1}(ρ_n/M_n)`. -/
noncomputable def invRM (lam A : ℕ → ℝ) {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, costRM lam x y i + pmax y n ^ 2 * psiOf lam A (n - 1) (wRM x y n)

/-- `psiOf` in the units of `Upper`: `2 log((λ/2 + G w)/(A/2))`. -/
theorem psiOf_eq (lam A : ℕ → ℝ) (t : ℕ) (w : ℝ) :
    psiOf lam A t w = 2 * log ((lam t / 2 + Upper.G w) / (A t / 2)) := by
  unfold psiOf
  rw [Gam_eq]
  congr 2
  field_simp

/-- (H1) on the potentials: `Q_{t+1} ≤ Ψ_t`. -/
theorem h1_log {lam A : ℕ → ℝ} (hs : IsSchedule lam A) (t : ℕ) (w : ℝ) :
    2 * log ((lam (t + 1) + 3 + Gam w) / A (t + 1)) ≤ psiOf lam A t w := by
  have h := hs.h1 t w
  have hG := Gam_nonneg w
  have hl := hs.lam_pos (t + 1)
  have hA := hs.A_pos (t + 1)
  unfold psiOf
  have := Real.log_le_log (by positivity) h
  linarith

theorem cost_eq (M p y : ℝ) (hM : M ≠ 0) :
    (M * p) ^ 2 - 2 * (M * p) * y = M ^ 2 * (p ^ 2 - 2 * p * (y / M)) := by
  field_simp

/-- (H1) shifted to round `n ≥ 1`. -/
theorem h1_log' {lam A : ℕ → ℝ} (hs : IsSchedule lam A) {n : ℕ} (hn : 1 ≤ n) (w : ℝ) :
    2 * log ((lam n + 3 + Gam w) / A n) ≤ psiOf lam A (n - 1) w := by
  have h := h1_log hs (n - 1) w
  rwa [Nat.sub_add_cancel hn] at h

/-- A round with the running maximum unchanged: the one-round inequality and (H1). -/
theorem round_same {lam A : ℕ → ℝ} (hs : IsSchedule lam A) {n : ℕ} (hn : 1 ≤ n)
    {S V x y M : ℝ} (hM : 0 < M) (hV : 0 ≤ V) (hSV : V = 0 → S = 0) (hy : |y| ≤ M) :
    (M * predLam (lam n) (S / M) V x) ^ 2 - 2 * (M * predLam (lam n) (S / M) V x) * y +
        M ^ 2 * psiOf lam A n ((S + x * y) / √(V + x ^ 2) / M) ≤
      M ^ 2 * psiOf lam A (n - 1) (S / √V / M) := by
  have hy1 : |y / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).2 hy
  have hSV' : V = 0 → S / M = 0 := fun h => by rw [hSV h, zero_div]
  have hst := stepLam (x := x) (hs.lam_pos n) hV hSV' hy1
  have hH := h1_log' hs hn (S / √V / M)
  have e1 : (S / M + x * (y / M)) / √(V + x ^ 2) = (S + x * y) / √(V + x ^ 2) / M := by
    field_simp
  have e2 : S / M / √V = S / √V / M := div_right_comm _ _ _
  rw [e1, e2] at hst
  have hA := hs.A_pos n
  have hl := hs.lam_pos n
  have hG1 := Gam_nonneg ((S + x * y) / √(V + x ^ 2) / M)
  have hG2 := Gam_nonneg (S / √V / M)
  have hQ : 2 * log ((lam n + 3 + Gam (S / √V / M)) / A n) =
      2 * log (lam n + 3 + Gam (S / √V / M)) - 2 * log (A n) := by
    rw [Real.log_div (by positivity) hA.ne']; ring
  have hP : psiOf lam A n ((S + x * y) / √(V + x ^ 2) / M) =
      2 * log (lam n + Gam ((S + x * y) / √(V + x ^ 2) / M)) - 2 * log (A n) := by
    unfold psiOf
    rw [Real.log_div (by positivity) hA.ne']; ring
  rw [cost_eq M _ y hM.ne', hP]
  have key : predLam (lam n) (S / M) V x ^ 2 - 2 * predLam (lam n) (S / M) V x * (y / M) +
      (2 * log (lam n + Gam ((S + x * y) / √(V + x ^ 2) / M)) - 2 * log (A n)) ≤
      psiOf lam A (n - 1) (S / √V / M) := by linarith
  have := mul_le_mul_of_nonneg_left key (sq_nonneg M)
  linarith

/-- A round that raises the running maximum from `M > 0` to `M' = |y|`: surprise round, (H1). -/
theorem round_up {lam A : ℕ → ℝ} (hs : IsSchedule lam A) {n : ℕ} (hn : 1 ≤ n)
    {S V x y M M' : ℝ} (hM : 0 < M) (hMM : M ≤ M') (hy : |y| = M') (hV : 0 ≤ V)
    (hSV : V = 0 → S = 0) :
    (M * predLam (lam n) (S / M) V x) ^ 2 - 2 * (M * predLam (lam n) (S / M) V x) * y +
        M' ^ 2 * psiOf lam A n ((S + x * y) / √(V + x ^ 2) / M') ≤
      M ^ 2 * psiOf lam A (n - 1) (S / √V / M) + KB * (M' ^ 2 - M ^ 2) := by
  have hSV' : V = 0 → S / M = 0 := fun h => by rw [hSV h, zero_div]
  have hm : 1 ≤ M' / M := (one_le_div hM).2 hMM
  have hym : |y / M| = M' / M := by rw [abs_div, abs_of_pos hM, hy]
  have hl := hs.lam_pos n
  have hA := hs.A_pos n
  have hH2 := hs.h2 n
  rw [Gam_zero] at hH2
  have hA' : lam n / 2 + 3 / 2 + Upper.G 0 ≤ A n / 2 := by rw [G_zero]; linarith
  have hS := lemmaS_state (l := lam n / 2) (A := A n / 2) (x := x) (half_pos hl) hA' hV hSV' hm hym
  rw [← predLam_eq (lam n) hV hSV'] at hS
  have hM' : 0 < M' := lt_of_lt_of_le hM hMM
  have e1 : (S / M + x * (y / M)) / √(V + x ^ 2) / (M' / M) = (S + x * y) / √(V + x ^ 2) / M' := by
    field_simp
  have e2 : S / M / √V = S / √V / M := div_right_comm _ _ _
  rw [e1, e2] at hS
  have hP : ∀ w, psiOf lam A n w = 2 * log ((lam n / 2 + Upper.G w) / (A n / 2)) :=
    fun w => psiOf_eq lam A n w
  have hQ : 2 * log ((lam n / 2 + 3 / 2 + Upper.G (S / √V / M)) / (A n / 2)) =
      2 * log ((lam n + 3 + Gam (S / √V / M)) / A n) := by
    rw [Gam_eq]
    congr 2
    field_simp
  rw [← hP, hQ] at hS
  have hH := h1_log' hs hn (S / √V / M)
  rw [cost_eq M _ y hM.ne']
  have key := mul_le_mul_of_nonneg_left (hS.trans (by linarith : _ ≤
    psiOf lam A (n - 1) (S / √V / M) + KB * ((M' / M) ^ 2 - 1))) (sq_nonneg M)
  have e3 : M ^ 2 * (M' / M) ^ 2 = M' ^ 2 := by field_simp
  have e4 : M ^ 2 * (KB * ((M' / M) ^ 2 - 1)) = KB * (M' ^ 2 - M ^ 2) := by field_simp
  have k2 : M ^ 2 * (predLam (lam n) (S / M) V x ^ 2 - 2 * predLam (lam n) (S / M) V x * (y / M) +
      (M' / M) ^ 2 * psiOf lam A n ((S + x * y) / √(V + x ^ 2) / M')) =
      M ^ 2 * (predLam (lam n) (S / M) V x ^ 2 - 2 * predLam (lam n) (S / M) V x * (y / M)) +
      M' ^ 2 * psiOf lam A n ((S + x * y) / √(V + x ^ 2) / M') := by
    rw [mul_add, ← mul_assoc, e3]
  have k3 : M ^ 2 * (psiOf lam A (n - 1) (S / √V / M) + KB * ((M' / M) ^ 2 - 1)) =
      M ^ 2 * psiOf lam A (n - 1) (S / √V / M) + KB * (M' ^ 2 - M ^ 2) := by
    rw [mul_add, e4]
  linarith

/-- The first round with a nonzero outcome (or any round from the zero state): the potential
term is at most `lipB M'²`. -/
theorem round_first {lam A : ℕ → ℝ} (hs : IsSchedule lam A) (n : ℕ) {V x y M' : ℝ}
    (hV : 0 ≤ V) (hy : |y| ≤ M') :
    M' ^ 2 * psiOf lam A n ((0 + x * y) / √(V + x ^ 2) / M') ≤ lipB * M' ^ 2 := by
  have hl := hs.lam_pos n
  have hA := hs.A_pos n
  have hH2 := hs.h2 n
  rw [Gam_zero] at hH2
  set w := (0 + x * y) / √(V + x ^ 2) / M' with hw
  have hw1 : |w| ≤ 1 := by
    rcases eq_or_lt_of_le (le_trans (abs_nonneg y) hy) with h | h
    · rw [hw, ← h, div_zero, abs_zero]; norm_num
    · rw [hw, zero_add, abs_div, abs_div, abs_of_pos h, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rcases eq_or_lt_of_le (Real.sqrt_nonneg (V + x ^ 2)) with h0 | h0
      · rw [← h0, div_zero, zero_div]; norm_num
      · rw [div_div, div_le_one (mul_pos h0 h)]
        have hx : |x| ≤ √(V + x ^ 2) := Real.abs_le_sqrt (by linarith)
        calc |x| * |y| ≤ √(V + x ^ 2) * M' :=
              mul_le_mul hx hy (abs_nonneg y) (Real.sqrt_nonneg _)
          _ = √(V + x ^ 2) * M' := rfl
  have hL := psi_lip (l := lam n / 2) (A := A n / 2) (x := w) (z := 0) (by linarith) (by linarith)
    hw1 (by rw [abs_zero]; exact abs_nonneg w)
  have h0 : 2 * log ((lam n / 2 + Upper.G 0) / (A n / 2)) ≤ 0 := by
    have hG := G_pos 0
    have : log ((lam n / 2 + Upper.G 0) / (A n / 2)) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one (by linarith)).2 (by rw [G_zero]; linarith))
    linarith
  rw [psiOf_eq]
  rw [abs_zero, sub_zero] at hL
  have hlip := lipB_nonneg
  have : 2 * log ((lam n / 2 + Upper.G w) / (A n / 2)) ≤ lipB := by nlinarith
  exact le_trans (mul_le_mul_of_nonneg_left this (sq_nonneg M')) (le_of_eq (mul_comm _ _))

/-- One round of the invariant. -/
theorem inv_step {lam A : ℕ → ℝ} (hs : IsSchedule lam A) {T : ℕ} (x y : Fin T → ℝ) (n : ℕ)
    (ih : invRM lam A x y n ≤ KB * pmax y n ^ 2) :
    invRM lam A x y (n + 1) ≤ KB * pmax y (n + 1) ^ 2 := by
  have hM0 : 0 ≤ pmax y n := pmax_nonneg y n
  have hMM : pmax y n ≤ pmax y (n + 1) := pmax_le_succ y n
  have hMs : pmax y (n + 1) = max (pmax y n) |Upper.ext y n| := pmax_succ y n
  have hS1 : Upper.Ssum x y (n + 1) = Upper.Ssum x y n + Upper.ext x n * Upper.ext y n :=
    Finset.sum_range_succ _ _
  have hV1 : Upper.Vsum x (n + 1) = Upper.Vsum x n + Upper.ext x n ^ 2 := Finset.sum_range_succ _ _
  have hV : 0 ≤ Upper.Vsum x n := Upper.Vsum_nonneg x n
  have hI1 : invRM lam A x y (n + 1) = ∑ i ∈ range n, costRM lam x y i + costRM lam x y n +
      pmax y (n + 1) ^ 2 * psiOf lam A n ((Upper.Ssum x y n + Upper.ext x n * Upper.ext y n) /
        √(Upper.Vsum x n + Upper.ext x n ^ 2) / pmax y (n + 1)) := by
    unfold invRM wRM
    rw [Finset.sum_range_succ, hS1, hV1, Nat.add_sub_cancel]
  have hI0 : invRM lam A x y n = ∑ i ∈ range n, costRM lam x y i +
      pmax y n ^ 2 * psiOf lam A (n - 1) (Upper.Ssum x y n / √(Upper.Vsum x n) / pmax y n) := rfl
  have hyle : |Upper.ext y n| ≤ pmax y (n + 1) := abs_ext_le_pmax y n
  rcases eq_or_lt_of_le hM0 with hM | hM
  · -- no nonzero outcome so far: the prediction is `0`
    have hy0 : yhatRM lam x y n = 0 := by unfold yhatRM; simp [← hM]
    have hc : costRM lam x y n = 0 := by unfold costRM; rw [hy0]; ring
    have hS0 : Upper.Ssum x y n = 0 := Ssum_eq_zero_of_pmax x hM.symm
    have hsum : ∑ i ∈ range n, costRM lam x y i ≤ 0 := by
      rw [hI0, ← hM] at ih
      simpa using ih
    have hf := round_first hs n (x := Upper.ext x n) hV hyle
    rw [hI1, hc, hS0]
    have := lipB_le_KB
    nlinarith [sq_nonneg (pmax y (n + 1))]
  · have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp [pmax, runMax] at hM
      · exact h
    have hSV := Ssum_eq_zero_of_Vsum' x y n
    have hy : yhatRM lam x y n = pmax y n * predLam (lam n) (Upper.Ssum x y n / pmax y n)
        (Upper.Vsum x n) (Upper.ext x n) := by
      unfold yhatRM; simp [hM.ne']
    have hc : costRM lam x y n = (pmax y n * predLam (lam n) (Upper.Ssum x y n / pmax y n)
        (Upper.Vsum x n) (Upper.ext x n)) ^ 2 - 2 * (pmax y n * predLam (lam n)
        (Upper.Ssum x y n / pmax y n) (Upper.Vsum x n) (Upper.ext x n)) * Upper.ext y n := by
      unfold costRM; rw [hy]
    rcases eq_or_lt_of_le hMM with hMM' | hMM'
    · -- the running maximum is unchanged: the one-round inequality
      have hyM : |Upper.ext y n| ≤ pmax y n := hMM' ▸ hyle
      have hr := round_same hs hn (x := Upper.ext x n) hM hV hSV hyM
      rw [hI1, hc, ← hMM']
      rw [hI0] at ih
      linarith
    · -- the running maximum increases: the surprise round
      have hyM : |Upper.ext y n| = pmax y (n + 1) := by
        rw [hMs] at hMM' ⊢
        rcases le_total (pmax y n) |Upper.ext y n| with h | h
        · exact (max_eq_right h).symm
        · rw [max_eq_left h] at hMM'; exact absurd hMM' (lt_irrefl _)
      have hr := round_up hs hn (x := Upper.ext x n) hM hMM hyM hV hSV
      rw [hI1, hc]
      rw [hI0] at ih
      linarith

theorem inv_le {lam A : ℕ → ℝ} (hs : IsSchedule lam A) {T : ℕ} (x y : Fin T → ℝ) (n : ℕ) :
    invRM lam A x y n ≤ KB * pmax y n ^ 2 := by
  induction n with
  | zero =>
    simp [invRM, pmax, runMax]
  | succ n ih => exact inv_step hs x y n ih

/-- **The running-maximum bound.** For every potential schedule and every play, if
`w² - Ψ_{T-1}(w) ≤ L` for `w² ≤ T`, the running-maximum learner has
`Regret_T ≤ M_T² (L + KB)`, `M_T = max_t |y t|`. -/
theorem regret_le {lam A : ℕ → ℝ} (hs : IsSchedule lam A) {T : ℕ} (x y : Fin T → ℝ) (L : ℝ)
    (hterm : ∀ w : ℝ, w ^ 2 ≤ T → w ^ 2 - psiOf lam A (T - 1) w ≤ L) :
    regret ((learnerRM lam).restrict T) x y ≤ runMax y ^ 2 * (L + KB) := by
  rw [regret_eqRM, pmax_all]
  have hinv := inv_le hs x y T
  unfold invRM at hinv
  have hM0 := pmax_nonneg y T
  rcases eq_or_lt_of_le hM0 with hM | hM
  · have hS0 : Upper.Ssum x y T = 0 := Ssum_eq_zero_of_pmax x hM.symm
    rw [← hM] at hinv ⊢
    simp only [hS0, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      add_zero, mul_zero] at hinv ⊢
    unfold costRM at hinv
    exact hinv
  · set M := pmax y T with hMdef
    set S := Upper.Ssum x y T with hSdef
    set V := Upper.Vsum x T with hVdef
    have hY : ∀ i, |Upper.ext y i / M| ≤ 1 := fun i => by
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      by_cases hi : i < T
      · exact le_pmax y T i hi
      · simp only [Upper.ext, hi, ↓reduceDIte, abs_zero]
        exact hM.le
    have hCS := Upper.sq_sum_mul_le (Upper.ext x) (fun i => Upper.ext y i / M) hY T
    have hsum : ∑ i ∈ range T, Upper.ext x i * (Upper.ext y i / M) = S / M := by
      rw [hSdef, Upper.Ssum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum] at hCS
    have hw : (S / √V / M) ^ 2 ≤ T := by
      rcases eq_or_lt_of_le (Upper.Vsum_nonneg x T) with h0 | h0
      · rw [show V = 0 from hVdef.trans h0.symm, Real.sqrt_zero, div_zero, zero_div]
        simp
      · rw [div_right_comm, div_pow, Real.sq_sqrt h0.le, div_le_iff₀ h0]
        exact hCS
    have ht := hterm _ hw
    have e : (S / √V) ^ 2 = M ^ 2 * (S / √V / M) ^ 2 := by field_simp
    rw [e]
    have : ∑ i ∈ range T, (yhatRM lam x y i ^ 2 - 2 * yhatRM lam x y i * Upper.ext y i) =
        ∑ i ∈ range T, costRM lam x y i := rfl
    rw [this]
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg M)
    have hwdef : wRM x y T = S / √V / M := rfl
    rw [hwdef] at hinv
    nlinarith

end RegretKappa.UnknownBT.UB
