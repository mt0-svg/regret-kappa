import RegretKappa.LowerSharp.Move

/-!
# Sharp lower bound: the phase-1 chain

The paper, Lemma 4.2 (the chain), for the move rule of `LowerSharp/Move.lean` stopped at level
`L`. Signs `ζ`; round `0` plays the feature `1` and the outcome `sgn ζ₀`; round `t + 1`, with
`s = ssm L ρ_t`, plays the feature `√(V_t s / (1 - s))` and the outcome `sgn ζ_{t+1}`. Then
`V_{t+1} = V_t / (1 - s)` and `ρ_{t+1} = sst L ρ_t ζ_{t+1}`: `V_t = ∑_{s ≤ t} x_s²` (`sum_xS_sq`)
and `S_t = ρ_t √V_t` (`sum_xS_mul`). Once `ρ² ≥ L` the move is `0`: the feature is `0` and the
state stays put. The proofs are those of `Lower/Adversary.lean` for this move.
-/

namespace RegretKappa.LowerSharp

open Finset Real RegretKappa.Lower

/-- The phase-1 statistic `ρ_t = S_t / √V_t` after round `t`, from the signs `ζ`. -/
noncomputable def rhoS (L : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => sgn (ζ 0)
  | t + 1 => sst L (rhoS L ζ t) (ζ (t + 1))

/-- `V_t`, the sum of the squared features up to round `t`. -/
noncomputable def VS (L : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | t + 1 => VS L ζ t / (1 - ssm L (rhoS L ζ t))

/-- The phase-1 feature of round `t`. -/
noncomputable def xS (L : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => 1
  | t + 1 => √(VS L ζ t * ssm L (rhoS L ζ t) / (1 - ssm L (rhoS L ζ t)))

theorem VS_pos (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) : 0 < VS L ζ t := by
  induction t with
  | zero => simp [VS]
  | succ t ih =>
    simp only [VS]
    exact div_pos ih (by linarith [ssm_lt_one L (rhoS L ζ t)])

theorem xS_nonneg (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) : 0 ≤ xS L ζ t := by
  cases t with
  | zero => simp [xS]
  | succ t => exact Real.sqrt_nonneg _

theorem sum_xS_sq (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) :
    ∑ s ∈ range (t + 1), xS L ζ s ^ 2 = VS L ζ t := by
  induction t with
  | zero => simp [xS, VS]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    have hV : 0 < VS L ζ t := VS_pos L ζ t
    have hs0 : 0 ≤ ssm L (rhoS L ζ t) := ssm_nonneg L _
    have hd : 0 < 1 - ssm L (rhoS L ζ t) := by linarith [ssm_lt_one L (rhoS L ζ t)]
    rw [xS, Real.sq_sqrt (by positivity), VS]
    field_simp
    ring

/-- Lemma 4.2 of the paper: `S_t = ρ_t √V_t`. -/
theorem sum_xS_mul (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) :
    ∑ s ∈ range (t + 1), xS L ζ s * sgn (ζ s) = rhoS L ζ t * √(VS L ζ t) := by
  induction t with
  | zero => simp [xS, rhoS, VS]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [xS, rhoS, VS, sst, stepS]
    have hV : 0 ≤ VS L ζ t := (VS_pos L ζ t).le
    set s := ssm L (rhoS L ζ t)
    have hs0 : 0 ≤ s := ssm_nonneg L _
    have hd : 0 < 1 - s := by linarith [ssm_lt_one L (rhoS L ζ t)]
    have e1 : √(VS L ζ t / (1 - s)) * √(1 - s) = √(VS L ζ t) := by
      rw [← Real.sqrt_mul (div_nonneg hV hd.le), div_mul_cancel₀ _ hd.ne']
    have e2 : √(VS L ζ t / (1 - s)) * √s = √(VS L ζ t * s / (1 - s)) := by
      rw [← Real.sqrt_mul (div_nonneg hV hd.le)]
      ring_nf
    calc rhoS L ζ t * √(VS L ζ t) + √(VS L ζ t * s / (1 - s)) * sgn (ζ (t + 1))
        = rhoS L ζ t * (√(VS L ζ t / (1 - s)) * √(1 - s)) +
          (√(VS L ζ t / (1 - s)) * √s) * sgn (ζ (t + 1)) := by rw [e1, e2]
      _ = (rhoS L ζ t * √(1 - s) + sgn (ζ (t + 1)) * √s) * √(VS L ζ t / (1 - s)) := by ring

theorem rhoS_eq_chainOf (L : ℝ) (ζ : ℕ → Bool) (t : ℕ) :
    rhoS L ζ t = chainOf (sst L) (sgn (ζ 0)) (fun i => ζ (i + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [rhoS, ih]; rfl

/-- `ρ_t` and `V_t` depend on the signs up to `t` only. -/
theorem rhoS_VS_congr (L : ℝ) {ζ ζ' : ℕ → Bool} {t : ℕ} (h : ∀ i ≤ t, ζ i = ζ' i) :
    rhoS L ζ t = rhoS L ζ' t ∧ VS L ζ t = VS L ζ' t := by
  induction t with
  | zero => exact ⟨by simp [rhoS, h 0 le_rfl], rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (by omega)
    refine ⟨?_, ?_⟩
    · simp only [rhoS, h1, h (t + 1) le_rfl]
    · simp only [VS, h1, h2]

/-- The feature of round `t` depends on the signs before `t` only. -/
theorem xS_congr (L : ℝ) {ζ ζ' : ℕ → Bool} {t : ℕ} (h : ∀ i < t, ζ i = ζ' i) :
    xS L ζ t = xS L ζ' t := by
  cases t with
  | zero => rfl
  | succ t =>
    obtain ⟨h1, h2⟩ := rhoS_VS_congr L (t := t) fun i hi => h i (by omega)
    simp only [xS, h1, h2]

end RegretKappa.LowerSharp
