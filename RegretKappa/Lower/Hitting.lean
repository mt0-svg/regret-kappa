import RegretKappa.Lower.Drift

/-!
# Lower bound: the hitting time of phase 1

The paper, Lemma B.4 at `j = 1` only, for the chain of `Lower/Drift.lean` stopped at
level `L`: below the level it moves by `step`, at or above it stays put (`sstep`, the move `0`).
As in the paper, the adversary plays the feature `0` once the level is reached, and phase 2
starts at a fixed round.

* `ex st n f ρ`, the expectation of `f` after `n` steps of the two-move chain `st` started at `ρ`,
  by the backward recursion (the Markov property built in), and `avg_chainOf`: it is the uniform
  average over sign vectors of `f` at the chain driven by the signs.
* Optional stopping on a finite horizon: `lyap ρ + n · P(ρ_n² < L) ≤ E[g(ρ_n)]` (`lyap_add_mul_le`,
  by induction on the drift inequality, the event `{ρ_j² < L}` decreasing in `j`); every state has
  `ρ² < L + 1` (`step_sq_le`), so `E[g(ρ_n)] ≤ G = 16 e^{(L+1)/2}`, and `P(ρ_n² < L) ≤ G / n`.

Departure from the paper: no geometric tail (the restart argument and the blocks `j₀`). One Markov
bound gives a failure probability `O(1 / log² T)` at the level `L = 2 log T - 4 log log T`, enough
for the asymptotic target.
-/

namespace RegretKappa.Lower

open Real

/-- The expectation of `f` after `n` steps of the chain with moves `st ρ true`, `st ρ false`
(probability `1/2` each), started at `ρ`. -/
noncomputable def ex (st : ℝ → Bool → ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, ρ => f ρ
  | n + 1, f, ρ => (ex st n f (st ρ true) + ex st n f (st ρ false)) / 2

/-- The chain with moves `st`, started at `ρ` and driven by the signs `ζ`. -/
noncomputable def chainOf (st : ℝ → Bool → ℝ) (ρ : ℝ) (ζ : ℕ → Bool) : ℕ → ℝ
  | 0 => ρ
  | n + 1 => st (chainOf st ρ ζ n) (ζ n)

/-- The chain after `n + 1` steps from the signs `b, ζ` is the chain after `n` steps from the first
move. -/
theorem chainOf_ncons (st : ℝ → Bool → ℝ) (ρ : ℝ) (b : Bool) (ζ : ℕ → Bool) (n : ℕ) :
    chainOf st ρ (ncons b ζ) (n + 1) = chainOf st (st ρ b) ζ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chainOf, ih]; rfl

/-- The backward recursion is the uniform average over the sign vectors. -/
theorem avg_chainOf (st : ℝ → Bool → ℝ) (f : ℝ → ℝ) (n : ℕ) (ρ : ℝ) :
    avg n (fun ξ => f (chainOf st ρ (ext ξ) n)) = ex st n f ρ := by
  induction n generalizing ρ with
  | zero =>
    simp [avg_const, chainOf, ex]
  | succ n ih =>
    rw [avg_cons]
    have h1 : (fun (ξ : Fin n → Bool) => f (chainOf st ρ (ext (Fin.cons true ξ)) (n + 1))) =
        (fun ξ => f (chainOf st (st ρ true) (ext ξ) n)) := by
      ext ξ
      calc
        f (chainOf st ρ (ext (Fin.cons true ξ)) (n + 1)) = f (chainOf st ρ (ncons true (ext ξ)) (n + 1)) := by rw [ext_cons]
        _ = f (chainOf st (st ρ true) (ext ξ) n) := by rw [chainOf_ncons]
    have h2 : (fun (ξ : Fin n → Bool) => f (chainOf st ρ (ext (Fin.cons false ξ)) (n + 1))) =
        (fun ξ => f (chainOf st (st ρ false) (ext ξ) n)) := by
      ext ξ
      calc
        f (chainOf st ρ (ext (Fin.cons false ξ)) (n + 1)) = f (chainOf st ρ (ncons false (ext ξ)) (n + 1)) := by rw [ext_cons]
        _ = f (chainOf st (st ρ false) (ext ξ) n) := by rw [chainOf_ncons]
    rw [h1, h2]
    rw [ih (st ρ true), ih (st ρ false)]
    simp [ex]

theorem ex_const (st : ℝ → Bool → ℝ) (n : ℕ) (c ρ : ℝ) : ex st n (fun _ => c) ρ = c := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih => simp only [ex, ih]; ring

/-- Monotonicity on a set that the moves preserve. -/
theorem ex_mono_on (st : ℝ → Bool → ℝ) {S : Set ℝ} (hS : ∀ ρ ∈ S, ∀ b, st ρ b ∈ S)
    {f g : ℝ → ℝ} (hfg : ∀ ρ ∈ S, f ρ ≤ g ρ) (n : ℕ) {ρ : ℝ} (hρ : ρ ∈ S) :
    ex st n f ρ ≤ ex st n g ρ := by
  induction n generalizing ρ with
  | zero => exact hfg ρ hρ
  | succ n ih =>
    simp only [ex]
    linarith [ih (hS ρ hρ true), ih (hS ρ hρ false)]

/-- At a fixed point of both moves the chain stays put. -/
theorem ex_fixed (st : ℝ → Bool → ℝ) {ρ : ℝ} (h : ∀ b, st ρ b = ρ) (f : ℝ → ℝ) (n : ℕ) :
    ex st n f ρ = f ρ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ex, h, ih]; ring

/-- The move stopped at level `L`: `mv ρ` below the level, `0` at or above it. -/
noncomputable def smv (L ρ : ℝ) : ℝ := if ρ ^ 2 < L then mv ρ else 0

/-- One step of the chain stopped at level `L`. -/
noncomputable def sstep (L ρ : ℝ) (b : Bool) : ℝ := ρ * √(1 - smv L ρ) + sgn b * √(smv L ρ)

theorem smv_nonneg (L ρ : ℝ) : 0 ≤ smv L ρ := by
  unfold smv; split_ifs
  · exact (mv_pos ρ).le
  · exact le_rfl

theorem smv_le (L ρ : ℝ) : smv L ρ ≤ 1 / 4 := by
  unfold smv; split_ifs
  · exact mv_le ρ
  · norm_num

theorem sstep_of_lt {L ρ : ℝ} (h : ρ ^ 2 < L) (b : Bool) : sstep L ρ b = step ρ b := by
  simp [sstep, smv, h, step]

theorem sstep_of_le {L ρ : ℝ} (h : L ≤ ρ ^ 2) (b : Bool) : sstep L ρ b = ρ := by
  simp [sstep, smv, not_lt.2 h]

/-- The stopped chain never goes above `L + 1` in `ρ²`. -/
theorem sstep_sq_lt {L ρ : ℝ} (h : ρ ^ 2 < L + 1) (b : Bool) : sstep L ρ b ^ 2 < L + 1 := by
  rcases lt_or_ge (ρ ^ 2) L with hL | hL
  · rw [sstep_of_lt hL]
    linarith [step_sq_le ρ b]
  · rw [sstep_of_le hL]
    exact h

/-- The indicator of the states below level `L`. -/
noncomputable def below (L ρ : ℝ) : ℝ := if ρ ^ 2 < L then 1 else 0

theorem ex_below_nonneg (L : ℝ) (n : ℕ) (ρ : ℝ) : 0 ≤ ex (sstep L) n (below L) ρ := by
  have h := ex_mono_on (sstep L) (S := Set.univ) (fun _ _ _ => Set.mem_univ _)
    (f := fun _ => (0 : ℝ)) (g := below L) (fun ρ _ => by unfold below; split_ifs <;> norm_num) n
    (Set.mem_univ ρ)
  rwa [ex_const] at h

theorem ex_below_le_one (L : ℝ) (n : ℕ) (ρ : ℝ) : ex (sstep L) n (below L) ρ ≤ 1 := by
  have h := ex_mono_on (sstep L) (S := Set.univ) (fun _ _ _ => Set.mem_univ _)
    (f := below L) (g := fun _ => (1 : ℝ)) (fun ρ _ => by unfold below; split_ifs <;> norm_num) n
    (Set.mem_univ ρ)
  rwa [ex_const] at h

-- TARGET

/-- Optional stopping on a finite horizon: `g(ρ) + n P(ρ_n² < L) ≤ E[g(ρ_n)]`. -/
theorem lyap_add_mul_le (L : ℝ) (n : ℕ) (ρ : ℝ) :
    lyap ρ + n * ex (sstep L) n (below L) ρ ≤ ex (sstep L) n lyap ρ := by
  induction n generalizing ρ with
  | zero =>
      simp [ex]
  | succ n ih =>
      simp [ex]
      have ih_true := ih (sstep L ρ true)
      have ih_false := ih (sstep L ρ false)
      by_cases h : ρ ^ 2 < L
      · have hsstep_true : sstep L ρ true = step ρ true := sstep_of_lt h true
        have hsstep_false : sstep L ρ false = step ρ false := sstep_of_lt h false
        rw [hsstep_true] at ih_true ⊢
        rw [hsstep_false] at ih_false ⊢
        have h_drift := drift ρ
        have h_below := ex_below_le_one L (n + 1) ρ
        simp [ex, hsstep_true, hsstep_false] at h_below
        nlinarith
      · have hL : L ≤ ρ ^ 2 := by linarith
        have hsstep_true : sstep L ρ true = ρ := sstep_of_le hL true
        have hsstep_false : sstep L ρ false = ρ := sstep_of_le hL false
        rw [hsstep_true, hsstep_false]
        have h_fixed_lyap : ex (sstep L) n lyap ρ = lyap ρ := ex_fixed (sstep L) (fun b => sstep_of_le hL b) lyap n
        have h_fixed_below : ex (sstep L) n (below L) ρ = below L ρ := ex_fixed (sstep L) (fun b => sstep_of_le hL b) (below L) n
        rw [h_fixed_lyap, h_fixed_below]
        have h_below_zero : below L ρ = 0 := by
          unfold below
          simp [hL]
        rw [h_below_zero]
        simp

/-- Every state of the stopped chain started below `L + 1` has `g ≤ 16 e^{(L+1)/2}`. -/
theorem ex_lyap_le (L : ℝ) (n : ℕ) {ρ : ℝ} (hρ : ρ ^ 2 < L + 1) :
    ex (sstep L) n lyap ρ ≤ 16 * exp ((L + 1) / 2) := by
  set S : Set ℝ := {ρ | ρ ^ 2 < L + 1} with hS
  have hρS : ρ ∈ S := by
    rw [hS, Set.mem_ofPred_eq]
    exact hρ
  have hS_preserve : ∀ ρ' ∈ S, ∀ b, sstep L ρ' b ∈ S := by
    intro ρ' hρ'S b
    rw [hS, Set.mem_ofPred_eq] at hρ'S ⊢
    exact sstep_sq_lt hρ'S b
  have hlyap_le : ∀ ρ' ∈ S, lyap ρ' ≤ (fun _ => 16 * exp ((L + 1) / 2)) ρ' := by
    intro ρ' hρ'S
    rw [hS, Set.mem_ofPred_eq] at hρ'S
    unfold lyap
    have hsq : ρ' ^ 2 / 2 ≤ (L + 1) / 2 := by linarith
    have hexp : exp (ρ' ^ 2 / 2) ≤ exp ((L + 1) / 2) := (Real.exp_le_exp.mpr hsq)
    nlinarith
  have hconst : ex (sstep L) n (fun _ => 16 * exp ((L + 1) / 2)) ρ = 16 * exp ((L + 1) / 2) :=
    ex_const (sstep L) n (16 * exp ((L + 1) / 2)) ρ
  calc
    ex (sstep L) n lyap ρ ≤ ex (sstep L) n (fun _ => 16 * exp ((L + 1) / 2)) ρ :=
      ex_mono_on (sstep L) hS_preserve hlyap_le n hρS
    _ = 16 * exp ((L + 1) / 2) := hconst

/-- **Hitting time bound.** From a state with `ρ² < L + 1`, the stopped chain is still below
level `L` after `n ≥ 1` steps with probability at most `16 e^{(L+1)/2} / n`. -/
theorem ex_below_le (L : ℝ) {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : ρ ^ 2 < L + 1) :
    ex (sstep L) n (below L) ρ ≤ 16 * exp ((L + 1) / 2) / n := by
  have h1 := lyap_add_mul_le L n ρ
  have h2 := ex_lyap_le L n hρ
  have h3 := lyap_pos ρ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  linarith

end RegretKappa.Lower
