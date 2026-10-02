import RegretKappa.Statement
import RegretKappa.StatementCheck.Indep

/-!
# The target statement against a formalization written separately

`RegretKappa.StatementCheck.Indep` (namespace `Indep`) is a formalization of the target written
separately from the text of the problem alone. Its model agrees with `RegretKappa/Statement.lean`:
a causal learner `(t : Fin T) → (Fin (t + 1) → ℝ) × (Fin t → ℝ) → ℝ`,
sequences `ℕ → ℝ` read on `[0, T)`, outcomes bounded by `B` at every index, the same regret.

Discrepancy. `Indep.minimaxRegret` takes `sSup` and `sInf` in `ℝ`. The learner that predicts its
current feature has regret unbounded above over the features, so its `sSup` is the junk value `0`;
every learner has a value `≥ 0`, hence `Indep.minimaxRegret B T = 0` for all `B ≥ 0` and all `T`
(`Indep_minimaxRegret_eq_zero`). So `Indep.UpperBound` holds trivially and `Indep.LowerBound`,
`Indep.KappaThree` are false (`Indep_upperBound`, `not_Indep_lowerBound`, `not_Indep_kappaThree`).

Repair. `IndepEReal` keeps every definition of `Indep` and only moves the two `sSup` and the `sInf`
of the minimax regret to `EReal`. Its minimax regret is the one of `RegretKappa/Statement.lean`
(`IndepEReal.minimaxRegret_eq`), and its three statements are equivalent to the target ones
(`IndepEReal.kappaThree_iff`, `IndepEReal.upperBound_iff`, `IndepEReal.lowerBound_iff`).
-/

open Filter Topology Set

namespace RegretKappa.StatementCheck

/-! ### The learners and the plays of the two versions -/

/-- A learner of `Indep` as a learner of the target statement. -/
def toLearner {T : ℕ} (f : Indep.CausalLearner T) : Learner T :=
  ⟨fun t a b => f t (a, b)⟩

/-- A learner of the target statement as a learner of `Indep`. -/
def ofLearner {T : ℕ} (L : Learner T) : Indep.CausalLearner T :=
  fun t p => L.predict t p.1 p.2

theorem toLearner_ofLearner {T : ℕ} (L : Learner T) : toLearner (ofLearner L) = L := rfl

/-- A sequence on `ℕ` read on the rounds `[0, T)`. -/
def restrict (T : ℕ) (x : ℕ → ℝ) : Fin T → ℝ := fun i => x i

/-- A sequence on the rounds `[0, T)`, extended by `0`. -/
def extend {T : ℕ} (x : Fin T → ℝ) : ℕ → ℝ := fun i => if h : i < T then x ⟨i, h⟩ else 0

theorem restrict_extend {T : ℕ} (x : Fin T → ℝ) : restrict T (extend x) = x := by
  funext i
  simp [restrict, extend, i.isLt]

theorem extend_mem_boundedY {T : ℕ} {B : ℝ} (hB : 0 ≤ B) {y : Fin T → ℝ}
    (hy : ∀ t, |y t| ≤ B) : extend y ∈ Indep.boundedY B := by
  intro i
  unfold extend
  split_ifs with h
  · exact hy _
  · simpa using hB

theorem evalLearner_coe {T : ℕ} (f : Indep.CausalLearner T) (x y : ℕ → ℝ) (t : Fin T) :
    Indep.evalLearner f x y t = f t (fun i => x i, fun i => y i) := by
  simp [Indep.evalLearner, t.isLt]

/-- The regret of `Indep` is the target regret of the same learner on the same play. -/
theorem causalRegret_eq {T : ℕ} (f : Indep.CausalLearner T) (x y : ℕ → ℝ) :
    Indep.causalRegret f x y T = regret (toLearner f) (restrict T x) (restrict T y) := by
  unfold Indep.causalRegret Indep.regret regret
  congr 1
  · unfold Indep.cumSqErr learnerLoss
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [evalLearner_coe, Indep.sqErr]
    change (y t - f t (fun i => x i, fun i => y i)) ^ 2 =
      (f t (fun i => x i, fun i => y i) - y t) ^ 2
    ring
  · unfold Indep.bestLinLoss bestLinearLoss linearLoss
    congr 1
    ext c
    simp only [mem_range]
    refine exists_congr fun θ => ?_
    rw [Finset.sum_range]
    refine Eq.congr_left (Finset.sum_congr rfl fun t _ => ?_)
    simp only [restrict]
    ring

/-! ### The junk value of `Indep.minimaxRegret` -/

/-- The learner that predicts its current feature. -/
def predictFeature (T : ℕ) : Indep.CausalLearner T := fun t p => p.1 (Fin.last t)

theorem regret_nonneg_zero {T : ℕ} (L : Learner T) : 0 ≤ regret L 0 0 := by
  have h0 : bestLinearLoss (0 : Fin T → ℝ) 0 ≤ 0 := by
    simpa [linearLoss] using bestLinearLoss_le (0 : Fin T → ℝ) 0 0
  have h1 : 0 ≤ learnerLoss L 0 0 := by unfold learnerLoss; positivity
  unfold regret
  linarith

theorem zero_mem_boundedY {B : ℝ} (hB : 0 ≤ B) : (0 : ℕ → ℝ) ∈ Indep.boundedY B := by
  intro i
  simpa using hB

theorem restrict_zero (T : ℕ) : restrict T 0 = 0 := rfl

/-- Every value `Indep.learnerRegretSup f B` is nonnegative, junk or not. -/
theorem learnerRegretSup_nonneg {T : ℕ} (f : Indep.CausalLearner T) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ Indep.learnerRegretSup f B := by
  unfold Indep.learnerRegretSup
  by_cases ho : BddAbove (range fun x : ℕ → ℝ =>
      sSup ((Indep.boundedY B).image fun y => Indep.causalRegret f x y T))
  · refine le_csSup_of_le ho (mem_range_self 0) ?_
    by_cases hi : BddAbove ((Indep.boundedY B).image fun y => Indep.causalRegret f 0 y T)
    · refine le_csSup_of_le hi (mem_image_of_mem _ (zero_mem_boundedY hB)) ?_
      rw [causalRegret_eq, restrict_zero]
      exact regret_nonneg_zero _
    · rw [Real.sSup_of_not_bddAbove hi]
  · rw [Real.sSup_of_not_bddAbove ho]

/-- For `T ≥ 1` the learner that predicts its current feature gets the junk value `0`. -/
theorem learnerRegretSup_predictFeature {T : ℕ} (hT : 1 ≤ T) {B : ℝ} (hB : 0 ≤ B) :
    Indep.learnerRegretSup (predictFeature T) B = 0 := by
  unfold Indep.learnerRegretSup
  refine Real.sSup_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  -- The inner set at the constant feature `n` is bounded above and contains a regret `≥ n ^ 2`.
  set n : ℝ := max M 0 + 1 with hn
  let x : ℕ → ℝ := fun _ => n
  have hbdd :
      BddAbove ((Indep.boundedY B).image fun y => Indep.causalRegret (predictFeature T) x y T) := by
    refine ⟨T * (n + B) ^ 2, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [causalRegret_eq]
    unfold regret
    have h0 := le_bestLinearLoss (restrict T x) (restrict T y) fun θ => by
      unfold linearLoss; positivity
    have h1 : learnerLoss (toLearner (predictFeature T)) (restrict T x) (restrict T y) ≤
        T * (n + B) ^ 2 := by
      unfold learnerLoss
      calc ∑ t : Fin T, ((toLearner (predictFeature T)).prediction (restrict T x) (restrict T y) t
              - restrict T y t) ^ 2
          ≤ ∑ _t : Fin T, (n + B) ^ 2 := Finset.sum_le_sum fun t _ => by
            change (n - y t) ^ 2 ≤ (n + B) ^ 2
            have hyt := abs_le.1 (hy t)
            have : 0 ≤ n := by rw [hn]; positivity
            nlinarith
        _ = T * (n + B) ^ 2 := by simp
    linarith
  have hlow : (T : ℝ) * n ^ 2 ≤
      sSup ((Indep.boundedY B).image fun y => Indep.causalRegret (predictFeature T) x y T) := by
    refine le_csSup_of_le hbdd (mem_image_of_mem _ (zero_mem_boundedY hB)) ?_
    rw [causalRegret_eq, restrict_zero]
    unfold regret
    have h0 : bestLinearLoss (restrict T x) (0 : Fin T → ℝ) ≤ 0 := by
      simpa [linearLoss] using bestLinearLoss_le (restrict T x) (0 : Fin T → ℝ) 0
    have h1 : learnerLoss (toLearner (predictFeature T)) (restrict T x) 0 = T * n ^ 2 := by
      unfold learnerLoss
      change ∑ _t : Fin T, (n - 0) ^ 2 = T * n ^ 2
      simp
    linarith
  have hmem := hM (mem_range_self x)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hn1 : 1 ≤ n := by rw [hn]; linarith [le_max_right M 0]
  have hMn : M < n := by rw [hn]; linarith [le_max_left M 0]
  nlinarith

/-- **Discrepancy.** The minimax regret of `Indep` is `0` for every `B ≥ 0` and every horizon. -/
theorem Indep_minimaxRegret_eq_zero {B : ℝ} (hB : 0 ≤ B) (T : ℕ) : Indep.minimaxRegret B T = 0 := by
  unfold Indep.minimaxRegret
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos T with rfl | hT
    · refine ⟨predictFeature 0, le_antisymm ?_ (learnerRegretSup_nonneg _ hB)⟩
      unfold Indep.learnerRegretSup
      have hs : ∀ x : ℕ → ℝ,
          (Indep.boundedY B).image (fun y => Indep.causalRegret (predictFeature 0) x y 0) =
            {0} := by
        intro x
        refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨0, zero_mem_boundedY hB, ?_⟩, ?_⟩
        · dsimp only
          rw [causalRegret_eq]; unfold regret learnerLoss bestLinearLoss linearLoss; simp
        · rintro _ ⟨y, -, rfl⟩
          dsimp only
          rw [causalRegret_eq]; unfold regret learnerLoss bestLinearLoss linearLoss; simp
      simp [hs]
    · exact ⟨predictFeature T, learnerRegretSup_predictFeature hT hB⟩
  · rintro _ ⟨f, rfl⟩
    exact learnerRegretSup_nonneg f hB

theorem Indep_upperBound : Indep.UpperBound := by
  intro B hB ε hε
  filter_upwards with T
  rw [Indep_minimaxRegret_eq_zero hB.le]
  have := Real.log_natCast_nonneg T
  positivity

theorem not_Indep_lowerBound : ¬ Indep.LowerBound := by
  intro h
  obtain ⟨T, hT, hT2⟩ := ((h 1 one_pos 1 one_pos).and (eventually_ge_atTop 2)).exists
  rw [Indep_minimaxRegret_eq_zero zero_le_one] at hT
  have := scale_pos one_pos hT2
  linarith

theorem not_Indep_kappaThree : ¬ Indep.KappaThree := by
  intro h
  have h1 := h 1 one_pos
  simp only [Indep_minimaxRegret_eq_zero zero_le_one, zero_div] at h1
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  norm_num at this

end RegretKappa.StatementCheck

/-! ### The repaired version: `Indep` with its minimax regret in `EReal` -/

namespace IndepEReal

open RegretKappa RegretKappa.StatementCheck

/-- `Indep.learnerRegretSup` with the two `sSup` in `EReal`. -/
noncomputable def learnerRegretSup {T : ℕ} (f : Indep.CausalLearner T) (B : ℝ) : EReal :=
  sSup (Set.range (fun (x : ℕ → ℝ) =>
    sSup ((Indep.boundedY B).image (fun y => (Indep.causalRegret f x y T : EReal)))))

/-- `Indep.minimaxRegret` with the `sInf` in `EReal`. -/
noncomputable def minimaxRegret (B : ℝ) (T : ℕ) : EReal :=
  sInf (Set.range (fun (f : Indep.CausalLearner T) => learnerRegretSup f B))

/-- `Indep.KappaThree` on the repaired minimax regret. -/
def KappaThree : Prop :=
  ∀ B > 0, Tendsto (fun T : ℕ => minimaxRegret B T / ((B ^ 2 * Real.log (T : ℝ) : ℝ) : EReal))
    atTop (𝓝 3)

/-- `Indep.UpperBound` on the repaired minimax regret. -/
def UpperBound : Prop :=
  ∀ B > 0, ∀ ε > 0, ∀ᶠ (T : ℕ) in atTop,
    minimaxRegret B T ≤ (((3 + ε) * B ^ 2 * Real.log (T : ℝ) : ℝ) : EReal)

/-- `Indep.LowerBound` on the repaired minimax regret. -/
def LowerBound : Prop :=
  ∀ B > 0, ∀ ε > 0, ∀ᶠ (T : ℕ) in atTop,
    minimaxRegret B T ≥ (((3 - ε) * B ^ 2 * Real.log (T : ℝ) : ℝ) : EReal)

theorem learnerRegretSup_eq {T : ℕ} (f : Indep.CausalLearner T) {B : ℝ} (hB : 0 ≤ B) :
    learnerRegretSup f B =
      ⨆ (x : Fin T → ℝ) (y : Fin T → ℝ) (_ : ∀ t, |y t| ≤ B),
        (regret (toLearner f) x y : EReal) := by
  unfold learnerRegretSup
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [causalRegret_eq]
    exact le_iSup_of_le (restrict T x) (le_iSup_of_le (restrict T y)
      (le_iSup_of_le (fun t => hy t) le_rfl))
  · refine iSup_le fun x => iSup_le fun y => iSup_le fun hy => ?_
    refine le_sSup_of_le (mem_range_self (extend x))
      (le_sSup ⟨extend y, extend_mem_boundedY hB hy, ?_⟩)
    dsimp only
    rw [causalRegret_eq, restrict_extend, restrict_extend]

/-- The repaired minimax regret is the target one. -/
theorem minimaxRegret_eq {B : ℝ} (hB : 0 ≤ B) (T : ℕ) :
    minimaxRegret B T = RegretKappa.minimaxRegret T B := by
  unfold minimaxRegret RegretKappa.minimaxRegret
  refine le_antisymm ?_ ?_
  · refine le_iInf fun L => sInf_le_of_le (mem_range_self (ofLearner L)) ?_
    rw [learnerRegretSup_eq _ hB, toLearner_ofLearner]
  · refine le_sInf ?_
    rintro _ ⟨f, rfl⟩
    dsimp only
    rw [learnerRegretSup_eq _ hB]
    exact iInf_le _ (toLearner f)

theorem kappaThree_iff : KappaThree ↔ RegretKappa.KappaEqThree := by
  refine forall₂_congr fun B hB => ?_
  simp only [minimaxRegret_eq hB.le]

theorem upperBound_iff : UpperBound ↔ RegretKappa.UpperBound := by
  constructor
  · intro h B hB ε hε
    filter_upwards [h B hB (ε / 2) (by linarith), eventually_ge_atTop 2] with T hT hT2
    rw [minimaxRegret_eq hB.le] at hT
    have hD := scale_pos hB hT2
    have hlt : (3 + ε / 2) * B ^ 2 * Real.log T < (3 + ε) * B ^ 2 * Real.log T := by nlinarith
    exact exists_learner_of_minimaxRegret_lt (hT.trans_lt (EReal.coe_lt_coe_iff.2 hlt))
  · intro h B hB ε hε
    filter_upwards [h B hB ε hε] with T ⟨L, hL⟩
    rw [minimaxRegret_eq hB.le]
    exact minimaxRegret_le_of_learner L hL

theorem lowerBound_iff : LowerBound ↔ RegretKappa.LowerBound := by
  constructor
  · intro h B hB ε hε
    filter_upwards [h B hB (ε / 2) (by linarith), eventually_ge_atTop 2] with T hT hT2
    rw [minimaxRegret_eq hB.le] at hT
    have hD := scale_pos hB hT2
    have hlt : (3 - ε) * B ^ 2 * Real.log T < (3 - ε / 2) * B ^ 2 * Real.log T := by nlinarith
    exact exists_play_of_lt_minimaxRegret ((EReal.coe_lt_coe_iff.2 hlt).trans_le hT)
  · intro h B hB ε hε
    filter_upwards [h B hB ε hε] with T hT
    rw [minimaxRegret_eq hB.le]
    exact le_minimaxRegret hT

end IndepEReal
