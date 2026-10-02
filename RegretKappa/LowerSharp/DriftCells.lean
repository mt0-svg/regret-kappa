import RegretKappa.LowerSharp.DriftCheck

/-!
# The drift certificate

The paper, Lemma 4.3 (b) and Computation 4.4: one kernel check per cell `[j/10, (j+1)/10)`,
with the order N = 14 of the partial sums, and `drift_table`, the inequality on `[0, 2.8)`.
Written by `code/lean-upper-sharp/drift_cells.gp` (the trees: `drift_tree_lib.gp`). Each cell
is its own declaration, since the kernel cost of one declaration grows faster than linearly.
-/

namespace RegretKappa.LowerSharp

/-- The move table of the paper (Section 4.2): `s_j` on the cell `[j/10, (j+1)/10)`, the values
of `(5/8) e^{-m²/2}` at the midpoints `m` rounded to four decimals. -/
def stab : ℕ → ℚ
  | 0 => 3121/5000
  | 1 => 309/500
  | 2 => 3029/5000
  | 3 => 5879/10000
  | 4 => 353/625
  | 5 => 5373/10000
  | 6 => 253/500
  | 7 => 2359/5000
  | 8 => 871/2000
  | 9 => 199/500
  | 10 => 3601/10000
  | 11 => 1613/5000
  | 12 => 2861/10000
  | 13 => 2513/10000
  | 14 => 273/1250
  | 15 => 47/250
  | 16 => 801/5000
  | 17 => 169/1250
  | 18 => 1129/10000
  | 19 => 467/5000
  | 20 => 191/2500
  | 21 => 31/500
  | 22 => 497/10000
  | 23 => 79/2000
  | 24 => 311/10000
  | 25 => 121/5000
  | 26 => 187/10000
  | 27 => 71/5000
  | _ => 0

/-- The kernel check of cell 0 (1 leaves). -/
theorem cell0_check : (check 14 (3121/5000) 8 (0 / 10) (1 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 0. -/
theorem drift_cell0 (ρ : ℝ) (h1 : (0 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (1 : ℝ) / 10) :
    0 ≤ driftGap ((stab 0 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell0_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 1 (1 leaves). -/
theorem cell1_check : (check 14 (309/500) 8 (1 / 10) (2 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 1. -/
theorem drift_cell1 (ρ : ℝ) (h1 : (1 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (2 : ℝ) / 10) :
    0 ≤ driftGap ((stab 1 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell1_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 2 (1 leaves). -/
theorem cell2_check : (check 14 (3029/5000) 8 (2 / 10) (3 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 2. -/
theorem drift_cell2 (ρ : ℝ) (h1 : (2 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (3 : ℝ) / 10) :
    0 ≤ driftGap ((stab 2 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell2_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 3 (1 leaves). -/
theorem cell3_check : (check 14 (5879/10000) 8 (3 / 10) (4 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 3. -/
theorem drift_cell3 (ρ : ℝ) (h1 : (3 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (4 : ℝ) / 10) :
    0 ≤ driftGap ((stab 3 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell3_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 4 (1 leaves). -/
theorem cell4_check : (check 14 (353/625) 8 (4 / 10) (5 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 4. -/
theorem drift_cell4 (ρ : ℝ) (h1 : (4 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (5 : ℝ) / 10) :
    0 ≤ driftGap ((stab 4 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell4_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 5 (1 leaves). -/
theorem cell5_check : (check 14 (5373/10000) 8 (5 / 10) (6 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 5. -/
theorem drift_cell5 (ρ : ℝ) (h1 : (5 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (6 : ℝ) / 10) :
    0 ≤ driftGap ((stab 5 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell5_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 6 (1 leaves). -/
theorem cell6_check : (check 14 (253/500) 8 (6 / 10) (7 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 6. -/
theorem drift_cell6 (ρ : ℝ) (h1 : (6 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (7 : ℝ) / 10) :
    0 ≤ driftGap ((stab 6 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell6_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 7 (1 leaves). -/
theorem cell7_check : (check 14 (2359/5000) 8 (7 / 10) (8 / 10)
    0).1 = true := by
  decide +kernel

/-- The drift on cell 7. -/
theorem drift_cell7 (ρ : ℝ) (h1 : (7 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (8 : ℝ) / 10) :
    0 ≤ driftGap ((stab 7 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell7_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 8 (2 leaves). -/
theorem cell8_check : (check 14 (871/2000) 8 (8 / 10) (9 / 10)
    1).1 = true := by
  decide +kernel

/-- The drift on cell 8. -/
theorem drift_cell8 (ρ : ℝ) (h1 : (8 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (9 : ℝ) / 10) :
    0 ≤ driftGap ((stab 8 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell8_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 9 (2 leaves). -/
theorem cell9_check : (check 14 (199/500) 8 (9 / 10) (10 / 10)
    1).1 = true := by
  decide +kernel

/-- The drift on cell 9. -/
theorem drift_cell9 (ρ : ℝ) (h1 : (9 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (10 : ℝ) / 10) :
    0 ≤ driftGap ((stab 9 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell9_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 10 (4 leaves). -/
theorem cell10_check : (check 14 (3601/10000) 8 (10 / 10) (11 / 10)
    19).1 = true := by
  decide +kernel

/-- The drift on cell 10. -/
theorem drift_cell10 (ρ : ℝ) (h1 : (10 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (11 : ℝ) / 10) :
    0 ≤ driftGap ((stab 10 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell10_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 11 (7 leaves). -/
theorem cell11_check : (check 14 (1613/5000) 8 (11 / 10) (12 / 10)
    1227).1 = true := by
  decide +kernel

/-- The drift on cell 11. -/
theorem drift_cell11 (ρ : ℝ) (h1 : (11 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (12 : ℝ) / 10) :
    0 ≤ driftGap ((stab 11 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell11_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 12 (11 leaves). -/
theorem cell12_check : (check 14 (2861/10000) 8 (12 / 10) (13 / 10)
    314151).1 = true := by
  decide +kernel

/-- The drift on cell 12. -/
theorem drift_cell12 (ρ : ℝ) (h1 : (12 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (13 : ℝ) / 10) :
    0 ≤ driftGap ((stab 12 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell12_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 13 (18 leaves). -/
theorem cell13_check : (check 14 (2513/10000) 8 (13 / 10) (14 / 10)
    5153171023).1 = true := by
  decide +kernel

/-- The drift on cell 13. -/
theorem drift_cell13 (ρ : ℝ) (h1 : (13 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (14 : ℝ) / 10) :
    0 ≤ driftGap ((stab 13 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell13_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 14 (32 leaves). -/
theorem cell14_check : (check 14 (273/1250) 8 (14 / 10) (15 / 10)
    1380113932199283871).1 = true := by
  decide +kernel

/-- The drift on cell 14. -/
theorem drift_cell14 (ρ : ℝ) (h1 : (14 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (15 : ℝ) / 10) :
    0 ≤ driftGap ((stab 14 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell14_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 15 (51 leaves). -/
theorem cell15_check : (check 14 (47/250) 8 (15 / 10) (16 / 10)
    379362829027192677197354519711).1 = true := by
  decide +kernel

/-- The drift on cell 15. -/
theorem drift_cell15 (ρ : ℝ) (h1 : (15 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (16 : ℝ) / 10) :
    0 ≤ driftGap ((stab 15 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell15_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 16 (65 leaves). -/
theorem cell16_check : (check 14 (801/5000) 8 (16 / 10) (17 / 10)
    110529200230075741541673742610051406143).1 = true := by
  decide +kernel

/-- The drift on cell 16. -/
theorem drift_cell16 (ρ : ℝ) (h1 : (16 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (17 : ℝ) / 10) :
    0 ≤ driftGap ((stab 16 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell16_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 17 (67 leaves). -/
theorem cell17_check : (check 14 (169/1250) 8 (17 / 10) (18 / 10)
    1631166027408019500143629019570765601087).1 = true := by
  decide +kernel

/-- The drift on cell 17. -/
theorem drift_cell17 (ρ : ℝ) (h1 : (17 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (18 : ℝ) / 10) :
    0 ≤ driftGap ((stab 17 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell17_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 18 (64 leaves). -/
theorem cell18_check : (check 14 (1129/10000) 8 (18 / 10) (19 / 10)
    25458608499841125675830090752109353279).1 = true := by
  decide +kernel

/-- The drift on cell 18. -/
theorem drift_cell18 (ρ : ℝ) (h1 : (18 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (19 : ℝ) / 10) :
    0 ≤ driftGap ((stab 18 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell18_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 19 (64 leaves). -/
theorem cell19_check : (check 14 (467/5000) 8 (19 / 10) (20 / 10)
    25458608499841125675830090752109353279).1 = true := by
  decide +kernel

/-- The drift on cell 19. -/
theorem drift_cell19 (ρ : ℝ) (h1 : (19 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (20 : ℝ) / 10) :
    0 ≤ driftGap ((stab 19 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell19_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 20 (64 leaves). -/
theorem cell20_check : (check 14 (191/2500) 8 (20 / 10) (21 / 10)
    25458608499841125675830090752109353279).1 = true := by
  decide +kernel

/-- The drift on cell 20. -/
theorem drift_cell20 (ρ : ℝ) (h1 : (20 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (21 : ℝ) / 10) :
    0 ≤ driftGap ((stab 20 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell20_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 21 (64 leaves). -/
theorem cell21_check : (check 14 (31/500) 8 (21 / 10) (22 / 10)
    25458608499841125675830090752109353279).1 = true := by
  decide +kernel

/-- The drift on cell 21. -/
theorem drift_cell21 (ρ : ℝ) (h1 : (21 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (22 : ℝ) / 10) :
    0 ≤ driftGap ((stab 21 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell21_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 22 (64 leaves). -/
theorem cell22_check : (check 14 (497/10000) 8 (22 / 10) (23 / 10)
    25458608499841125675830090752109353279).1 = true := by
  decide +kernel

/-- The drift on cell 22. -/
theorem drift_cell22 (ρ : ℝ) (h1 : (22 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (23 : ℝ) / 10) :
    0 ≤ driftGap ((stab 22 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell22_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 23 (64 leaves). -/
theorem cell23_check : (check 14 (79/2000) 8 (23 / 10) (24 / 10)
    25458608499841125675830090752109353279).1 = true := by
  decide +kernel

/-- The drift on cell 23. -/
theorem drift_cell23 (ρ : ℝ) (h1 : (23 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (24 : ℝ) / 10) :
    0 ≤ driftGap ((stab 23 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell23_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 24 (93 leaves). -/
theorem cell24_check : (check 14 (311/10000) 8 (24 / 10) (25 / 10)
    7337944304208373489075160711979605376373585955912233599).1 = true := by
  decide +kernel

/-- The drift on cell 24. -/
theorem drift_cell24 (ρ : ℝ) (h1 : (24 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (25 : ℝ) / 10) :
    0 ≤ driftGap ((stab 24 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell24_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 25 (128 leaves). -/
theorem cell25_check : (check 14 (121/5000) 8 (25 / 10) (26 / 10)
    8663115558839460662834107038584249281567296941925835957216867859106897670783).1 = true := by
  decide +kernel

/-- The drift on cell 25. -/
theorem drift_cell25 (ρ : ℝ) (h1 : (25 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (26 : ℝ) / 10) :
    0 ≤ driftGap ((stab 25 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell25_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 26 (128 leaves). -/
theorem cell26_check : (check 14 (187/10000) 8 (26 / 10) (27 / 10)
    8663115558839460662834107038584249281567296941925835957216867859106897670783).1 = true := by
  decide +kernel

/-- The drift on cell 26. -/
theorem drift_cell26 (ρ : ℝ) (h1 : (26 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (27 : ℝ) / 10) :
    0 ≤ driftGap ((stab 26 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell26_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- The kernel check of cell 27 (128 leaves). -/
theorem cell27_check : (check 14 (71/5000) 8 (27 / 10) (28 / 10)
    8663115558839460662834107038584249281567296941925835957216867859106897670783).1 = true := by
  decide +kernel

/-- The drift on cell 27. -/
theorem drift_cell27 (ρ : ℝ) (h1 : (27 : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (28 : ℝ) / 10) :
    0 ≤ driftGap ((stab 27 : ℚ) : ℝ) ρ :=
  check_sound 14 (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell27_check (by norm_num)
    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)

/-- **The paper, Lemma 4.3 (b).** On `[0, 2.8)`, with `s = s_j` on the cell `j = ⌊10 ρ⌋`, the
drift `8 h_s(ρ) - 8 e^{ρ²/2}` is at least `1`. -/
theorem drift_table (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 28 / 10) :
    0 ≤ driftGap ((stab ⌊10 * ρ⌋₊ : ℚ) : ℝ) ρ := by
  have hlo : ((⌊10 * ρ⌋₊ : ℕ) : ℝ) ≤ 10 * ρ := Nat.floor_le (by linarith)
  have hhi : 10 * ρ < ((⌊10 * ρ⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj : ⌊10 * ρ⌋₊ < 28 := by
    have : ((⌊10 * ρ⌋₊ : ℕ) : ℝ) < 28 := by linarith
    exact_mod_cast this
  generalize ⌊10 * ρ⌋₊ = j at hlo hhi hj ⊢
  interval_cases j <;> push_cast at hlo hhi
  · exact drift_cell0 ρ (by linarith) (by linarith)
  · exact drift_cell1 ρ (by linarith) (by linarith)
  · exact drift_cell2 ρ (by linarith) (by linarith)
  · exact drift_cell3 ρ (by linarith) (by linarith)
  · exact drift_cell4 ρ (by linarith) (by linarith)
  · exact drift_cell5 ρ (by linarith) (by linarith)
  · exact drift_cell6 ρ (by linarith) (by linarith)
  · exact drift_cell7 ρ (by linarith) (by linarith)
  · exact drift_cell8 ρ (by linarith) (by linarith)
  · exact drift_cell9 ρ (by linarith) (by linarith)
  · exact drift_cell10 ρ (by linarith) (by linarith)
  · exact drift_cell11 ρ (by linarith) (by linarith)
  · exact drift_cell12 ρ (by linarith) (by linarith)
  · exact drift_cell13 ρ (by linarith) (by linarith)
  · exact drift_cell14 ρ (by linarith) (by linarith)
  · exact drift_cell15 ρ (by linarith) (by linarith)
  · exact drift_cell16 ρ (by linarith) (by linarith)
  · exact drift_cell17 ρ (by linarith) (by linarith)
  · exact drift_cell18 ρ (by linarith) (by linarith)
  · exact drift_cell19 ρ (by linarith) (by linarith)
  · exact drift_cell20 ρ (by linarith) (by linarith)
  · exact drift_cell21 ρ (by linarith) (by linarith)
  · exact drift_cell22 ρ (by linarith) (by linarith)
  · exact drift_cell23 ρ (by linarith) (by linarith)
  · exact drift_cell24 ρ (by linarith) (by linarith)
  · exact drift_cell25 ρ (by linarith) (by linarith)
  · exact drift_cell26 ρ (by linarith) (by linarith)
  · exact drift_cell27 ρ (by linarith) (by linarith)

end RegretKappa.LowerSharp
