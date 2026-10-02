\\ Writes the module RegretKappa/LowerSharp/DriftCells.lean: the move table of the paper,
\\ one kernel check per cell of the bisection tree of drift_tree_lib.gp at the order
\\ NN = 14, and the drift inequality
\\ on [0, 2.8) as drift_table. The checker and its soundness are in DriftCheck.lean.
read("drift_tree_lib.gp");
bitsToNat(b) = my(v = Vec(b), c = 0); for(i = 1, #v, if(v[i] == "1", c += 2^(i-1))); c;
NN = 14;
{
my(F = "../../RegretKappa/LowerSharp/DriftCells.lean");
system(Str("rm -f ", F));
write(F, "import RegretKappa.LowerSharp.DriftCheck\n");
write(F, "/-!\n# The drift certificate\n");
write(F, "The drift on `[0, 2.8)` and its certificate: one kernel check per cell `[j/10, (j+1)/10)`,");
write(F, "with the order N = ", NN, " of the partial sums, and `drift_table`, the inequality on `[0, 2.8)`.");
write(F, "Written by `code/drift-cells/drift_cells.gp` (the trees: `drift_tree_lib.gp`). Each cell");
write(F, "is its own declaration, since the kernel cost of one declaration grows faster than linearly.\n-/\n");
write(F, "namespace RegretKappa.LowerSharp\n");
write(F, "/-- The move table of the paper: `s_j` on the cell `[j/10, (j+1)/10)`, the values");
write(F, "of `(5/8) e^{-m²/2}` at the midpoints `m` rounded to four decimals. -/");
write(F, "def stab : ℕ → ℚ");
for(j = 0, 27, write(F, "  | ", j, " => ", tab[j+1]));
write(F, "  | _ => 0");
for(j = 0, 27,
  my(t = tree(j/10, (j+1)/10, tab[j+1], NN, 0), c = bitsToNat(t[1]));
  write(F, "\n/-- The kernel check of cell ", j, " (", t[2], " leaves). -/");
  write(F, "theorem cell", j, "_check : (check ", NN, " (", tab[j+1], ") 8 (", j, " / 10) (", j + 1, " / 10)");
  write(F, "    ", c, ").1 = true := by");
  write(F, "  decide +kernel");
  write(F, "\n/-- The drift on cell ", j, ". -/");
  write(F, "theorem drift_cell", j, " (ρ : ℝ) (h1 : (", j, " : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (", j + 1, " : ℝ) / 10) :");
  write(F, "    0 ≤ driftGap ((stab ", j, " : ℚ) : ℝ) ρ :=");
  write(F, "  check_sound ", NN, " (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell", j, "_check (by norm_num)");
  write(F, "    (by norm_num) (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)"));
write(F, "\n/-- **The drift on `[0, 2.8)`.** With `s = s_j` on the cell `j = ⌊10 ρ⌋`, the");
write(F, "drift `8 h_s(ρ) - 8 e^{ρ²/2}` is at least `1`. -/");
write(F, "theorem drift_table (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 28 / 10) :");
write(F, "    0 ≤ driftGap ((stab ⌊10 * ρ⌋₊ : ℚ) : ℝ) ρ := by");
write(F, "  have hlo : ((⌊10 * ρ⌋₊ : ℕ) : ℝ) ≤ 10 * ρ := Nat.floor_le (by linarith)");
write(F, "  have hhi : 10 * ρ < ((⌊10 * ρ⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _");
write(F, "  have hj : ⌊10 * ρ⌋₊ < 28 := by");
write(F, "    have : ((⌊10 * ρ⌋₊ : ℕ) : ℝ) < 28 := by linarith");
write(F, "    exact_mod_cast this");
write(F, "  generalize ⌊10 * ρ⌋₊ = j at hlo hhi hj ⊢");
write(F, "  interval_cases j <;> push_cast at hlo hhi");
for(j = 0, 27, write(F, "  · exact drift_cell", j, " ρ (by linarith) (by linarith)"));
write(F, "\nend RegretKappa.LowerSharp");
}
quit
