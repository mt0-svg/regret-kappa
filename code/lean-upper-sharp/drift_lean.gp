\\ The cells of the drift certificate (the paper, Lemma B.1 (b) and Computation B.2): for each
\\ cell j and the order N given in the
\\ variable NN (default 14), the bisection tree of drift_tree_lib.gp as a natural number (preorder
\\ bits from the least significant one, 1 = split, 0 = leaf), and a draft Lean theorem per
\\ cell. Writes the table to out/drift_codes.txt and the drafts to out/drift_cells.lean.part; the module
\\ RegretKappa/LowerSharp/DriftCells.lean, with the same trees, is written by drift_cells.gp.
read("drift_tree_lib.gp");
bitsToNat(b) = my(v = Vec(b), c = 0); for(i = 1, #v, if(v[i] == "1", c += 2^(i-1))); c;
NN = 14;
{
my(F = "out/drift_cells.lean.part", G = "out/drift_codes.txt", tot = 0);
system(Str("rm -f ", F, " ", G));
write(G, "N ", NN, ": cell, s_j, leaves, depth, smallest margin, code");
write(F, "/-- The move table of the paper (Section 4.2): `s_j` on the cell `[j/10, (j+1)/10)`. -/");
write(F, "def stab : ℕ → ℚ");
for(j = 0, 27, write(F, "  | ", j, " => ", tab[j+1]));
write(F, "  | _ => 0");
for(j = 0, 27,
  my(t = tree(j/10, (j+1)/10, tab[j+1], NN, 0), c = bitsToNat(t[1]));
  tot += t[2];
  write(G, j, " ", tab[j+1], " ", t[2], " ", t[3], " ", t[4] * 1., " ", c);
  write(F, "");
  write(F, "theorem cell", j, " : (check ", NN, " (", tab[j+1], ") 8 (", j, " / 10) (", j + 1, " / 10) ", c, ").1 = true := by decide +kernel");
  write(F, "");
  write(F, "theorem drift_cell", j, " (ρ : ℝ) (h1 : (", j, " : ℝ) / 10 ≤ ρ) (h2 : ρ ≤ (", j + 1, " : ℝ) / 10) :");
  write(F, "    0 ≤ driftGap ((stab ", j, " : ℚ) : ℝ) ρ :=");
  write(F, "  check_sound ", NN, " (by norm_num [stab]) (by norm_num [stab]) 8 _ _ _ cell", j, " (by norm_num) (by norm_num)");
  write(F, "    (by norm_num) ρ (by push_cast; linarith) (by push_cast; linarith)"));
write(G, "total leaves ", tot);
}
quit
