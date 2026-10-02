\\ Order scan of the drift certificate (the paper, Lemma 4.3 (b)): for each N, whether bisection
\\ certifies the 28 cells (to depth 30), the number of leaves and the smallest margin; then the two
\\ corrupted tables of Computation 4.4 (s_16 = 0.1852, s_27 = 0.0050), which must fail.
read("drift_tree_lib.gp");
scan(N, tb) =
{
  my(tot = 0, mm = 10^9, mj = -1, ok = 1);
  iferr(for(j = 0, 27, my(t = tree(j/10, (j+1)/10, tb[j+1], N, 0)); tot += t[2];
      if(t[4] < mm, mm = t[4]; mj = j)),
    E, ok = 0; printf("  failure: %s\n", E));
  printf("N = %d: certified %d, leaves %d, smallest margin %.4e in cell %d\n", N, ok, tot, mm * 1., mj);
}
{
  print("the paper's table");
  foreach([8, 10, 12, 14, 16, 20, 30, 40], N, scan(N, tab));
  my(t16 = tab, t27 = tab);
  t16[17] = 1852/10000; t27[28] = 50/10000;
  print("corrupted s_16 = 0.1852"); foreach([14, 40], N, scan(N, t16));
  print("corrupted s_27 = 0.0050"); foreach([14, 40], N, scan(N, t27));
}
quit
