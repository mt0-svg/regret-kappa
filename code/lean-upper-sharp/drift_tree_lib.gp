\\ Bisection trees of the drift certificate of the paper, Lemma 4.3 (b) (copy of the method of
\\ code/lower-bound/drift_check.gp, same table, same bound): for each cell j and each N in Ns, the
\\ preorder bit string of the bisection tree (1 = split, 0 = certified leaf), its number of leaves,
\\ its depth and its smallest margin with the leaf where it occurs. Exact rational arithmetic.
tab = vector(28, j, round(5/8 * exp(-((j-1)/10 + 1/20)^2 / 2) * 10^4) / 10^4);
explo(q, N) = sum(n = 0, N, q^n / n!);
expup(q, N) = if(q >= N + 2, error("q too large"), sum(n = 0, N, q^n / n!) + q^(N+1) / (N+1)! * (N+2) / (N+2-q));
coshlo(y, N) = sum(n = 0, N, y^n / (2*n)!);
cert(lo, hi, s, N) = 8 * (explo((lo^2 * (1-s) + s) / 2, N) * coshlo(lo^2 * s * (1-s), N) - expup(hi^2 / 2, N)) - 1;
\\ returns [bits, leaves, depth, minmargin, lo_at_min, hi_at_min]
tree(lo, hi, s, N, d) =
{
  my(c = cert(lo, hi, s, N), m = (lo + hi) / 2, A, B);
  if(c >= 0, return(["0", 1, d, c, lo, hi]));
  if(d > 30, error("certificate failed near ", lo * 1.));
  A = tree(lo, m, s, N, d + 1); B = tree(m, hi, s, N, d + 1);
  [concat(concat("1", A[1]), B[1]), A[2] + B[2], max(A[3], B[3]), if(A[4] <= B[4], A[4], B[4]),
   if(A[4] <= B[4], A[5], B[5]), if(A[4] <= B[4], A[6], B[6])];
}
