\\ The 22 rational pieces of Lemma 3.11 of the paper, with the rounded values of the Lean proof.
\\ Piece i (i = 1..22) is rho in [(i-1)/11, i/11]. With s2 = 1.4142136 >= sqrt 2:
\\   q_i >= q((i-1)/11) = m2((i-1)/11) - ((i-1)/11)^2 and x_i >= m2(i/11), both rounded up to 1e-6,
\\   and the bound q_i * (gpN(30, x_i) + tailN(30, x_i)) <= 2.7053 in exact rationals, with
\\   E = 0.6065306598 >= e^{-1/2} and K = 0.2798869 >= K_0 (Gamma units).
\\ Run: gp -q pieces_lean.gp > out/pieces_lean.txt
s2 = 14142136/10^7;
E = 6065306598/10^10; K = 2798869/10^7;
kk(m) = if(m == 0, 0, m == 1, 1, 1 + 2*(m-1)*kk(m-1));
GamC(n) = if(n == 1, 2*E + 4*K, 2*E*(kk(n) + 2*kk(n-1)));
gpN(N, x) = sum(n = 0, N-1, (n+1)*GamC(n+1)*x^n/(2*n+2)!);
tailN(N, x) = 2*x^N/((N+1)!*(1 - x/(N+2)));
m2up(r) = if(r^2 <= 1/2, 1 + r^2, r^2/3 + 2*s2*r/3 + 2/3);
up6(v) = ceil(v*10^6)/10^6;
worst = 0;
for(i = 1, 22, a = (i-1)/11; b = i/11; \
  q = up6(m2up(a) - a^2); x = up6(m2up(b)); \
  v = q*(gpN(30, x) + tailN(30, x)); worst = max(worst, v); \
  printf("piece %2d: a = %s, b = %s, q = %s, x = %s, bound = %.7f, margin = %.7f\n", i, a, b, q, x, v, 2.7053 - v));
printf("max bound = %.7f (needs <= 2.7053), max x = %s (needs < 32)\n", worst, up6(m2up(2)));
\\ sanity: the rounded q and x dominate the exact ones with sqrt 2
for(i = 1, 22, a = (i-1)/11; b = i/11; \
  qe = if(a^2 <= 1/2, 1, -2*a^2/3 + 2*sqrt(2)*a/3 + 2/3); xe = if(b^2 <= 1/2, 1 + b^2, b^2/3 + 2*sqrt(2)*b/3 + 2/3); \
  if(up6(m2up(a) - a^2) < qe || up6(m2up(b)) < xe, print("ROUNDING FAILS at ", i)));
print("DONE");
quit
