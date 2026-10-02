\\ Theorem 4.1 of the paper (Theorem LB in the outputs) and its proof: the explicit bound B(T), the threshold
\\ T0, the side conditions (C1)-(C3), the simplified form, and a comparison with the dynamic
\\ program values W_T(0) (a dynamic program not part of the paper or of this repository; the proof does not use them).
default(realprecision, 120);
A = 2; EZ2 = A^2*(1/3 - 2/Pi^2); J = Pi^2/A^2; c0 = 1 + EZ2 - log(A^2/(4*Pi^2)); c1 = c0 - 1/2 + (J - 2)/(Pi^2*exp(2));
j0(T) = ceil(log(3*log(T)));
Lev(T) = 2*log(T/(20*exp(1)*j0(T)));
aplus(L) = sqrt(L) + sqrt(5/8)*exp(-L/4);
\\ G = sup of g over the states reachable before and at the hitting time (Lemma 3.3)
Gb(L) = 8*max(exp(aplus(L)^2/2), exp((38/10)^2/2));
T1(T) = floor(T/2);
kmin(T) = T - T1(T);
B0(T) = my(L = Lev(T), a = sqrt(L), k = kmin(T)); L + log(k/(a + A)^2) - c1 - log(k)/(2*k) - 1/k;
Bfull(T) = (1 - exp(-j0(T)))*B0(T);
Bsimple(T) = 3*log(T) - log(log(T)) - 2*log(log(log(T)) + 21/10) - 146/10;
\\ side conditions, evaluated exactly at T
C1(T) = Lev(T) >= 29/2;
C2(T) = my(L = Lev(T), G = Gb(L), n = ceil(exp(1)*G)); j0(T)*n <= T1(T) - 1;
C3(T) = kmin(T) >= Pi^2*exp(2)*(aplus(Lev(T)) + A)^2;
\\ the increasing lower bound of L used for T >= T0 (j0 <= log(3 log T) + 1)
Llow(T) = 2*log(T) - 2*log(20*exp(1)) - 2*log(log(3*log(T)) + 1);
{
  printf("constants: c0 = %.6f, c1 = %.6f, E Z^2 = %.6f, log(1.1) = %.6f\n", c0, c1, EZ2, log(11/10));
  my(eps(L) = sqrt(5*L/8)*exp(-L/4) + (5/16)*exp(-L/2));
  printf("eps_L at L = 14.5: %.6f (<= log 1.1 = %.6f: %d); eps_L decreasing for L >= 2\n", eps(29/2), log(11/10), eps(29/2) <= log(11/10));
}
\\ T0: smallest T with Llow(T) >= 14.5 (Llow is increasing for T >= 3)
{my(lo = 10^3, hi = 10^8);
  while(hi - lo > 1, my(mid = (lo + hi)\2); if(Llow(mid) >= 29/2, hi = mid, lo = mid));
  T0 = hi;}
{
  printf("T0 = %d (smallest T with 2 log T - 2 log(20 e) - 2 log(log(3 log T) + 1) >= 14.5)\n", T0);
  printf("at T0: j0 = %d, L = %.6f, Llow = %.6f, C1 %d, C2 %d, C3 %d\n", j0(T0), Lev(T0), Llow(T0), C1(T0), C2(T0), C3(T0));
  printf("C3 margin function T/2 - pi^2 e^2 (sqrt(2 log T) + 2.03)^2 at T0: %.3f; sqrt(5/8) exp(-14.5/4) = %.5f\n", T0/2 - Pi^2*exp(2)*(sqrt(2*log(T0)) + 203/100)^2, sqrt(5/8)*exp(-29/8));
  \\ scan: side conditions and B >= Bsimple on a geometric grid of T in [T0, 1e30]
  my(ok = 1, mn = 10^9, argm);
  forstep(e = log(T0)/log(10), 30, 1/50,
    my(T = floor(10^e));
    if(T < T0, T = T0);
    if(!(C1(T) && C2(T) && C3(T)), ok = 0; printf("condition fails at T = %d\n", T));
    my(d = Bfull(T) - Bsimple(T)); if(d < mn, mn = d; argm = T));
  printf("scan T in [T0, 1e30], 50 points per decade: conditions %s; min of B(T) - Bsimple(T) = %.6f at T = %.4g\n",
         if(ok, "all hold", "FAIL"), mn, argm*1.);
  \\ also every jump point of j0 (T = exp(e^j / 3)) and its neighbours
  for(j = 4, 6, my(Tj = floor(exp(exp(j)/3)));
    if(Tj >= T0, foreach([Tj - 1, Tj, Tj + 1], T,
      if(!(C1(T) && C2(T) && C3(T)), printf("condition fails at jump T = %d\n", T));
      my(d = Bfull(T) - Bsimple(T)); if(d < 0, printf("B < Bsimple at jump T = %d\n", T)))));
  print("jump points of j0 checked (j = 4..6, T up to 1e58)");
}
\\ the forms 3 log T - 2 log log T - 15.2 and 3 log T - 8 log log T: v - 2 log(v + 2.1) is increasing for v > -0.1,
\\ so it suffices to check at v = log log T0; 6 log log T >= 15.2 likewise
{
  my(v = log(log(T0)));
  printf("at T0: log log T0 = %.6f, v - 2 log(v + 2.1) = %.6f (>= -0.6: %d), 6 log log T0 = %.6f (>= 15.2: %d)\n",
         v, v - 2*log(v + 21/10), v - 2*log(v + 21/10) >= -6/10, 6*v, 6*v >= 152/10);
}
\\ table of the bound against the dynamic program
{
  my(dp = [[10^3, 12.991100627], [10^4, 19.491657618], [10^5, 26.243932117], [316228, 29.662458245], [10^6, 33.095193243]]);
  print("T\tj0\tL\tB(T)\tBsimple(T)\tW_T(0) (DP)\tW - B\tconditions");
  for(i = 1, #dp, my(T = dp[i][1]);
    printf("%d\t%d\t%.4f\t%.4f\t%.4f\t%.4f\t%.4f\t%s\n", T, j0(T), Lev(T), Bfull(T), Bsimple(T), dp[i][2], dp[i][2] - Bfull(T),
           if(T >= T0, "T >= T0", "T < T0 (bound not claimed)")));
  foreach([10^7, 10^8, 10^10, 10^15, 10^20], T,
    printf("%.0e\t%d\t%.4f\t%.4f\t%.4f\t-\t-\t-\n", T*1., j0(T), Lev(T), Bfull(T), Bsimple(T)));
  printf("B(T)/log T at T = 1e6, 1e10, 1e20, 1e50, 1e100: %.4f %.4f %.4f %.4f %.4f\n",
         Bfull(10^6)/log(10^6), Bfull(10^10)/log(10^10), Bfull(10^20)/log(10^20), Bfull(10^50)/log(10^50), Bfull(10^100)/log(10^100));
}
quit
