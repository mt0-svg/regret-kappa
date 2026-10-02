\\ Phase 2 (Lemma 4.11 of the paper, Lemma P2 in the outputs): tests of the van Trees lower bound of the future excess.
\\ Parameters: prior half-width A = 2, cap nu_m^2 = 1/2, J = pi^2/A^2, E Z^2 = A^2 (1/3 - 2/pi^2).
\\ For a state rho and k rounds left, r = |rho| + A, nu_i^2 = nu_m^2 i/k, eps_i^2 = nu_i^2/r^2,
\\   w_0 = J, w_i = w_{i-1} + eps_i^2/(1 - nu_i^2),
\\   vT(rho,k) = sum_i eps_i^2/w_{i-1} - E Z^2 + (1 + X_k)/w_k, X_k = sum_i eps_i^2
\\     (the van Trees sum of Lemma 4.3: the predictions, then the comparator term V_T (theta* - S_T/V_T)^2)
\\   Phi0(rho,k) = log(k/r^2) - c1 - log(k)/(2k) - 1/k, c1 = 1 + E Z^2 - log(A^2/(4 pi^2)) - 1/2 + (J-2)/(pi^2 e^2)
\\ Claims checked: vT >= Phi0 when k >= pi^2 e^2 r^2 (the closed form is a valid lower bound of
\\ the sum), and W_k(rho) - rho^2 >= vT at the points of the dynamic program tables
\\ (a dynamic program for the value W_k of the game, not part of the paper or of this repository; our adversary
\\ is one strategy of the game, so its guaranteed excess cannot exceed the game value).
default(realprecision, 38);
A = 2; num2 = 1/2; J = Pi^2/A^2; EZ2 = A^2*(1/3 - 2/Pi^2);
c0 = -log(A^2/(4*Pi^2)) + 1 + EZ2; c1 = c0 - 1/2 + (J - 2)/(Pi^2*exp(2));
vT(rho, k) =
{
  my(r = abs(rho) + A, w = J, tot = 0., X = 0.);
  for(i = 1, k,
    my(nu2 = num2*i/k, e2 = nu2/r^2);
    tot += e2/w; X += e2;
    w += e2/(1 - nu2));
  tot - EZ2 + (1 + X)/w;
}
Phi0(rho, k) = my(r = abs(rho) + A); log(k/r^2) - c1 - log(k)/(2*k) - 1/k;
printf("constants: A = %d, J = %.6f, E Z^2 = %.6f, c0 = -log(A^2/(4 pi^2)) + 1 + E Z^2 = %.6f, c1 = c0 - 1/2 + (J-2)/(pi^2 e^2) = %.6f\n", A, J, EZ2, c0, c1);
printf("validity threshold of Phi0: k >= pi^2 e^2 r^2 = %.4f r^2\n", Pi^2*exp(2));

\\ W_k(rho) - rho^2 from the dynamic program tables (strategy sections), k = 1e5 and 1e6
{tabW = [
 [100000, 0.0, 26.243932], [100000, 1.0, 25.243962], [100000, 2.0, 22.244544], [100000, 3.0, 17.254004],
 [100000, 4.0, 10.523336], [100000, 5.0, 6.213967], [100000, 6.0, 5.665321], [100000, 8.0, 5.087667],
 [100000, 10.0, 4.654667], [100000, 12.0, 4.308650], [100000, 17.8314, 3.580469], [100000, 26.4965, 2.888087],
 [100000, 39.3724, 2.241517], [100000, 58.5053, 1.657028], [100000, 86.9358, 1.153139], [100000, 129.1820, 0.744247],
 [100000, 191.9576, 0.442031], [100000, 233.9952, 0.329133],
 [1000000, 0.0, 33.095193], [1000000, 1.0, 32.095196], [1000000, 2.0, 29.095255], [1000000, 3.0, 24.096212],
 [1000000, 4.0, 17.125204], [1000000, 5.0, 9.586649], [1000000, 6.0, 7.927020], [1000000, 8.0, 7.323731],
 [1000000, 10.0, 6.873505], [1000000, 12.0, 6.510541], [1000000, 17.8314, 5.733877], [1000000, 26.4965, 4.972367],
 [1000000, 39.3724, 4.228703], [1000000, 58.5053, 3.509163], [1000000, 86.9358, 2.823512], [1000000, 129.1820, 2.184229],
 [1000000, 191.9576, 1.606211], [1000000, 233.9952, 1.346756]];}
{
  print("k\trho\tW-rho^2(DP)\tvT\tPhi0\tvalid(k>=pi^2e^2r^2)\tDP-vT\tvT-Phi0");
  my(okDP = 1, okPhi = 1);
  for(i = 1, #tabW,
    my(k = tabW[i][1], rho = tabW[i][2], w = tabW[i][3], v = vT(rho, k), p = Phi0(rho, k), r = abs(rho) + A,
       valid = (k >= Pi^2*exp(2)*r^2));
    if(w < v, okDP = 0);
    if(valid && v < p, okPhi = 0);
    printf("%d\t%.4f\t%.6f\t%.6f\t%.6f\t%d\t%.4f\t%.4f\n", k, rho, w, v, p, valid, w - v, v - p));
  printf("DP >= vT at every table point: %s\n", if(okDP, "PASS", "FAIL"));
  printf("vT >= Phi0 at every valid table point: %s\n", if(okPhi, "PASS", "FAIL"));
}
\\ vT - Phi0 over a grid of (rho, k) in the validity range (the closed form must be below the sum)
{
  my(mn = 10^9, arg);
  foreach([10^3, 10^4, 10^5], k,
    forstep(rho = 0, 40, 1/4,
      my(r = rho + A);
      if(k >= Pi^2*exp(2)*r^2, my(d = vT(rho, k) - Phi0(rho, k)); if(d < mn, mn = d; arg = [k, rho]))));
  printf("min over the grid k in {1e3,1e4,1e5}, rho in [0,40] step 1/4 (valid points) of vT - Phi0: %.6f at k = %d, rho = %.2f\n", mn, arg[1], arg[2]);
}
quit
