\\ Lemma 3.11 of the paper, item (3) of Computation 3.13, with rational breakpoints as in the Lean proof:
\\ pieces [a, b] of [0, 2], bound max(q(a), 0) (g'_N(m2(b)) + tail_N(m2(b))),
\\ with sqrt 2 <= S2 rational in q and m2, e^{-1/2} <= Ep, K_0 <= Kp.
\\ Run: gp -q pieces.gp > out/pieces.txt
default(realprecision, 50);
Ep = 6065306598/10^10; Kp = 2798869/10^7; S2 = 14142136/10^7;
k = vector(40); k[1] = 1; for(m = 2, 40, k[m] = 1 + 2*(m-1)*k[m-1]);
Gam(n) = if(n == 1, 2*Ep + 4*Kp, 2*Ep*(k[n] + 2*k[n-1]));
gpN(x, N) = sum(n = 1, N, n*Gam(n)*x^(n-1)/(2*n)!);
tl(x, N) = 2*x^N/((N+1)!*(1 - x/(N+2)));
m2(r) = if(r^2 <= 1/2, 1 + r^2, r^2/3 + 2*S2*r/3 + 2/3);
q(r) = m2(r) - r^2;
print("sqrt 2 <= S2: ", sqrt(2) <= S2);
run(bp, N) = my(mx = 0, imx = 0); for(i = 1, #bp - 1, my(a = bp[i], b = bp[i+1], v = max(q(a), 0)*(gpN(m2(b), N) + tl(m2(b), N))); if(v > mx, mx = v; imx = i)); [mx*1., imx];
for(n = 20, 26, my(bp = vector(n + 1, i, 2*(i-1)/n)); print("uniform pieces of [0,2], n = ", n, ": max bound, piece = ", run(bp, 30)));
bp = vector(21, i, (i-1)/10);
print("pieces of width 1/10, N = 30:");
for(i = 1, 20, my(a = bp[i], b = bp[i+1]); print("  [", a, ", ", b, "]  q(a)+ = ", q(a)*1., "  m2(b)+ = ", m2(b)*1., "  bound = ", (max(q(a), 0)*(gpN(m2(b), 30) + tl(m2(b), 30)))*1.));
print("q(2) = ", q(2)*1., " (negative: psi <= 0 beyond 2)");
for(N = 12, 20, print("width 1/10: N = ", N, "  max bound ", run(bp, N)));
quit
