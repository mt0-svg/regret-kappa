\\ Rational enclosure of K_0 = int_1^oo e^{-t^2/2}/t dt = E_1(1/2)/2 for the Lean proof:
\\ R = sqrt 32, int_1^R expNegT(m)(t^2/2)/t dt = log R + S(m), tail <= e^{-16}/32.
\\ Run: gp -q k0.gp > out/k0.txt
default(realprecision, 60);
S(m) = sum(k = 0, m - 2, (-1)^(k+1)*(32^(k+1) - 1)/(2^(k+1)*(k+1)!*(2*(k+1))));
K0 = eint1(1/2)/2;
l2lo = 6931471803/10^10; l2hi = 6931471808/10^10;
e16 = sum(k = 0, 19, 16^k/k!);
print("K_0 = ", K0);
print("exp(16) >= ", e16*1., "  so e^{-16}/32 <= ", 1/(32*e16)*1.);
for(m = 50, 60, my(lo, hi); \
  if(m % 2 == 0, lo = 5/2*l2lo + S(m); print("m = ", m, " (lower) lower bound = ", lo*1., "  margin to 0.2798867: ", (lo - 2798867/10^7)*1.)); \
  if(m % 2 == 1, hi = 5/2*l2hi + S(m) + 1/(32*e16); print("m = ", m, " (upper) upper bound = ", hi*1., "  margin to 0.2798869: ", (2798869/10^7 - hi)*1.)));
quit
