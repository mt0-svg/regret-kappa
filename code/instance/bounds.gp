\\ The bounds of Theorem 1.1 at T = 10^6 and B = 1, and the sharper bounds b(T) of (4.1) and u(T) of
\\ Theorem 3.1 between them, printed after Theorem 1.1 of the paper. Evaluated with 100 significant digits;
\\ lower bounds rounded down and upper bounds rounded up to two decimals, so the printed inequalities hold.
default(realprecision, 100);
T = 10^6;
j0 = ceil(log(3*log(T)));
L = 2*log(T/(20*exp(1)*j0));
k0 = T - floor(T/2);
c1 = 1/2 + 4/3 - 8/Pi^2 + log(Pi^2) + (Pi^2/4 - 2)/(Pi^2*exp(2));
b = (1 - exp(-j0))*(L + log(k0/(sqrt(L) + 2)^2) - c1 - log(k0)/(2*k0) - 1/k0);
u = 2*log(exp(2) + (sqrt(T) + 1)*(3*T + 2*exp(-1/2))/sqrt(2*Pi));
lo = 3*log(T) - 2*log(log(T)) - 15.2;
hi = 3*log(T) + 37/100;
down(x) = floor(100*x)/100.;
up(x) = ceil(100*x)/100.;
f(x) = Strprintf("%.2f", x);
print("T = 10^6, j0 = ", j0, ", k0 = ", k0);
print("3 log T - 2 log log T - 15.2 >= ", f(down(lo)));
print("b(T) >= ", f(down(b)));
print("u(T) <= ", f(up(u)));
print("3 log T + 0.37 <= ", f(up(hi)));
quit
