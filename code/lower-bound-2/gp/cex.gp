\\ Constructed counterexamples for the drift certificate (Lemma 3.1 (b)): one table entry changed so that
\\ the drift falls below 1 on part of its cell (float scan first, to show the counterexample is genuine),
\\ then the certificate of drift.gp must answer FAIL. Usage: gp -q cex.gp CASE, CASE = 1 or 2 (read from env CEX).
c = eval(getenv("CEX"));
TAB = [6242, 6180, 6058, 5879, 5648, 5373, 5060, 4718, 4355, 3980, 3601, 3226, 2861, 2513, 2184, 1880, 1602, 1352, 1129, 934, 764, 620, 497, 395, 311, 242, 187, 142];
if (c == 1, TAB[17] = 1852; cell = 16, TAB[28] = 50; cell = 27);
dr(r, s) = 8 * exp((r^2 * (1 - s) + s) / 2) * cosh(r * sqrt(s * (1 - s))) - 8 * exp(r^2 / 2);
m = 10^9; at = 0; forstep (i = 0, 1000, 1, my(r = cell / 10 + i / 10000., d = dr(r, TAB[cell + 1] / 10000)); if (d < m, m = d; at = r));
print("counterexample ", c, ": cell ", cell, " s = ", TAB[cell + 1] / 10000., "; float min drift on the cell ", m, " at rho = ", at, " (below 1: ", if (m < 1, "yes", "no"), ")");
read("gp/drift.gp");
