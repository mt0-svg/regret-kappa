# Negative controls: corrupted inputs fed to the same check functions as the main scripts.
# Each CHECK below passes when the corrupted input is rejected; the failing values are printed.
# Run from this directory: sage negative_controls.sage

load("common.sage")
load("drift_lib.sage")
load("rational_lib.sage")
load("lb_lib.sage")

C = Checker("negative_controls")
K8 = R(K_G)
c1 = c1_of(J_prior(), EZ2_prior())


def moves_with(j, digits):
    m = list(MOVES)
    m[j] = QQ(digits) / 10000
    return m


def mvf_cell(j, moves, K):
    s = R(moves[j])
    return certify_trisect(QQ(j) / 10, QQ(j + 1) / 10, lambda a, b: drift_mean_value(a, b, s, R(K)))


print("== NC1: move s_16 = 0.1602 replaced by 0.1000")
mv = moves_with(16, 1000)
ok_r, leaves, info = certify_cell(16, mv)
print("rational certificate, cell 16: %s; piece [%s, %s] still negative at depth 20, bound there %.6f" %
      ("certified" if ok_r else "NOT certified", info[0], info[1], float(bound(info[0], info[1], mv[16]))) if not ok_r
      else "rational certificate, cell 16: certified")
ok_m, _, info_m = mvf_cell(16, mv, K_G)
print("Arb mean value form, cell 16: %s" % ("certified" if ok_m else "NOT certified, piece [%s, %s]" % info_m))
ce = find_counterexample(QQ(16) / 10, QQ(17) / 10, lambda r: drift_direct(r, R(mv[16]), K8), 200)
print("counterexample: D(%s) <= %.6f (drift 8 h_s - g = %.6f < 1)" % (ce[0], float(ce[1]), float(ce[1]) + 1))
bad = [r for r in table_rounding([QQ(x * 10000) for x in mv]) if r[0] != r[1]]
print("table rounding: %s" % ", ".join("table %d, rounding %d" % (r[0], r[1]) for r in bad))
C.check("NC1 rejected by the rational certificate", not ok_r)
C.check("NC1 rejected by the Arb mean value form", not ok_m)
C.check("NC1 refuted: a rational point with D certainly < 0", ce is not None and ce[1] < 0)
C.check("NC1 rejected by the table rounding check", len(bad) == 1)

print("== NC2: move s_17 = 0.1352 replaced by 0.1353 (a typo in the last digit)")
mv2 = moves_with(17, 1353)
bad2 = [(j, r) for j, r in enumerate(table_rounding([QQ(x * 10000) for x in mv2])) if r[0] != r[1]]
print("table rounding: " + ", ".join("cell %d: table %d, rounding %d (value %s)" % (j, r[0], r[1], r[2].mid().n(digits=8))
                                     for j, r in bad2))
ok2, _, _ = certify_cell(17, mv2)
print("rational certificate, cell 17 with 0.1353: %s (the drift has slack, only the table check sees it)" %
      ("certified" if ok2 else "NOT certified"))
C.check("NC2 rejected by the table rounding check", len(bad2) == 1 and bad2[0][0] == 17)

print("== NC3: constant K = 7 in g = K exp(rho^2/2) (the note: the least admissible K is 7.16)")
fails_r = [j for j in range(NCELLS) if not certify_cell(j, MOVES, K=7)[0]]
fails_m = [j for j in range(NCELLS) if not mvf_cell(j, MOVES, 7)[0]]
print("rational certificate fails on cells %s" % fails_r)
print("Arb mean value form fails on cells %s" % fails_m)
ce3 = find_counterexample(QQ(16) / 10, QQ(17) / 10, lambda r: drift_direct(r, R(MOVES[16]), R(7)), 200)
print("counterexample (cell 16): D_7(%s) <= %.6f" % (ce3[0], float(ce3[1])))
C.check("NC3 rejected by the rational certificate", len(fails_r) > 0)
C.check("NC3 rejected by the Arb mean value form", len(fails_m) > 0)
C.check("NC3 refuted: a rational point with D_7 certainly < 0", ce3 is not None and ce3[1] < 0)

print("== NC4: part (a) with corrupted constants")
for split, const, name in [(RHO_SPLIT, QQ(9) / 25, "12/25 -> 9/25"), (RHO_SPLIT, QQ(13) / 25, "12/25 -> 13/25"),
                           (QQ(2), QQ(12) / 25, "split 2.8 -> 2.0")]:
    cond = part_a_conditions(split, const)
    print("%s: phi decreasing %s, phi(split) = %.6f < const %s, 5/2 - (25/8) const >= 1 %s" %
          (name, cond[0], phi_ball(split).mid(), cond[1], cond[2]))
    C.check("NC4 (%s) rejected" % name, not all(cond))

print("== NC5: T_0 = 355713 replaced by 355712")
print("L_low(355712) = %.9f, L(355712) = %.6f" % (L_low(T0 - 1).mid(), L_of(T0 - 1).mid()))
C.check("NC5 rejected: L_low(T_0 - 1) < 14.5", L_low(T0 - 1) < R(QQ(145) / 10))

print("== NC6: constant 8.8 of Lemma 3.3 replaced by 8.5, and G = 10 exp(L/2) in (C2)")
print("eps_14.5 = %.6f against log(8.5/8) = %.6f" % (eps_L(QQ(145) / 10).mid(), R(QQ(85) / 80).log().mid()))
C.check("NC6 rejected: eps_14.5 > log(8.5/8)", eps_L(QQ(145) / 10) > R(QQ(85) / 80).log())
lhs = j0_of(T0) * (10 * E1 * (L_of(T0) / 2).exp() + 1)
print("(C2) with G = 10 exp(L/2) at T_0: j_0 (e G + 1) = %.2f against T_1 - 1 = %d" % (lhs.mid(), T0 // 2 - 1))
C.check("NC6 rejected: (C2) fails at T_0 with G = 10 exp(L/2)", not C2_holds(T0, Gfac=10))

print("== NC7: c_1 = 3.318633 replaced by its truncation 3.3186")
print("c_1 = %.9f" % c1.mid())
C.check("NC7 rejected: c_1 > 3.3186 (the stated value must be an upper rounding)", c1 > R(QQ(33186) / 10000))

print("== NC8: Phi_1 with c_1 lowered by 1/2 (vT - Phi_1 is about 0.50 at rho = 3.81, k = 10^6)")
d = vT_detail(QQ(381) / 100, 10 ** 6, steps=False)
ph = Phi1(QQ(381) / 100, 10 ** 6, c1 - R(1) / 2)
print("vT = %.6f, corrupted Phi_1 = %.6f" % (d["vT"].mid(), ph.mid()))
C.check("NC8 rejected: vT < Phi_1 with c_1 - 1/2", d["vT"] < ph)

print("== NC9: vT with J = 1 in place of pi^2/4 against the Bayes learner")
M = prior_moments(16)
rows = []
for rho, k in [(QQ(0), 2), (QQ(385) / 100, 6), (QQ(6), 12)]:
    bv, _ = bayes_value(rho, k, M)
    vw = vT_detail(rho, k, J=R(1), steps=False)["vT"]
    rows.append(bv < vw)
    print("rho = %s, k = %d: Bayes value %.6f, corrupted vT %.6f" % (rho, k, bv.mid(), vw.mid()))
C.check("NC9 rejected: corrupted vT exceeds the Bayes value at 3 points", all(rows))

print("== NC10: step (s4) of Lemma 4.3 outside its validity range (rho = 3.81, k = 50 < k_min = 2462)")
d = vT_detail(QQ(381) / 100, 50, steps=False)
lhs4 = (1 + d["X"]) / d["wk"]
rhs4 = R(1) / 2 - (J_prior() - 2) / (PI ** 2 * E1 ** 2)
print("(1 + X)/w_k = %.6f against 1/2 - (J - 2)/(pi^2 e^2) = %.6f" % (lhs4.mid(), rhs4.mid()))
C.check("NC10 rejected: (s4) fails at k = 50", lhs4 < rhs4)

print("== NC11: the constant 15.2 of the cleaner form replaced by 15.0")
v0 = R(T0).log().log()
hv0 = v0 - 2 * (v0 + R(QQ(21) / 10)).log()
print("14.6 - (log log T_0 - 2 log(log log T_0 + 2.1)) = %.6f against 15.0" % (R(QQ(146) / 10) - hv0).mid())
C.check("NC11 rejected: 14.6 + 0.5249 > 15.0", QQ(146) / 10 + QQ(5249) / 10000 > 15)
C.finish(19)
