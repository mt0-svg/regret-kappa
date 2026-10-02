# neg_raise.sage: negative control of run.sh. An error after a passing check: the run must be rejected.
load("lib.sage")
check("true claim", RB(1) < RB(2))
bisect_root(lambda t: t ^ 2 + 1, 0, 1, QQ(1) / 1000)
finish()
