# neg_fail.sage: negative control of run.sh. One false check: the run must be rejected.
load("lib.sage")
check("true claim", RB(1) < RB(2))
check("false claim 2 < 1", RB(2) < RB(1))
finish()
