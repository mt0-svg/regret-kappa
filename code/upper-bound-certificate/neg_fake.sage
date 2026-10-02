# neg_fake.sage: negative control of run.sh. A faked pass: exit status 0 and a final
# "RESULT: ALL ... PASSED" line, but a FAIL line before it. The run must be rejected.
print("PASS true claim")
print("FAIL false claim")
print("RESULT: ALL 2 CHECKS PASSED")
