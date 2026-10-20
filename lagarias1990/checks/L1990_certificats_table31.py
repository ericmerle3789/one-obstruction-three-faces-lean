"""Non-periodicity certificates (j0, L) for Table 3.1 rows k=35 and k=73 (Lagarias 1990). Deterministic."""
from math import gcd


def Tk(k, n):
    return (3 * n + k) // 2 if n % 2 else n // 2


for k, n0 in ((35, 13), (73, 5)):
    for n in range(1, n0):
        if gcd(n, k) != 1:
            continue
        seen, orb, x = {}, [], n
        while x not in seen:
            seen[x] = len(orb)
            orb.append(x)
            x = Tk(k, x)
        j0, L = seen[x], len(orb) - seen[x]
        assert n not in orb[j0:], (k, n)
        print("k=%d n=%d j0=%d L=%d periodic=%s" % (k, n, j0, L, j0 == 0))
