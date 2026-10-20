"""Details of Table 3.1 rows k=35 and k=73 (Lagarias 1990). Deterministic."""
from math import gcd, log2


def Tk(k, n):
    return (3 * n + k) // 2 if n % 2 else n // 2


def cycle(k, n0, cap=10**6):
    c, n = [n0], Tk(k, n0)
    while n != n0 and len(c) < cap:
        if n in c:
            return None
        c.append(n)
        n = Tk(k, n)
    return c if n == n0 else None


for k, n0 in ((35, 7), (35, 13), (73, 5), (73, 19)):
    c = cycle(k, n0)
    print("k=%d n0=%d: cycle=%s length=%s min=%s gcd(n0,k)=%d primitive=%s" % (
        k, n0, (c if c and len(c) <= 12 else "..."), len(c) if c else None, min(c) if c else None,
        gcd(n0, k), bool(c) and all(gcd(a, k) == 1 for a in c)))
print("T_5 cycle of 1 times 7:", [7 * a for a in cycle(5, 1)])
seen, cycles73 = set(), []
for n0 in range(1, 400):
    if gcd(n0, 73) == 1 and n0 not in seen:
        c = cycle(73, n0)
        if c:
            seen |= set(c)
            cycles73.append((min(c), len(c)))
print("primitive cycles of T_73 meeting [1,400) (min, length):", sorted(set(cycles73)))
phi = 1 / log2(3)
H = -phi * log2(phi) - (1 - phi) * log2(1 - phi)
print("H=%.8f alpha_c=%.8f alpha_c(H=0.949955)=%.8f beta_c=%.8f" % (
    H, (1 - H) / (2 - H), (1 - 0.949955) / (2 - 0.949955), 2 - H))
