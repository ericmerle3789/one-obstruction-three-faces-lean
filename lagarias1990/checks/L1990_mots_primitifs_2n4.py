"""Lagarias 1990: checks before the Lean proofs of (2.4), (2.5), Table 2.1 and Theorem 4.2 with 2n^4."""
from math import log2, log

TABLE = [2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335, 630, 1161, 2182, 4080, 7710, 14532, 27594, 52377]

def mobius(n):
    res, p, m = 1, 2, n
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    if m > 1:
        res = -res
    return res

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def irred_count(n):
    c = 0
    for x in range(2 ** n):
        v = [(x >> i) & 1 for i in range(n)]
        if all(v[i:] + v[:i] != v for i in range(1, n)):
            c += 1
    return c

print("P1-P3: n, #Irred(n), divisible, sum_{d|n} #Irred(d) == 2^n, Mobius, table")
ok1 = ok2 = ok3 = True
irr = {}
for n in range(1, 17):
    irr[n] = irred_count(n)
    div = irr[n] % n == 0
    s = sum(irr[d] for d in divisors(n))
    mob = sum(mobius(d) * 2 ** (n // d) for d in divisors(n))
    ok1 &= div
    ok2 &= (s == 2 ** n)
    ok3 &= (mob % n == 0 and mob // n == irr[n] // n == TABLE[n - 1])
    print(n, irr[n], div, s == 2 ** n, mob // n, TABLE[n - 1])
print("P1", ok1, "P2", ok2, "P3", ok3)

I = {}
for n in range(1, 21):
    I[n] = (2 ** n - sum(d * I[d] for d in divisors(n) if d < n)) // n
rec = [I[n] for n in range(1, 21)]
print("P4 recursion == table:", rec == TABLE, sum(a == b for a, b in zip(rec, TABLE)), "/ 20")

bad = [n for n in range(1, 10001) if n * n * (n + 2) ** 2 + n > 2 * n ** 4]
print("P5 failures of n^2(n+2)^2+n <= 2n^4 for n <= 10^4:", bad)

n6 = min(n for n in range(1, 200) if 2 * n ** 4 < 2 ** n)
print("P6 smallest n with 2n^4 < 2^n:", n6)

phi = log(2) / log(3)
H = -phi * log2(phi) - (1 - phi) * log2(1 - phi)
ac = (1 - H) / (2 - H)
print("H(phi) = %.7f, alpha_c = %.7f" % (H, ac))

def exists_M(n):
    lo, hi = 2 * n ** 4, 2 ** (ac * n)
    M = lo + 1
    while M <= hi:
        if M % 2 and M % 3:
            return True
        M += 1
    return False

n7 = next(n for n in range(1, 5000) if exists_M(n))
print("P7 smallest n with an M coprime to 6, 2n^4 < M <= 2^(alpha_c n):", n7)
