"""Continued fraction of theta = log 3 / log 2 (mpmath, 600 digits): convergents p/q; the loop stops at the first
q > 10^100, which is qBr' (101 digits); the convergent before it is pBr/qBr.
Numerical only. Lean does not use that these are convergents; it re-certifies what it uses: pBr' qBr - pBr qBr' = 1
and 2^334 <= qBr' by exact integer computation (decide +kernel), the two signs and |pBr log 2 - qBr log 3| >= 10^(-101)
from rational enclosures of log 2 and log 3.
Prints pBr, qBr, pBr', qBr' of Logs23/Logs23_Enonces.lean."""
import mpmath as mp
mp.mp.dps = 600
th = mp.log(3) / mp.log(2)
x = th; a = []
p0, q0, p1, q1 = 1, 0, int(mp.floor(th)), 1
a.append(p1); x = 1 / (x - p1)
convs = [(p1, q1)]
while q1 <= 10 ** 100:
    ai = int(mp.floor(x)); a.append(ai); x = 1 / (x - ai)
    p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
    convs.append((p1, q1))
print("number of partial quotients:", len(a))
print("partial quotients a_0..a_n:", a)
print("max partial quotient:", max(a[1:]))
(p, q), (pp, qq) = convs[-2], convs[-1]
print("last two convergents: q has", len(str(q)), "digits; q' has", len(str(qq)), "digits")
print("p'q - pq' =", pp * q - p * qq)
e1, e2 = q * th - p, qq * th - pp
print("q theta - p =", mp.nstr(e1, 8), "; q' theta - p' =", mp.nstr(e2, 8), "; opposite signs:", e1 * e2 < 0)
print("log10|q theta - p| =", mp.nstr(mp.log10(abs(e1)), 8))
print("first convergents (p/q):", convs[:16])
print("digits of the last four denominators:", [len(str(d)) for _, d in convs[-4:]])
print("pBr  =", p)
print("qBr  =", q)
print("pBr' =", pp)
print("qBr' =", qq)
