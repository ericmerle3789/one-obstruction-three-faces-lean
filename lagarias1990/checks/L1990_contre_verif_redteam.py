"""Counter-check of three Red Team remarks on the Lagarias 1990 formalisation. Deterministic."""
from itertools import product


def N(v):
    return sum(v[j] * 2**j * 3**sum(v[j + 1:]) for j in range(len(v)))


fails = []
maxheads = 0
for n in range(1, 13):
    words = list(product((0, 1), repeat=n))
    nums = [N(list(v)) for v in words]
    for M in range(2, min(2000, 3**n)):
        if M % 3 == 0:
            continue
        m = 0
        while 3**(m + 1) <= M and m + 1 <= n:
            m += 1
        cnt = {}
        for a in nums:
            cnt[a % M] = cnt.get(a % M, 0) + 1
        if max(cnt.values()) > m * 2**(n - m):
            fails.append((n, M, m))
        if m >= 1 and n <= 9:
            tails = {}
            for v in words:
                key = (v[m:], N(list(v)) % M)
                tails[key] = tails.get(key, 0) + 1
            maxheads = max(maxheads, max(tails.values()) - max(1, m) if tails else 0)
print("R1 failures of m*2^(n-m):", len(fails), "| all with m == 0:", all(f[2] == 0 for f in fails),
      "| M values:", sorted({f[1] for f in fails}))
print("R2 max over (tail, class) of #heads minus max(1,m) (n<=9):", maxheads)


def T(x):
    return (3 * x + 1) // 2 if x % 2 else x // 2


for x0 in (-5, -17):
    c, x = [x0], T(x0)
    while x != x0:
        c.append(x)
        x = T(x)
    print("R3 cycle of %d: length %d, min %d, min %% 6 = %d" % (x0, len(c), min(c), min(c) % 6))
