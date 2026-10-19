#!/usr/bin/env python3
# run_131 — Merle's key on L-A12 (round 19, Macindoe, PR #9). Recorded in the lab as D040 (labtrace id=375,
# 2026-10-19; predictions frozen beforehand: run_131.predictions.md). Fresh code written from the text alone
# (LEDGER.md L-A12 in PR #9; cycles.md 12.6.1 and 12.8.7 at dff0a95); reads and imports nothing of Macindoe's.
# Every (S), (X), sandwich and divisibility decision in exact integers; mpmath at 1600 bits only for gamma, eta,
# Gamma', eps_p, p1 and the real brackets. Y_0 from the 12.6.1 definition, then Y_1..Y_p by the Terras dynamics
# itself (exact 2-adic valuations at every block, return to Y_0 checked), so the dictionary x_r = 2^{m_r} R_r/q - 1
# is tested, not assumed. Labels in the output are French: ECHEC = failure, controles = checks, graine = seed,
# fenetre = window, rabot = trim, bloc unite = unit block. Output: run_131_output.txt (96,119 checks, 0 failures).
# Runtime about 65 s. Body below unchanged.
"""D040 — clé Merle sur L-A12 (Macindoe, round 19, PR #9).

Code neuf, écrit depuis le texte seul (LEDGER.md L-A12 de la PR #9 ; cycles.md §12.6.1 et §12.8.7 à dff0a95).
N'importe et ne lit aucun script de Macindoe. Toute décision (S), (X), sandwich, divisibilités : entiers exacts.
mpmath (1600 bits) seulement pour γ, η, Γ′, ε_p, p₁, les crochets réels.

Parties : A configurations aléatoires (dictionnaire, sandwich, rabot, bloc unité, minimax de Rozier) ;
B Construction B sous (H0)+(H1′) et contrôle négatif ; C p₁ ; D fenêtre (Thm 12.8.7.4) ;
E exclusion du bloc unité (12.8.7.5) et constante 2,09 ; F canaris.
"""
import random
from fractions import Fraction
import mpmath as mp

mp.mp.prec = 1600
L = mp.log(3) / mp.log(2)
LAM = L / (L - 1) + mp.mpf(2) ** -20          # λ de 12.8.7.4
NCHK = [0, 0]


def check(cond, label):
    NCHK[0] += 1
    if not cond:
        NCHK[1] += 1
        print("  ECHEC :", label)
    return cond


def D(x):                                      # δ(x) = −log₂(1 − 2^{−x}) ; involution
    return -mp.log(1 - mp.mpf(2) ** (-x), 2)


def eps(p):
    return (L - 1) / (L ** p - 1)


def gam(n, K):                                 # γ = K − log₂(2^K − 3^n) = D(K − nL)
    return D(K - n * L)


def f(x, d=4):
    return mp.nstr(x, d)


# ---------- objets exacts ----------
def R_def(ms, ss, r):
    """R_r par la définition 12.6.1, rotation commençant au bloc r."""
    p = len(ms)
    m = [ms[(r + i) % p] for i in range(p)]
    s = [ss[(r + i) % p] for i in range(p)]
    S = [0] * p
    for t in range(1, p):
        S[t] = S[t - 1] + s[t - 1] + m[t]      # σ_{t-1} = s_{t-1} + m_t
    tot, pw = 0, 1                             # pw = 3^{M_t}, M_t = Σ_{j>t} m_j
    for t in range(p - 1, -1, -1):
        tot += (pw << (S[t] + s[t])) - (pw << S[t])
        pw *= 3 ** m[t]
    return tot


def orbit_Y(ms, ss, q, label):
    """Y_r = q·(x_r + 1) = 2^{m_r} R_r : Y_0 par la définition, puis la DYNAMIQUE de Terras
    (montée : x+1 → (3/2)^m (x+1) ; descente : s divisions), valuations exactes et retour au départ."""
    p = len(ms)
    Y = R_def(ms, ss, 0) << ms[0]
    Ys = [Y]
    ok = True
    for r in range(p):
        m, s = ms[r], ss[r]
        ok &= (Y % (1 << m) == 0) and ((Y >> m) & 1 == 1)          # v₂(x_r + 1) = m_r exactement
        V = (Y >> m) * 3 ** m - q                                   # q · (sommet de la montée)
        ok &= (V % (1 << s) == 0) and ((V >> s) & 1 == 1)          # v₂ = s_r exactement, puis impair
        Y = (V >> s) + q
        Ys.append(Y)
    ok &= Ys[p] == Ys[0]
    check(ok, f"dynamique/valuations/retour {label}")
    return Ys[:p]


def terras_sim(ms, ss, q, Y0):
    """Simulation pas à pas, en rationnels exacts, du cycle de Terras rationnel (P2)."""
    x = Fraction(Y0 - q, q)
    x0 = x
    word = []
    for m, s in zip(ms, ss):
        word += [1] * m + [0] * s
    for b in word:
        par = (x.numerator % 2)                # dénominateur impair : parité 2-adique = celle du numérateur
        if par != b:
            return False
        x = (3 * x + 1) / 2 if b else x / 2
    return x == x0


# ---------- Partie F : canaris ----------
print("F. Canaris")
Ys = orbit_Y([1], [1], 1, "cycle trivial")
check(Ys == [2], "cycle trivial : Y_0 = q(1+1) = 2")
m7, n7 = [4, 7, 9, 15, 23, 35, 1], 94
K7 = (3 ** n7).bit_length()
s7 = [1] * 6 + [K7 - n7 - 6]
q7 = (1 << K7) - 3 ** n7
Y7 = orbit_Y(m7, s7, q7, "p=7 publié")
pass7 = sum(Y7[r] >= q7 << m7[r] for r in range(7))
check(K7 == 149 and pass7 == 7, "p=7 publié : K=149, taille 7/7")
check(f(gam(n7, K7), 5) == "6.7438", "p=7 publié : γ = 6,7438")
check(all(Y7[r] % (q7 << m7[r]) != 0 for r in range(7)), "p=7 publié : divisibilité 0/7")
print(f"  trivial Y=2 ; p=7 : K={K7}, γ={f(gam(n7, K7), 6)}, taille {pass7}/7, divisibilité 0/7")

# ---------- Partie A : configurations aléatoires ----------
print("A. Configurations aléatoires (graine 20261019)")
rng = random.Random(20261019)
nconf = npass = nunit = nsim = 0
lo_ratio, hi_ratio = mp.inf, mp.mpf(0)
min_trim = min_unit = mp.inf
for it in range(30000):
    p = rng.randint(1, 7)
    ms = [rng.randint(1, 7) if rng.random() < 0.8 else 1 for _ in range(p)]
    n = sum(ms)
    K = (3 ** n).bit_length() + (0 if rng.random() < 0.75 else rng.randint(1, 3))
    S = K - n
    if S < p:
        continue
    cuts = sorted(rng.sample(range(1, S), p - 1)) if p > 1 else []
    ss = [b - a for a, b in zip([0] + cuts, cuts + [S])]
    q = (1 << K) - 3 ** n
    Ys = orbit_Y(ms, ss, q, f"cfg{it}")
    nconf += 1
    check(all((R_def(ms, ss, r) << ms[r]) == Ys[r] for r in range(p)), f"R_r déf = dynamique cfg{it}")
    if nsim < 400:
        nsim += 1
        check(terras_sim(ms, ss, q, Ys[0]), f"simulation de Terras cfg{it}")
    mn = min(Ys)
    check((1 << (K - 1)) <= mn < p * (1 << K), f"sandwich cfg{it}")
    lo_ratio = min(lo_ratio, mp.mpf(mn) / mp.mpf(1 << (K - 1)))
    hi_ratio = max(hi_ratio, mp.mpf(mn) / mp.mpf(p * (1 << K)))
    if all(Ys[r] >= q << ms[r] for r in range(p)):        # (S)
        npass += 1
        g = gam(n, K)
        t = g + mp.log(p, 2) - eps(p) * n
        min_trim = min(min_trim, t)
        check(t > 0, f"rabot cfg{it}")
        if p >= 2 and 1 in ms:
            nunit += 1
            u = g + mp.log(p, 2) - (L - 1) * (n - L ** (p - 1)) / (L ** (p - 1) - 1)
            min_unit = min(min_unit, u)
            check(u > 0, f"bloc unité (iii) cfg{it}")
print(f"  {nconf} configurations q>0 ; {nsim} simulations de Terras ; {npass} passent (S) ; {nunit} avec bloc unité")
print(f"  sandwich : min_r Y / 2^(K-1) ≥ {f(lo_ratio, 8)} ; min_r Y / (p·2^K) ≤ {f(hi_ratio, 6)}")
print(f"  marge minimale : rabot {f(min_trim, 5)} bit ; bloc unité {f(min_unit, 5)} bit")
# minimax de Rozier (iv) sur réels positifs, toute rotation
viol = 0
for it in range(3000):
    p = rng.randint(1, 9)
    xs = [mp.mpf(rng.random()) ** 3 * 50 + mp.mpf(10) ** -6 for _ in range(p)]
    tot = sum(xs)
    for r in range(p):
        ys = xs[r:] + xs[:r]
        pre, best = mp.mpf(0), -mp.inf
        for y in ys:
            best = max(best, y - (L - 1) * pre)
            pre += y
        if best < eps(p) * tot * (1 - mp.mpf(10) ** -30):
            viol += 1
check(viol == 0, "minimax de Rozier (iv)")
print(f"  minimax de Rozier : {viol} violation sur 3000 n-uplets × toutes rotations")

# ---------- Partie B : Construction B ----------
def constructB(p, n):
    P = 3 ** n
    K = P.bit_length()
    q = (1 << K) - P
    S = K - n
    if S < p:
        return None
    sc = S - (p - 1)
    base = (1 << sc) - 1
    T, pw3, ms = 0, 1, []
    for r in range(p - 1):
        X = (pw3 * base) << (n - T + p - 1 - r)
        c0 = X.bit_length() - q.bit_length()       # cap = max{m ≥ 0 : q·2^m ≤ X}, sans division
        cap = c0 if c0 >= 0 and (q << c0) <= X else c0 - 1
        if cap < 0:
            return None
        budget = n - 1 - T - (p - 2 - r)
        m = min(cap, budget)
        ms.append(m)
        T += m
        pw3 *= 3 ** m
    ms.append(n - T)
    return ms, [1] * (p - 1) + [sc], K, q, S


def hyps(p, n, K, S):
    g = gam(n, K)
    eta = D(mp.mpf(S - p + 1))
    Gp = 1 + eta + (L ** p - L ** 2 - (L - 1) * (p - 2) + (L - 1) ** 2 * n) / ((L - 1) * (L ** p - 1))
    H0 = S >= p and (L - 1) * (n - p) + g >= p + eta
    return g, eta, Gp, H0, g >= max(2 + eta, Gp)


def verifyB(p, n, label, X0=None):
    out = constructB(p, n)
    if out is None:
        return None
    ms, ss, K, q, S = out
    g, eta, Gp, H0, H1 = hyps(p, n, K, S)
    ent = all(m >= 1 for m in ms) and sum(ms) == n and sum(ss) + n == K
    Ys = orbit_Y(ms, ss, q, label)
    Sok = all(Ys[r] >= q << ms[r] for r in range(p))
    Xok = None if X0 is None else all(Ys[r] >= (X0 + 1) * q for r in range(p))
    pre, best = mp.mpf(0), -mp.inf
    for m in ms:
        best = max(best, m - (L - 1) * pre)
        pre += m
    return dict(ms=ms, K=K, q=q, g=g, eta=eta, Gp=Gp, H0=H0, H1=H1, ent=ent, S=Sok, X=Xok,
                c=ms[-1], m0=ms[0], roz=best, Ys=Ys)


print("B. Construction B sous (H0)+(H1′), p = 2..22, n jusqu'à 3·10^5 (graine 7)")
rng = random.Random(7)
nB = nneg = nnegfail = 0
cs = []
for p in range(2, 23):
    top = int(min(3 * 10 ** 5, max(400, 1.6 * float(L) ** p)))
    got = negs = tries = 0
    while (got < 30 or negs < 6) and tries < 4000:
        tries += 1
        n = rng.randint(3 * p + 40, top)
        P = 3 ** n
        K = P.bit_length()
        S = K - n
        if S < p:
            continue
        g, eta, Gp, H0, H1 = hyps(p, n, K, S)
        if not H0:
            continue
        if H1 and got < 30:
            r = verifyB(p, n, f"B p={p} n={n}")
            got += 1
            if not check(r is not None, f"Construction B indéfinie p={p} n={n}"):
                continue
            nB += 1
            ok = r["ent"] and r["S"] and r["c"] >= 1 and mp.almosteq(r["roz"], r["m0"]) and r["m0"] <= r["g"] - r["eta"]
            check(ok, f"Construction B p={p} n={n} : entrées/(S)/crash/Rozier")
            cs.append(r["c"])
        elif (not H1) and g >= 2 + eta and g <= Gp - mp.mpf(1.5) and negs < 6:
            r = verifyB(p, n, f"NC p={p} n={n}")
            negs += 1
            nneg += 1
            if r is None or not (r["ent"] and r["S"]):
                nnegfail += 1
print(f"  {nB} points sous (H0)+(H1′) : tous vérifiés ci-dessus ; crash c ∈ [{min(cs)}, {max(cs)}], c > 1 sur {sum(c > 1 for c in cs)}")
print(f"  contrôle négatif (γ ≤ Γ′ − 1,5) : {nnegfail}/{nneg} configurations ratent (S) ou ne se construisent pas")
check(nnegfail >= 1, "contrôle négatif : l'hypothèse (H1′) mord")

# ---------- Partie C : p₁ ----------
print("C. p₁(X₀) depuis la fraction continue de log₂3")
x, a = L, []
pp, qq = [1, mp.floor(L)], [0, 1]          # p_{-1}, p_0 ; q_{-1}, q_0
a0 = int(mp.floor(L))
x = 1 / (L - a0)
pc, qc = [1, a0], [0, 1]
while qc[-1] < 2 ** 300:
    ai = int(mp.floor(x))
    x = 1 / (x - ai)
    pc.append(ai * pc[-1] + pc[-2])
    qc.append(ai * qc[-1] + qc[-2])
P_, Q_ = pc[1:], qc[1:]                    # P_[j]/Q_[j] = j-ième réduite, Q_[0] = 1
theta = [abs(Q_[j] * L - P_[j]) for j in range(len(Q_))]
check(Q_[:15] == [1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867, 79335, 111202, 190537, 10590737],
      "dénominateurs des réduites de log₂3")


def p1(X0):
    g = 1 + max(mp.log(X0 + 1, 2), LAM)
    ell = D(g) - D(g + 1)
    k = next(k for k in range(1, len(Q_)) if theta[k - 1] <= ell)
    N = Q_[k] + Q_[k - 1]
    p = 2
    while (L ** p - 1) / (2 * (L - 1)) < max(N, 3 * p + 40):
        p += 1
    return p, N, g


table = [(1, 10), (2, 10), (10, 10), (16, 10), (2 ** 8, 22), (2 ** 10, 22), (2 ** 12, 22),
         (2 ** 20, 36), (2 ** 60, 94), (5 * 2 ** 60, 98), (2 ** 71, 110), (2 ** 200, 309)]
for X0, want in table:
    got = p1(mp.mpf(X0))[0]
    check(got == want, f"p₁({X0}) = {got}, attendu {want}")
print("  " + " ; ".join(f"p₁({X0 if X0 < 10**5 else '2^' + str(mp.nint(mp.log(X0, 2)))})={p1(mp.mpf(X0))[0]}" for X0, _ in table))
excess = [(j, p1(mp.mpf(2) ** j)[0] - j / mp.log(L, 2)) for j in range(0, 201)]
mn = min(excess, key=lambda t: t[1])
mx = max(excess, key=lambda t: t[1])
print(f"  p₁ − log_L X₀ sur X₀ = 2^j, 0 ≤ j ≤ 200 : min {f(mn[1], 5)} (j={mn[0]}), max {f(mx[1], 5)} (j={mx[0]})")
ex1 = [(j, e) for j, e in excess if j >= 1]
print(f"  idem 1 ≤ j ≤ 200 : min {f(min(e for _, e in ex1), 5)}, max {f(max(e for _, e in ex1), 5)}")
rows = [1, 16, 2 ** 8, 2 ** 12, 2 ** 20, 2 ** 60, 5 * 2 ** 60, 2 ** 71, 2 ** 200]
er = [p1(mp.mpf(X))[0] - mp.log(X, 2) / mp.log(L, 2) for X in rows]
print(f"  idem sur les lignes de la table : [{f(min(er), 4)}, {f(max(er), 4)}]")

# ---------- Partie D : la fenêtre ----------
print("D. Théorème 12.8.7.4 : fenêtre, Construction B, (S)+(X) et crochets (n* ≤ 1,1·10^6)")
npts = 0
for X0 in [1, 10, 31, 100, 1000, 4096]:
    p1v, N, g = p1(mp.mpf(X0))
    line = []
    for p in range(p1v, 60):
        e = eps(p)
        nstar = int(mp.floor((g - LAM) / e))
        if nstar > 1_100_000:
            break
        lo = nstar - N + 1
        check(lo >= 3 * p + 40, f"bas de fenêtre X0={X0} p={p}")
        found = None
        for n in range(nstar, lo - 1, -1):
            gm = D(mp.ceil(n * L) - n * L)
            if g <= gm <= g + 1:
                found = n
                break
        if not check(found is not None, f"fenêtre vide X0={X0} p={p}"):
            continue
        n = found
        r = verifyB(p, n, f"D X0={X0} p={p} n={n}", X0=X0)
        if not check(r is not None, f"Construction B indéfinie X0={X0} p={p}"):
            continue
        gm, en = r["g"], e * n
        xmin1 = mp.log(mp.mpf(min(r["Ys"])), 2) - mp.log(mp.mpf(r["q"]), 2)   # log₂(x_min + 1)
        Lam = r["K"] * mp.log(2) - n * mp.log(3)
        conds = [r["H0"], r["H1"], r["ent"], r["S"], r["X"], r["c"] >= 1,
                 LAM <= gm - en <= LAM + mp.mpf(1.5), en <= r["m0"] <= gm,
                 gm - 1 <= xmin1 <= gm + mp.mpf("1.87447"),
                 Lam >= mp.mpf(2) ** (-gm), Lam > mp.mpf("0.054") * mp.mpf(2) ** (-en),
                 en < p]
        check(all(conds), f"crochets X0={X0} p={p} n={n} : {conds}")
        npts += 1
        line.append(f"p={p} n={n} γ−εn={f(gm - en, 4)} c={r['c']}")
    print(f"  X₀={X0} (p₁={p1v}, N={N}) : " + " | ".join(line))
print(f"  {npts} points (X₀, p) vérifiés de bout en bout")

# ---------- Partie E : 12.8.7.5 ----------
print("E. Exclusion du bloc unité à l'échelle du Lemme 7, et la constante 2,09")
first, holds_after = None, True
for j in range(0, 201):
    X0 = mp.mpf(2) ** j
    p, N, g = p1(X0)
    e = eps(p)
    nlo = int(mp.floor((g - LAM) / e)) - N + 1
    cond = (L - 1) * e * nlo > LAM + mp.mpf("2.09") + mp.log(p, 2)
    if cond and first is None:
        first = j
    if first is not None and not cond:
        holds_after = False
print(f"  première puissance 2^j où la condition tient : j = {first} ; tient ensuite jusqu'à 200 : {holds_after}")
check(first is not None and 13 <= first <= 20 and holds_after, "12.8.7.5 : de 2^20 au plus tard, puis toujours")
worst = max((L - 1) * (1 + 1 / (L ** (p - 1) - 1)) + mp.mpf(1.5) for p in range(12, 401))
check(worst <= mp.mpf("2.09"), "constante 2,09 pour p ≥ 12")
print(f"  max_(p≥12) (L−1)(1 + 1/(L^(p−1) − 1)) + 1,5 = {f(worst, 6)} ≤ 2,09")
print(f"  2^(−(λ+1,5)) = {f(mp.mpf(2) ** (-(LAM + 1.5)), 6)}")

print(f"\nTOTAL : {NCHK[0]} contrôles, {NCHK[1]} échec(s)")
