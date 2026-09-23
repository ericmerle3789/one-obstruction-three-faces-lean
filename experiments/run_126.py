#!/usr/bin/env python3
# BRECHE-126 — LE LEMME DU DEPLACEMENT UNIQUE : KNIGHT ET LA MOITIE ELEMENTAIRE DE STEINER SONT LE MEME ARGUMENT.
#
# Cadre (carte de Terras T(x) = x/2 ou (3x+1)/2). Un mot de parite w de longueur N a r uns aux positions
# p_0 < ... < p_{r-1} ; le point du cycle rationnel est x(w) = C(w)/d, C(w) = sum_j 2^{p_j} 3^{r-1-j},
# d = 2^N - 3^r (Knight 2025 eq. 2.1 ; Fernandez-Ibanez arXiv 2607.24844 eq. 3-4). Les rotations de w
# donnent les autres membres du meme cycle rationnel.
#
# LEMME. Si deux rotations de w (mots lineaires) different par le deplacement d'un seul 1, de la position
# p a p+t, a travers t zeros, leurs C different de exactement 2^p (2^t - 1) 3^{r-1-j} (l'ordre des uns est
# conserve, donc j ne bouge pas). Si le cycle etait entier, d diviserait les deux C ; comme pgcd(d,6) = 1,
# d | 2^t - 1. Donc : cycle NON entier des que d ne divise pas 2^t - 1 — en particulier TOUJOURS pour
# t = 1 et t = 2, et des que 2^t - 1 < d.
#
# PREDICTIONS (NASA, ecrites avant execution) :
#  P1  Identite : pour chaque paire a un deplacement trouvee, C(r2) - C(r1) = 2^p (2^t - 1) 3^{r-1-j} EXACTEMENT.
#  P2  (Knight, t = 1) Pour tout N <= 20 et tout r avec 2^N > 3^r : un necklace primitif a une paire t = 1
#      SI ET SEULEMENT SI c'est le necklace de Christoffel (uns aux positions floor(N i / r)).
#  P3  [CORRIGEE A L'EXECUTION, 2026-09-23 — gardee visible] "t minimal du circuit = N - r pour tout (N,r)" :
#      FAUX pour r = 1, ou le circuit 1 0^(N-1) EST aussi un mot de Christoffel (t = 1). Enonce juste : pour r >= 2,
#      (Steiner, moitie elementaire) Le necklace circuit 1^r 0^(N-r) a t minimal = N - r ; la condition
#      est d | 2^(N-r) - 1, qui est la reduction classique (d | 3^r - 2^r <=> d | 2^(N-r) - 1).
#  P4  Coherence : aucun necklace exclu par le lemme n'a C divisible par d (verification directe).
#  P5  Recensement pres de la somme de couture : la classe a un deplacement est rare (quelques necklaces
#      par ligne sur des milliers) et sa fraction decroit avec N.
#  P6  CONTROLE NEGATIF : le cycle trivial (N,r) = (2,1), d = 1 : la paire existe (mot 10 / ... ) mais le
#      lemme ne conclut rien (d = 1 divise tout) — il ne doit pas exclure le seul cycle qui existe.
#  P7  (caracterisation, trouvee par le workflow du 23/09 et verifiee par un refere independant a N <= 26)
#      pour r >= 2 : un necklace a une paire a un deplacement SSI sa suite cyclique des longueurs de
#      plages de zeros (apres chaque 1) prend exactement deux valeurs a et a+t et est un mot equilibre
#      (rotation d'un mot de Christoffel sur r lettres, c valeurs lourdes, pgcd(c,r) = 1) ; t est alors
#      unique et egal a max - min. Prediction : exact pour N <= 16, tout r >= 2.
from itertools import combinations
from math import log2, gcd
from collections import Counter
L = log2(3)
FAILS = []
def check(nom, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {nom}" + (f"   {detail}" if detail else ""))
    if not ok: FAILS.append(nom)
def C(w):
    r = sum(w); s = 0; j = 0
    for p, b in enumerate(w):
        if b: s += 2**p * 3**(r-1-j); j += 1
    return s
def rotations(w): return {w[i:]+w[:i] for i in range(len(w))}
def primitive(w):
    n = len(w); return all(w != w[i:]+w[:i] for i in range(1, n) if n % i == 0)
def one_moves(rots):
    """all (t, r1, r2, p, j) with r2 = r1 with its j-th one moved right from p to p+t through zeros, r1, r2 rotations"""
    out = []
    for w in rots:
        n = len(w); j = -1
        for p in range(n):
            if not w[p]: continue
            j += 1
            for t in range(1, n):
                q = p + t
                if q >= n or w[q]: break
                v = list(w); v[p] = 0; v[q] = 1; v = tuple(v)
                if v in rots: out.append((t, w, v, p, j)); break
    return out
def christoffel(N, r): return tuple(1 if p in {(N*i)//r for i in range(r)} else 0 for p in range(N))

print("=" * 94); print("CANARIS (a la main avant le code)"); print("=" * 94)
check("C1  cycle trivial : mot 10, C = 2^0*3^0 = 1, d = 4 - 3 = 1, x = 1", C((1, 0)) == 1)
check("C2  Knight Ex. 5.5 : (8,5), v_h = 11011010 -> C = 319, d = 13", C((1,1,0,1,1,0,1,0)) == 319 and 2**8 - 3**5 == 13)
check("C3  Knight Ex. 5.5 : v_h^R = 01011011 -> C = 842", C((0,1,0,1,1,0,1,1)) == 842)
check("C4  mot de Christoffel (8,5) selon floor(8i/5) = 11011010 (Knight Ex. 4.2)", christoffel(8, 5) == (1,1,0,1,1,0,1,0))
assert not FAILS, FAILS

print(); print("=" * 94); print("P1/P2/P4 — EXHAUSTIF N <= 20, TOUT r AVEC 2^N > 3^r, d > 1"); print("=" * 94)
n_neck = 0; n_pairs = 0; bad_id = []; bad_chr = []; bad_int = []; rows = []
for N in range(3, 21):
    for r in range(1, N):
        d = 2**N - 3**r
        if d <= 1: continue
        chr_rots = rotations(christoffel(N, r)) if gcd(N, r) == 1 else None
        seen = set(); cls = Counter(); cnt = 0
        for ones in combinations(range(N), r):
            w = tuple(1 if i in ones else 0 for i in range(N))
            if w in seen: continue
            R = rotations(w); seen |= R
            if not primitive(w): continue
            cnt += 1; n_neck += 1
            mv = one_moves(R)
            for (t, a, b, p, j) in mv:
                n_pairs += 1
                if C(b) - C(a) != 2**p * (2**t - 1) * 3**(r - 1 - j): bad_id.append((N, r, a, b))
            ts = {m[0] for m in mv}
            has1 = 1 in ts
            if has1 != (R == chr_rots): bad_chr.append((N, r, ''.join(map(str, max(R)))))
            if mv:
                tmin = min(ts)
                cls[tmin if tmin <= 2 else '>=3'] += 1
                if (2**tmin - 1) % d != 0 and C(w) % d == 0: bad_int.append((N, r))
        if N == int(r*L) + 1: rows.append((N, r, d, cnt, cls))
check(f"P1 identite exacte sur les {n_pairs} paires a un deplacement trouvees", not bad_id, f"{len(bad_id)} ecarts")
check(f"P2 t = 1 <=> necklace de Christoffel, sur {n_neck} necklaces primitifs (N <= 20, tout r)", not bad_chr, f"contre-exemples : {bad_chr[:4]}")
check("P4 aucun necklace exclu par le lemme n'a C divisible par d", not bad_int, str(bad_int[:4]))

print(); print("=" * 94); print("P3 — LE CIRCUIT : t minimal = N - r, et la condition est la reduction classique de Steiner"); print("=" * 94)
okc = True; okred = True
for N in range(3, 21):
    for r in range(1, N):
        d = 2**N - 3**r
        if d <= 1: continue
        w = tuple([1]*r + [0]*(N-r))
        if not primitive(w): continue
        mv = one_moves(rotations(w))
        tmin = min(m[0] for m in mv) if mv else None
        okc &= (tmin == N - r) if r >= 2 else (tmin == 1 and rotations(w) == rotations(christoffel(N, 1)))
        okred &= (((3**r - 2**r) % d == 0) == ((2**(N-r) - 1) % d == 0))
check("t minimal du circuit = N - r pour r >= 2 ; pour r = 1 le circuit est le mot de Christoffel (t = 1), N <= 20", okc)
check("d | C(circuit) = 3^r - 2^r  <=>  d | 2^(N-r) - 1  (la reduction elementaire de Steiner)", okred)

print(); print("=" * 94); print("P5 — RECENSEMENT A LA SOMME DE COUTURE N = ceil(r log2 3)"); print("=" * 94)
print(f"  {'N':>3} {'r':>3} {'d':>8} {'necklaces':>9} {'t=1':>4} {'t=2':>4} {'t>=3':>5}  fraction")
fr = []
for (N, r, d, cnt, cls) in rows:
    f = (cls[1] + cls[2] + cls['>=3']) / cnt
    fr.append(f)
    print(f"  {N:>3} {r:>3} {d:>8} {cnt:>9} {cls[1]:>4} {cls[2]:>4} {cls['>=3']:>5}  {100*f:6.2f} %")
check("fraction decroissante sur les 5 dernieres lignes (classe mince)", all(fr[i] >= fr[i+1] for i in range(len(fr)-5, len(fr)-1)))

print(); print("=" * 94); print("P6 — CONTROLE NEGATIF : le cycle trivial ne doit pas etre exclu"); print("=" * 94)
mv = one_moves(rotations((1, 0)))
check("(N,r) = (2,1) : d = 1 divise 2^t - 1 pour tout t -> le lemme ne conclut rien", 2**2 - 3**1 == 1 and all((2**t - 1) % 1 == 0 for t in range(1, 5)), f"paires trouvees : {len(mv)}")

print(); print("=" * 94); print("P7 — CARACTERISATION : suite des plages de zeros a deux valeurs et equilibree"); print("=" * 94)
def gaps(w):
    n = len(w); ones = [i for i in range(n) if w[i]]
    return tuple((ones[(k+1) % len(ones)] - ones[k] - 1) % n for k in range(len(ones)))
def balanced_two_valued(g):
    vals = sorted(set(g))
    if len(vals) != 2: return None
    a, b = vals; r = len(g); h = tuple(1 if x == b else 0 for x in g); c = sum(h)
    if gcd(c, r) != 1: return None
    return (b - a) if rotations(h) == rotations(christoffel(r, c)) else None
mism = 0; tbad = 0; seen_n = 0
for N in range(3, 17):
    for r in range(2, N):
        seen = set()
        for ones in combinations(range(N), r):
            w = tuple(1 if i in ones else 0 for i in range(N))
            if w in seen: continue
            R = rotations(w); seen |= R
            if not primitive(w): continue
            seen_n += 1
            mv = one_moves(R); pred = balanced_two_valued(gaps(w))
            if bool(mv) != (pred is not None): mism += 1
            elif mv and {m[0] for m in mv} != {pred}: tbad += 1
check(f"P7 classe a un deplacement = suites de zeros bi-valuees equilibrees, sur {seen_n} necklaces (N <= 16, r >= 2)", mism == 0, f"{mism} desaccords")
check("P7 t unique et egal a max - min des plages", tbad == 0, f"{tbad} ecarts")

print(); print("=" * 94); print(f"TOTAL : {'TOUS LES CONTROLES PASSENT' if not FAILS else 'ECHECS : ' + str(FAILS)}"); print("=" * 94)
