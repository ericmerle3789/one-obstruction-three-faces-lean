#!/usr/bin/env python3
# test_REQ-MATH-010_kangourous_cycles_reels.py — ARES
# LA QUESTION D'ERIC : "ne peut-on pas prouver simplement que les kangourous (2^a, 3^b)
# ne vont pas a la meme vitesse, donc jamais la meme marche ?"
# REPONSE EN 4 ACTES, tout machine :
#  A. Le moyen simple EXISTE : 2^a != 3^b toujours (parite / factorisation unique) — verifie.
#  B. MAIS le jeu contient un escabeau : le +1 de 3n+1. La boucle n'exige pas "meme marche",
#     elle exige "marches voisines + compensation exacte". Preuve que cette porte est REELLE :
#     les cycles 1, -1, -5, -17 EXISTENT — on les detecte, on extrait (k, K), et on verifie
#     que chacun est accroche a un frolement : n0 * (2^K - 3^k) = R exactement.
#  C. CONTRASTE : le frolement suivant cote positif (2^8 vs 3^5, q = +13) ne porte AUCUN
#     cycle — demonstration EXHAUSTIVE (toutes les compositions de s), en ne testant
#     qu'UNE rotation par profil, grace a L-A1 (les p divisibilites n'en sont qu'une).
#  D. Morale : tout argument "simple" (vitesse/parite) prouverait TROP — il interdirait
#     aussi les 4 boucles reelles. C'est le canari des preuves.
from itertools import product as iproduct

def v2(x):
    x = abs(x)
    return (x & -x).bit_length() - 1

def T(n):  # odd map, valable pour n impair positif ou negatif
    y = 3*n + 1
    return y >> v2(y), v2(y)

print("=== A. LE MOYEN SIMPLE (il existe, il est vrai) ===")
clash = [(a, b) for a in range(1, 301) for b in range(1, 191) if 2**a == 3**b]
print(f"2^a = 3^b pour a<=300, b<=190 ? {clash if clash else 'JAMAIS'}")
print("Preuve (3 lignes) : 2^a est pair, 3^b est impair ; un nombre n'est pas les deux.")
print("Corollaire vitesse : log2(3) irrationnel (sinon 2^a = 3^b). ACQUIS depuis toujours.")

print("\n=== B. MAIS LES BOUCLES EXISTENT — detection + ancrage au frolement ===")
def trace_cycle(n0, maxit=100):
    seen, n, path, svals = {}, n0, [], []
    for _ in range(maxit):
        if n in seen:
            i = seen[n]
            return path[i:], svals[i:]
        seen[n] = len(path); path.append(n)
        n, s = T(n); svals.append(s)
    return None, None

def steiner_R(svals):
    # R = sum_t 3^{k-1-t} * 2^{S_t},  S_t = somme des s_j pour j<t
    k = len(svals); R, S = 0, 0
    for t in range(k):
        R += 3**(k-1-t) * 2**S
        S += svals[t]
    return R

print(f"{'depart':>7} {'cycle (impairs)':>28} {'k':>3} {'K':>3} {'q=2^K-3^k':>10} {'R':>6} {'R/q':>6} {'ancrage'}")
for n0 in (1, -1, -5, -17):
    cyc, svals = trace_cycle(n0)
    k, K = len(cyc), sum(svals)
    q = 2**K - 3**k
    R = steiner_R(svals)
    ok = (R % q == 0) and (R // q == cyc[0])
    frol = f"2^{K} vs 3^{k}"
    print(f"{n0:>7} {str(cyc):>28} {k:>3} {K:>3} {q:>10} {R:>6} {R//q:>6} {frol}  exact={ok}")

print("\n=== C. LE FROLEMENT SUIVANT COTE POSITIF : 2^8 vs 3^5 (q = +13) ===")
print("Enumeration EXHAUSTIVE : k=5 pas impairs, K in {8..12}, toutes compositions de s ;")
print("par L-A1 (transport), UNE rotation suffit : on teste q | R_0 seulement.")
total, passers = 0, []
for K in range(8, 13):
    q = 2**K - 3**5
    # compositions de K en 5 parts >= 1
    for cuts in iproduct(range(1, K-3), repeat=4):
        s4 = K - sum(cuts)
        if s4 < 1: continue
        svals = list(cuts) + [s4]
        total += 1
        R = steiner_R(svals)
        if R % q == 0:
            n0 = R // q
            # candidat : doit etre impair, positif, et engendrer un vrai cycle
            passers.append((K, svals, n0))
print(f"profils testes : {total} ; divisibilite q | R_0 satisfaite : {len(passers)} fois")
for K, sv, n0 in passers:
    # verification finale : n0 engendre-t-il vraiment un cycle de ce profil ?
    cyc, svals2 = trace_cycle(n0) if n0 % 2 == 1 and n0 > 0 else (None, None)
    print(f"  candidat K={K} s={sv} n0={n0} -> vrai cycle positif ? {cyc is not None and len(cyc)==5}")
if not passers:
    print("=> AUCUN profil ne passe : le frolement 256/243 ne porte AUCUN cycle (preuve exhaustive).")

print("\n=== D. MORALE (le canari des preuves) ===")
print("Les boucles 1, -1, -5, -17 sont REELLES et vivent des frolements (q = 1, -1, -1, -139).")
print("Tout argument 'simple' (parite, vitesse) qui interdirait les boucles interdirait AUSSI")
print("celles-la — donc il prouverait trop, donc il est faux. La conjecture n'est pas")
print("'les kangourous ne se rencontrent jamais' (acquis) ; c'est : 'le cote positif")
print("n'aura plus jamais le coup de chance' — frolement + compensation exacte du +1.")
raise SystemExit(0)
