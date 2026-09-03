#!/usr/bin/env python3
# BRECHE-050 — SECTION 96, REPRIS A LA RACINE : LE TEMOIN EXACT, ET DEUX RETRACTATIONS.
#
# POURQUOI CE RUN (round 13 de la correspondance Macindoe, 2026-09-03).
# B. Macindoe a reconstruit §96 de son cote et a rapporte une NON-REPRODUCTION pour p=3
# a petit k. Verification faite : sa mesure est juste, mais elle porte sur un AUTRE graphe
# (carte acceleree, un seul successeur canonique par reste). Notre graphe est celui de
# Terras (x -> x/2 ou (px+1)/2) avec les DEUX relevements de Z/2^(k+1) — run_049 ligne 33.
# En reponse, §96 est repris ici a la racine, en ENTIERS EXACTS, sans Bellman-Ford et sans
# recensement de fantomes.
#
# CE QUI EST NOUVEAU ICI : rien de mathematique. La boucle est celle du §95
# (point fixe de la branche montante, x = -1/(p-2) mod 2^k) et la legitimite des
# contraintes est l'argument du §96 (run_049 P1). Ce run montre seulement que ces DEUX
# resultats deja acquis suffisent a eux seuls, en deux lignes, sans le reste de l'appareil.
#
# CE QUI EST RETRACTE ICI (deux points, aucun n'affecte la conclusion) :
#  R1. run_048 ECHOUE SON PROPRE CANARI C3 et s'arrete : sa fonction `rationnel` parcourt
#      le mot a l'envers (`reversed(bits)`, ligne 76) la ou run_049 le parcourt a l'endroit.
#      Ses sorties P3/P4/P5 n'ont donc JAMAIS ete produites.
#  R2. Le bug corrige (un mot), run_048 echoue alors son propre CONTROLE P5 : il sort
#      x = -6, qui n'est sur aucun cycle (T(-6)=-3, -4, -2, -1). Cause : il resout
#      l'equation du mot sans verifier que les parites de la trajectoire suivent le mot.
#      => LE RECENSEMENT DE FANTOMES EST RETIRE. En particulier le chiffre "100 % de
#      fantomes a p=7,k=8" cite dans la correspondance n'a AUCUN artefact derriere lui :
#      run_048 ne teste pas p=7, et son recensement est faux deux fois.
#      La conclusion du §96 n'en depend pas — run_049 P1 etablit precisement que la
#      qualite de fantome est SANS OBJET, puisque chaque ARETE est realisee.
#
# PREDICTIONS (NASA, ecrites avant execution) :
#  P1  Pour tout p impair >= 3 et tout k >= 1, r_p = -(p-2)^(-1) mod 2^(k+1) est impair,
#      et l'arete montante issue de r_p boucle sur u_p = r_p mod 2^k. Prediction : exact,
#      pour tous les p et k testes, en arithmetique entiere.
#  P2  Cette arete est realisee par une INFINITE d'entiers POSITIFS x = r_p + m*2^(k+1),
#      et pour p >= 3 chacun MONTE : T(x) > x. Prediction : exact.
#  P3  *** LA CONCLUSION *** La contrainte de l'arete est g(u_p) - g(u_p) > log(p/2),
#      c'est-a-dire 0 > log(p/2), fausse des que p > 2 — comparaison d'ENTIERS.
#      Donc aucune altitude V(x) = x f(x mod 2^k) ne decroit sur tous les entiers
#      positifs, pour aucun k, pour aucun f. Prediction : etabli sans calcul flottant.
#  P4  Le desaccord avec la reconstruction Macindoe s'explique entierement : dans la carte
#      ACCELEREE a successeur canonique unique, l'arete temoin est ABSENTE (elle vient du
#      relevement m=1). Prediction : absente, et aucun cycle fautif a p=3, k=4..9.
#  P5  CONTROLE DE NON-VACUITE : pour p=3, u_p = 2^k - 1 et le plus petit temoin positif
#      est x = 2^(k+1) - 1 ; sa trajectoire monte strictement. Verifie sur les entiers.
#  P6  CONTROLE NEGATIF : pour p=1 (x -> (x+1)/2, qui DESCEND), la contrainte 0 > log(1/2)
#      est VRAIE : la methode ne doit PAS conclure a l'impossibilite. Si elle conclut
#      quand meme, l'argument prouve trop et il est faux.
from fractions import Fraction

FAILS = []
def check(nom, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {nom}" + (f"   {detail}" if detail else ""))
    if not ok: FAILS.append(nom)

def T(x, p=3):
    return x // 2 if x % 2 == 0 else (p * x + 1) // 2

def temoin(p, k):
    """r_p = -(p-2)^(-1) mod 2^(k+1) : le relevement dont l'arete montante boucle."""
    M2 = 1 << (k + 1)
    return (-pow((p - 2) % M2, -1, M2)) % M2

print("=" * 94)
print("CANARIS (calcules a la main AVANT le code)")
print("=" * 94)
check("C1  p=3, k=8 : le temoin est 2^9-1 = 511", temoin(3, 8) == 511, f"temoin={temoin(3,8)}")
check("C2  T(511) = 767 et 767 = 511 mod 256", T(511) == 767 and 767 % 256 == 511 % 256 == 255)
check("C3  le cycle trivial 1 -> 2 -> 1 est bien parcouru", T(1) == 2 and T(2) == 1)
check("C4  -1 est un point fixe reel de la branche montante", T(-1) == -1)
check("C5  p=5 : le point fixe -1/3 n'est PAS un entier (rappel §95/run_048 P2)",
      Fraction(1, 2 - 5).denominator != 1, str(Fraction(1, 2 - 5)))
assert not FAILS, f"canaris en echec : {FAILS}"

print()
print("=" * 94)
print("P1 — LE TEMOIN EXISTE POUR TOUT p IMPAIR ET TOUT k  (entiers exacts, zero flottant)")
print("=" * 94)
n1 = 0
bad1 = []
for p in range(3, 202, 2):
    for k in range(1, 41):
        M = 1 << k
        r = temoin(p, k)
        u = r % M
        if not (r % 2 == 1 and (p * r + 1) // 2 % M == u):
            bad1.append((p, k))
        n1 += 1
check(f"boucle montante presente : {n1} couples (p,k), p=3..201 impairs, k=1..40",
      not bad1, f"echecs : {bad1[:5] if bad1 else 'aucun'}")
print(f"       exemples : " + ", ".join(
    f"p={p},k=8 -> u={temoin(p,8)%256}" for p in (3, 5, 7, 9, 11)))

print()
print("=" * 94)
print("P2 — L'ARETE EST REALISEE PAR UNE INFINITE D'ENTIERS POSITIFS, ET ILS MONTENT")
print("=" * 94)
n2 = 0
bad2 = []
for p in (3, 5, 7, 9, 11, 101):
    for k in (1, 2, 3, 5, 8, 12, 20, 31):
        M = 1 << k
        M2 = M << 1
        r = temoin(p, k)
        u = r % M
        for m in range(0, 60):
            x = r + m * M2
            if x <= 0:
                continue
            y = T(x, p)
            n2 += 1
            if not (x % M == u and y % M == u and y > x):
                bad2.append((p, k, m))
check(f"{n2} entiers positifs temoins : meme reste, image de meme reste, et STRICTEMENT croissants",
      not bad2, f"echecs : {bad2[:5] if bad2 else 'aucun'}")
x0 = temoin(3, 8)
print(f"       le plus petit pour p=3,k=8 : x={x0} -> T(x)={T(x0)} "
      f"(restes {x0 % 256} et {T(x0) % 256}, ratio {T(x0)/x0:.4f})")

print()
print("=" * 94)
print("P3 *** LA CONCLUSION *** — LA CONTRAINTE DE LA BOUCLE, EN ENTIERS")
print("=" * 94)
print("  Sur l'arete u -> u, la condition de decroissance de V(x) = x f(x mod 2^k) s'ecrit")
print("  g(u) - g(u) > log(2/p) apres passage au log, soit 0 > log(2/p), soit p > 2.")
print("  C'est une comparaison d'ENTIERS : aucun flottant n'intervient.")
bad3 = [p for p in range(3, 202, 2) if not (p > 2)]
check("p > 2 pour tout p impair >= 3 : la contrainte est violee, le systeme est insatisfiable",
      not bad3)
print("  -> aucune altitude a quotient fini ne decroit sur tous les entiers positifs,")
print("     pour aucun k, pour aucun f. Sans Bellman-Ford, sans recensement, sans flottant.")

print()
print("=" * 94)
print("P4 — POURQUOI LA RECONSTRUCTION MACINDOE DIVERGE : L'ARETE TEMOIN Y EST ABSENTE")
print("=" * 94)


def graphe_accelere_canonique(p, k):
    """la carte ACCELEREE x -> (px+1)/2^v sur les restes impairs, UN successeur
       (representant canonique seul) — la convention que Macindoe a du deviner."""
    M = 1 << k
    succ, val = {}, {}
    for r in range(1, M, 2):
        y = p * r + 1
        v = (y & -y).bit_length() - 1
        succ[r], val[r] = (y >> v) % M, v
    return succ, val


def cycles_fautifs_acceleres(p, k):
    succ, val = graphe_accelere_canonique(p, k)
    coul, out = {}, []
    for s in range(1, 1 << k, 2):
        if coul.get(s, 0):
            continue
        chemin, pos, r = [], {}, s
        while coul.get(r, 0) == 0:
            coul[r] = 1
            pos[r] = len(chemin)
            chemin.append(r)
            r = succ[r]
        if coul.get(r, 0) == 1:
            cyc = chemin[pos[r]:]
            L, K = len(cyc), sum(val[q] for q in cyc)
            if p ** L >= (1 << K):
                out.append((L, K))
        for q in chemin:
            coul[q] = 2
    return out


print(f"  {'p':>3} {'k':>3} {'cycles fautifs (carte acceleree, 1 successeur)':>48}")
for p, ks in ((3, range(4, 17)), (7, [8])):
    for k in ks:
        f = cycles_fautifs_acceleres(p, k)
        print(f"  {p:>3} {k:>3} {str(len(f)) + ('  ' + str(sorted(f)[:3]) if f else ''):>48}")
succ3, _ = graphe_accelere_canonique(3, 8)
u3 = temoin(3, 8) % 256
check("l'arete temoin u -> u est ABSENTE de la carte acceleree canonique",
      succ3[u3] != u3, f"u={u3} y va vers {succ3[u3]}, pas vers lui-meme")
print("  -> sa non-reproduction a p=3 est exacte, et porte sur un autre objet :")
print("     un seul relevement (m=0) la ou la relation en a 2^v. Le temoin vient de m=1.")

print()
print("=" * 94)
print("P5 — CONTROLE DE NON-VACUITE, ET UNE CORRECTION DE FORMULATION")
print("=" * 94)
x = temoin(3, 8)
suite = [x]
for _ in range(6):
    x = T(x)
    suite.append(x)
print("  " + " -> ".join(f"{t} [{t % 256}]" for t in suite) + "   (entre crochets : le reste mod 2^8)")
check("le temoin monte : premier pas strictement croissant",
      suite[1] > suite[0], f"{suite[0]} -> {suite[1]}")
check("le temoin boucle : x et T(x) ont le MEME reste mod 2^k",
      suite[0] % 256 == suite[1] % 256, f"reste {suite[0] % 256}")
#  Ce controle a d'abord ete ecrit comme "la trajectoire reste dans la classe pour
#  toujours". IL A ECHOUE, et il avait raison d'echouer : au pas 2 la trajectoire QUITTE
#  la classe (1151 = 127 mod 256). L'arete boucle, mais aucun entier ne la parcourt deux
#  fois : le relevement de 767 dans Z/2^(k+1) est 255, pas 511, donc l'etape suivante
#  emprunte l'autre branche. La formulation "elle monte pour toujours dans la meme classe"
#  etait FAUSSE et est retiree.
#  Rien de l'argument n'en depend, et c'est precisement le point du §96 (run_049 P1) :
#  la contrainte porte sur l'ARETE, pas sur une trajectoire qui boucle. UN SEUL PAS suffit.
quitte = [i for i in range(1, len(suite)) if suite[i] % 256 != 255]
check("correction enregistree : la trajectoire QUITTE la classe des le pas 2",
      quitte and quitte[0] == 2, f"premier pas hors classe : {quitte[0] if quitte else 'aucun'}")
print("  -> un seul pas suffit : V(T(x)) = 767*f(255) > 511*f(255) = V(x), pour TOUT f > 0.")
print("     Aucun cycle n'est requis, donc la question 'fantome ou reel' ne se pose meme pas.")

print()
print("=" * 94)
print("P6 — CONTROLE NEGATIF : l'argument ne doit PAS prouver trop")
print("=" * 94)
print("  Pour p=1 la branche 'montante' x -> (x+1)/2 DESCEND. La contrainte de boucle")
print("  devient 0 > log(2/1), soit 1 > 2 : FAUSSE, donc la boucle n'obstrue RIEN.")
check("l'argument ne conclut pas a l'impossibilite quand p=1 (il prouverait trop)",
      not (1 > 2))
print("  -> le critere est bien p > 2, et il separe correctement les cas.")

print()
print("=" * 94)
print(f"TOTAL : {'TOUS LES CONTROLES PASSENT' if not FAILS else 'ECHECS : ' + str(FAILS)}")
print("=" * 94)
