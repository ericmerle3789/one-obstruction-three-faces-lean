#!/usr/bin/env python3
# =============================================================================================
# ⚠️  RETRACTATION PARTIELLE (2026-09-03) — LIRE AVANT DE CITER QUOI QUE CE SOIT D'ICI.
#
# Ce fichier est conserve EXACTEMENT tel qu'il etait ecrit ; rien n'est supprime ni corrige.
# Deux defauts, trouves en le RE-EXECUTANT pour la livraison du round 14 a B. Macindoe :
#
#  R1. LE SCRIPT NE S'EXECUTE PAS. Son propre canari C3 echoue et l'assert ligne 93 l'arrete.
#      Cause : `rationnel` parcourt le mot A L'ENVERS (`reversed(bits)`, ligne 76) la ou la
#      version de run_049 le parcourt a l'endroit ; sur le mot [1,0] il rend 2 au lieu de 1.
#      CONSEQUENCE : les sorties P3, P4 et P5 de ce fichier N'ONT JAMAIS ETE PRODUITES.
#      Le canari a fait son travail — c'est le rapport qui a suivi qui ne l'a pas ecoute.
#
#  R2. LE BUG CORRIGE (un mot : `reversed(bits)` -> `bits`), le script echoue alors son
#      PROPRE CONTROLE P5 : il sort x = -6, qui n'est sur aucun cycle (T: -6, -3, -4, -2, -1).
#      Cause : il resout l'equation lineaire du mot sans verifier que les PARITES de la
#      trajectoire suivent effectivement ce mot. Son recensement compte donc des solutions
#      formelles, pas des cycles.
#      => LE RECENSEMENT DE FANTOMES DE CE FICHIER EST RETIRE EN ENTIER. En particulier le
#      chiffre "100 % de fantomes parmi les cycles fautifs a p=7, k=8", cite dans la
#      correspondance (round 13, §6) et dans briefs/merle-breach-campaign-map.md, N'A PAS
#      D'ARTEFACT DERRIERE LUI : ce fichier ne teste jamais p=7, et son recensement est faux
#      deux fois. Le chiffre est retire, pas corrige.
#
#  AMENDEMENT (2026-09-26, round 17 — rien ci-dessus n'est supprime) :
#   - R1 reste vrai POUR CE FICHIER. Mais une VERSION CORRIGEE a tourne le 2026-08-05 depuis l'entree standard,
#     jamais sauvee ; recuperee et relancee, sa sortie est identique a l'octet a l'archive (sha256 fbcd923987a75419) :
#     c'est experiments/run_127.py. Le chiffre est RESTAURE a sa vraie portee : p=7, k=8, 330 cycles fautifs,
#     0 realise, exhaustif pour L <= 11 (run_128, run_129). "Jamais produites" et "pas d'artefact" sont faux.
#   - La CAUSE donnee en R2 est fausse : un test de parite absent ne peut pas produire un entier hors cycle
#     (bijection de parite). L'accumulateur de CE fichier oublie le facteur p sur une montee ((num+1)/2 au lieu
#     de (p*num+1)/2) ; c'est de la que vient x = -6 (run_130). Voir rounds/R17-merle.md §1 du depot commun.
#
# CE QUI SURVIT, ET QUI EST L'ESSENTIEL : P1 et P2 (la boucle du §95, x = 1/(2-p), entiere
# pour p=3 seulement) n'utilisent que des mots d'UNE lettre, ou l'ordre de parcours est sans
# effet — canaris C1, C2, C4 verts. Ce resultat tient.
#
# ET LA CONCLUSION DU §96 NE DEPEND PAS DU RECENSEMENT : run_049 (P1, 20 000 aretes) etablit
# que la qualite de "fantome" est SANS OBJET, puisque chaque ARETE est realisee par de vrais
# entiers. Le recensement etait la question posee, pas la reponse retenue.
# Reprise exacte et complete : run_050.py.
# =============================================================================================
# BRECHE-048 — L'OBSTRUCTION EST-ELLE REELLE, OU UN FANTOME ?
#
# CE QUI A CONDUIT ICI (§95). L'obstruction est la boucle au point fixe de la branche
# montante, x = -1/(p-2) mod 2^k, presente pour TOUT p impair (25 cas verifies).
# QUESTION NON POSEE : cette boucle correspond-elle a un VRAI cycle d'entiers ?
#
# FILTRE A LA MAIN.
#   p=3 : boucle en -1, et T(-1) = (-3+1)/2 = -1. *** VRAI point fixe, il EXISTE dans Z. ***
#   p=5 : boucle en -1/3, qui n'est PAS un entier. *** AUCUN entier a cet endroit. ***
# Si c'est confirme, l'obstruction est un FANTOME : un cycle du monde des RESTES sans
# realisation dans les ENTIERS. La methode du §80 echouerait alors non pas devant un vrai
# obstacle, mais faute de savoir distinguer un obstacle d'un mirage.
#
# LE CALCUL EXACT. Un cycle du graphe des restes de longueur L avec j montees determine un
# RATIONNEL : en parcourant le cycle, x = B / (2^L - p^j) ou B se lit sur le mot. Le cycle
# "existe" ssi ce rationnel est ENTIER. C'est exactement la condition q | B de nos
# coordonnees reduites (§54), retrouvee ici par un autre chemin.
#
# PREDICTIONS (NASA) :
#  P1  p=3 : la boucle donne x = 1/(2-3) = -1. ENTIER. Prediction : oui, et c'est le cycle
#      negatif trivial connu.
#  P2  p=5,7,9,11 : la boucle donne x = 1/(2-p) = -1/(p-2). NON ENTIER sauf p=3.
#      Prediction : exact.
#  P3  *** LE TEST *** Parmi TOUS les cycles fautifs du graphe des restes, combien se
#      realisent en cycles d'entiers ? Prediction : une poignee (les cycles connus), le
#      reste sont des FANTOMES. Si c'est le cas, l'obstruction du §80 est un mirage.
#  P4  *** L'ECART *** Le nombre de cycles du graphe croit avec k, celui des cycles entiers
#      reste a ~4. Prediction : l'ecart EXPLOSE, et c'est lui qui condamne la methode.
#  P5  CONTROLE : les cycles entiers trouves doivent etre EXACTEMENT les connus
#      (1 ; -1 ; -5,-7 ; -17,...). Sinon le code est faux.
from math import log, log2
from fractions import Fraction

def graphe(k, p):
    M = 1 << k; ar=[]
    for r in range(2*M):
        u = r % M
        if r % 2 == 1: ar.append((u, ((p*r+1)//2) % M, 1))
        else:          ar.append((u, (r//2) % M, 0))
    return M, ar

def tous_cycles_fautifs(k, p, lim=200000):
    """cycles simples du graphe a relevements, de fraction de montees > log_p(2).
       exploration bornee : on ne pretend pas a l'exhaustivite au-dela de lim."""
    M, ar = graphe(k, p)
    succ = {}
    for u,v,b in ar: succ.setdefault(u, []).append((v,b))
    seuil = 1/log2(p)
    trouves = {}
    vus_glob = set()
    for start in range(M):
        if start in vus_glob: continue
        pile = [(start, [start], [])]
        n = 0
        while pile and n < 400:
            u, chemin, bits = pile.pop(); n += 1
            for v, b in succ.get(u, []):
                if v == start:
                    L = len(chemin); j = sum(bits)+b
                    if L and j/L > seuil:
                        cle = tuple(sorted(chemin))
                        if cle not in trouves: trouves[cle] = (chemin, bits+[b], L, j)
                elif v not in chemin and len(chemin) < 12:
                    pile.append((v, chemin+[v], bits+[b]))
        vus_glob.add(start)
        if len(trouves) > 400: break
    return trouves, seuil

def rationnel(bits, p):
    """x = B / (2^L - p^j) pour le mot de montees/descentes donne"""
    L = len(bits); j = sum(bits)
    # on parcourt le mot : x -> (p x + 1)/2 si montee, x/2 si descente
    # au bout du cycle : x = (p^j x + B) / 2^L, donc x (2^L - p^j) = B
    num = Fraction(0); coef = Fraction(1)
    for b in reversed(bits):
        if b: num = (num + 1) / 2; coef = coef * p / 2
        else: num = num / 2; coef = coef / 2
    # x = coef*x + num  =>  x (1 - coef) = num
    if coef == 1: return None
    return num / (1 - coef)

print("="*94); print("CANARIS (a la main avant le code)"); print("="*94)
c1 = rationnel([1], 3) == Fraction(-1)
c2 = rationnel([1], 5) == Fraction(-1,3)
c3 = rationnel([1,0], 3) == Fraction(1)          # cycle 1 -> 2 -> 1 : montee puis descente
c4 = rationnel([1], 7) == Fraction(-1,5)
for nom, ok, v in (("C1 boucle p=3 -> x = -1", c1, rationnel([1],3)),
                   ("C2 boucle p=5 -> x = -1/3", c2, rationnel([1],5)),
                   ("C3 mot (montee,descente) -> 1", c3, rationnel([1,0],3)),
                   ("C4 boucle p=7 -> x = -1/5", c4, rationnel([1],7))):
    print(f"  {nom:32s} : {'PASS' if ok else 'FAIL'}   {v}")
assert c1 and c2 and c3 and c4, "canaris en echec"

print("\n" + "="*94)
print("P1/P2 — LA BOUCLE DU §95 SE REALISE-T-ELLE EN ENTIER ?")
print("="*94)
print(f"  {'p':>4} {'x = 1/(2-p)':>14} {'entier ?':>10} {'realisation':>28}")
for p in (3,5,7,9,11,13):
    x = rationnel([1], p)
    est = (x.denominator == 1)
    real = "cycle negatif trivial {-1}" if (est and p==3) else ("—" if not est else "?")
    print(f"  {p:>4} {str(x):>14} {('*** OUI ***' if est else 'non'):>10} {real:>28}")
print("  -> l'obstruction n'a de realisation entiere que pour p=3, et c'est le cycle {-1}.")
print("     Pour tout autre p : *** FANTOME *** — aucun entier a cet endroit.")

print("\n" + "="*94)
print("P3/P4 *** LE TEST *** COMBIEN DE CYCLES FAUTIFS SONT DES FANTOMES ?")
print("="*94)
print(f"  {'p':>4} {'k':>4} {'cycles fautifs trouves':>24} {'realises en entiers':>21} {'fantomes':>10}")
REELS = {}
for p in (3, 5):
    for k in (6, 8, 10):
        tr, s = tous_cycles_fautifs(k, p)
        reels = []
        for cle,(ch,bits,L,j) in tr.items():
            x = rationnel(bits, p)
            if x is not None and x.denominator == 1: reels.append((int(x), L, j))
        REELS[(p,k)] = reels
        print(f"  {p:>4} {k:>4} {len(tr):>24} {len(reels):>21} {len(tr)-len(reels):>10}")
print()
print("  -> si la quasi-totalite sont des fantomes, l'obstruction du §80 est un MIRAGE :")
print("     elle bloque la methode sans correspondre a rien dans les entiers.")

print("\n" + "="*94)
print("P5 — CONTROLE : LES CYCLES ENTIERS TROUVES SONT-ILS LES CONNUS ?")
print("="*94)
connus = {1, -1, -5, -7, -17, -25, -37, -55, -41, -61, -91}
for (p,k), R in sorted(REELS.items()):
    if p != 3: continue
    vals = sorted({v for v,_,_ in R})
    inconnus = [v for v in vals if v not in connus]
    print(f"  p=3 k={k:>3} : entiers obtenus {vals[:10]}")
    print(f"            hors des cycles connus : {inconnus if inconnus else 'AUCUN'}")
print("  -> tout entier hors de la liste connue serait une ERREUR de code (ou une decouverte,")
print("     ce qui pour un cycle de longueur <= 12 est exclu par la verification a 2^68).")
