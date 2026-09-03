#!/usr/bin/env python3
# BRECHE-049 — LE TEST DES FANTOMES AJOUTE A LA METHODE DU §80 : REFUTATION CONSTRUCTIVE.
#
# CE QUE J'AI PROPOSE (fin du §96) : "filtrer les cycles fantomes du graphe, puis chercher
# une fonction de Lyapunov sur ce qui reste".
#
# POURQUOI C'EST FAUX (filtre a la main, avant tout code). Avec V(x) = x f(x mod 2^k) et
# g = log f, la condition devient  g(r) - g(r') > w  sur CHAQUE ARETE. En faisant le tour
# d'un cycle de restes, g REVIENT SUR LUI-MEME, donc la somme des w doit etre negative.
# *** Cela ne depend nullement de savoir si les ENTIERS reviennent. *** Chaque arete est
# realisee par un vrai entier, donc chaque contrainte est legitime. Un cycle "fantome"
# impose une contrainte parfaitement reelle sur f.
#
# MAIS JE NE ME CONTENTE PAS DE L'ARGUMENT : je CONSTRUIS le filtre, j'en tire la fonction,
# et je la TESTE SUR DE VRAIS ENTIERS. Si elle echoue, c'est refute EN DUR.
#
# PREDICTIONS (NASA) :
#  P1  Chaque arete d'un cycle fantome est realisee par un vrai entier. Prediction : oui,
#      par construction du graphe (chaque arete vient d'un relevement).
#  P2  En filtrant les fantomes, le systeme devient satisfiable et on obtient un f.
#      Prediction : oui — moins de contraintes.
#  P3  *** LE TEST *** Ce f fait-il decroitre V sur de VRAIS entiers ? Prediction : NON,
#      et j'exhiberai un contre-exemple explicite. Si f marchait, Collatz serait demontre.
#  P4  CONCLUSION : aucune altitude a quotient FINI ne peut exister, pour aucun k, et la
#      raison est la FINITUDE du quotient (Z/2^k a des cycles que Z n'a pas).
#  P5  CONTROLE : sans filtrage, le systeme est insatisfiable (c'est le §80).
from math import log, log2
from fractions import Fraction

def graphe(k, p=3):
    M = 1 << k; lm = log(p/2.0); ld = log(0.5); ar=[]
    for r in range(2*M):
        u = r % M
        if r % 2 == 1: ar.append((u, ((p*r+1)//2) % M, lm, r))
        else:          ar.append((u, (r//2) % M, ld, r))
    return M, ar

def bellman(M, ar):
    """renvoie g si le systeme g(u)-g(v) > w est satisfiable, sinon None"""
    A=[(u,v,-w) for u,v,w,_ in ar]
    d=[0.0]*M
    for _ in range(M+1):
        chg=False
        for u,v,c in A:
            if d[u]+c < d[v]-1e-12: d[v]=d[u]+c; chg=True
        if not chg: return d
    return None

def rationnel(bits, p=3):
    a=Fraction(1); c=Fraction(0)
    for b in bits:
        if b: a,c = a*p/2, (c*p+1)/2
        else: a,c = a/2, c/2
    return None if a==1 else c/(1-a)

def T(x, p=3): return x//2 if x%2==0 else (p*x+1)//2

print("="*94); print("CANARIS"); print("="*94)
k = 8; M, ar = graphe(k)
c1 = bellman(M, ar) is None                       # §80 : insatisfiable
c2 = all(0 <= u < M and 0 <= v < M for u,v,_,_ in ar)
c3 = rationnel([1]) == Fraction(-1)
c4 = T(7) == 11
print(f"  C1 sans filtrage : insatisfiable (=§80)  : {'PASS' if c1 else 'FAIL'}")
print(f"  C2 aretes bien dans Z/2^k                : {'PASS' if c2 else 'FAIL'}")
print(f"  C3 boucle -> x = -1                      : {'PASS' if c3 else 'FAIL'}")
print(f"  C4 T(7) = 11                             : {'PASS' if c4 else 'FAIL'}")
assert c1 and c2 and c3 and c4

print("\n" + "="*94)
print("P1 — CHAQUE ARETE D'UN CYCLE FANTOME EST-ELLE REALISEE PAR UN VRAI ENTIER ?")
print("="*94)
# la boucle fantome de p=5 : point fixe -1/3. Verifions ses aretes pour p=3 sur un cycle
# fantome quelconque : on prend la boucle en 2^k-1 (REELLE pour p=3) et une arete au hasard
print("  Chaque arete (u -> v) du graphe provient d'un relevement r dans Z/2^(k+1) :")
print("  il existe donc une INFINITE d'entiers x = r mod 2^(k+1), et pour chacun")
print("  x mod 2^k = u et T(x) mod 2^k = v. L'arete est donc TOUJOURS realisee.")
ok = True
import random
random.seed(0)
for _ in range(20000):
    u,v,w,r = random.choice(ar)
    x = r + (1 << (k+1)) * random.randrange(1, 10**6)
    if (x % M) != u or (T(x) % M) != v: ok = False; break
print(f"  verification sur 20 000 aretes tirees au hasard : {'PASS — toutes realisees' if ok else 'FAIL'}")

print("\n" + "="*94)
print("P2 — EN FILTRANT LES FANTOMES, OBTIENT-ON UN f ?")
print("="*94)
# on retire les aretes de la boucle fantome... mais pour p=3 la boucle est REELLE.
# on prend donc p=7, ou 100% des cycles fautifs sont des fantomes (§96).
p = 7; k = 8
M7, ar7 = graphe(k, p)
print(f"  p={p}, k={k} : §96 a mesure 100 % de fantomes parmi les cycles fautifs.")
print(f"  sans filtrage : {'insatisfiable' if bellman(M7, ar7) is None else 'satisfiable'}")
# filtrage : on retire les aretes du point fixe (la boucle fantome)
f7 = (-pow((p-2) % M7, -1, M7)) % M7
ar7f = [(u,v,w,r) for u,v,w,r in ar7 if not (u == f7 and v == f7)]
g = bellman(M7, ar7f)
print(f"  apres retrait de la boucle fantome en {f7} : "
      f"{'SATISFIABLE — on obtient un f' if g is not None else 'toujours insatisfiable'}")

print("\n" + "="*94)
print("P3 *** LE TEST *** CE f FAIT-IL DECROITRE V SUR DE VRAIS ENTIERS ?")
print("="*94)
if g is None:
    print("  (systeme toujours insatisfiable meme apres filtrage : le filtre ne suffit pas)")
    # on retire alors gloutonnement jusqu'a satisfiabilite
    ex = set()
    while bellman(M7, [(u,v,w,r) for u,v,w,r in ar7 if u not in ex and v not in ex]) is None and len(ex) < 300:
        # trouver un temoin
        A=[(u,v,-w) for u,v,w,_ in ar7 if u not in ex and v not in ex]
        d=[0.0]*M7; par=[-1]*M7; dern=-1
        for _ in range(M7+1):
            dern=-1
            for u,v,c in A:
                if d[u]+c < d[v]-1e-12: d[v]=d[u]+c; par[v]=u; dern=v
            if dern==-1: break
        if dern==-1: break
        x=dern
        for _ in range(M7): x=par[x] if par[x]!=-1 else x
        ex.add(x)
    ar7g = [(u,v,w,r) for u,v,w,r in ar7 if u not in ex and v not in ex]
    g = bellman(M7, ar7g)
    print(f"  apres retrait GLOUTON de {len(ex)} restes : "
          f"{'satisfiable' if g is not None else 'toujours pas'}")
if g is not None:
    import math
    V = lambda x: x * math.exp(g[x % M7]) if x > 0 else None
    ech = [x for x in range(1, 60000) if (x % M7) not in (ex if 'ex' in dir() else set())]
    viol = 0; ex1 = None
    for x in ech[:40000]:
        y = T(x, p)
        if y <= 0: continue
        if 'ex' in dir() and (y % M7) in ex: continue
        if V(y) >= V(x):
            viol += 1
            if ex1 is None: ex1 = (x, y, V(x), V(y))
    print(f"  entiers testes : {min(len(ech),40000)} | V ne decroit PAS : {viol}")
    if ex1:
        print(f"  contre-exemple : x={ex1[0]}, T(x)={ex1[1]}, V(x)={ex1[2]:.4g}, V(T(x))={ex1[3]:.4g}")
    print(f"  -> {'*** LE f OBTENU NE MARCHE PAS SUR LES ENTIERS : le filtre est REFUTE ***' if viol else '*** il marche ?! a re-examiner ***'}")

print("\n" + "="*94)
print("P4 — LA CONCLUSION")
print("="*94)
print("  Un cycle du graphe des restes impose une contrainte sur g QUELLE QUE SOIT sa")
print("  realisation entiere, parce que g est une fonction du RESTE : en faisant le tour,")
print("  g revient sur lui-meme. Les 'fantomes' sont donc des contraintes LEGITIMES.")
print()
print("  *** AUCUNE ALTITUDE A QUOTIENT FINI x*f(x mod 2^k) NE PEUT EXISTER, pour aucun k,")
print("      et la raison n'est pas Collatz : c'est la FINITUDE DU QUOTIENT. ***")
print("      Z/2^k possede des cycles que Z n'a pas ; toute fonction du reste en herite.")
print()
print("  Echappatoire : il faudrait que k CROISSE avec x — c'est-a-dire ne plus compresser")
print("  du tout. On retombe sur le vecteur de parite complet (§75), donc sur 'presque tous'.")
