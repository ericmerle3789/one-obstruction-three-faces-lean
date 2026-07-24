# Lemme de séparation du contenu adélique
### La falaise démontrée — pourquoi le contenu ne vit que sur les répétitions

**Session 2026-07-24 · protocole A.R.E.S. · vérification machine : `tests_math/test_REQ-MATH-019_lemme_separation.py` (identités exactes 713/713 et 604/604 ; corollaire 560/560 ; sortie `findings/OUT_REQ-MATH-019.txt`).**
**Statut : démontré à la main + vérifié machine en arithmétique entière exacte. Lean : à faire. Antériorité (repo Macindoe) : à vérifier avant tout usage public.**

---

## 0. Cadre et notations

Mot (profil) `P = (m_0..m_{p-1} | s_0..s_{p-1})`, entrées ≥ 1 ; `n = Σm`, `S = Σs`, `K = S+n`, serrure `q = 2^K − 3^n` (toujours impair et premier à 3). Numérateur de rotation :

```
R_0(P) = Σ_t 3^{M_t} · 2^{Σ_{u<t} σ_u} · (2^{s_t} − 1),   M_t = Σ_{u>t} m_u,   σ_u = s_u + m_{u+1 mod p}.
```

**Contenu** : `C(P) = log gcd(q, R_0) / log |q| ∈ [0,1]` — invariant par rotation (corollaire de la récurrence de transport L-A1 : pour `d | q`, `R_{r+1} ≡ unité·R_r (mod d)`). `C = 1 ⟺ q | R_0 ⟺ cycle`. Lecture point fixe : `x_P = R_0/q` est LE point fixe du lacet affine `F_P` ; `den(x_P) = |q|/gcd` ; `C` mesure la fonte du dénominateur (la jauge décimal→entier).

**Voisin adjacent** : même serrure `q`, une unité déplacée entre deux lettres consécutives :
- *s-transfert en i* : `s_i → s_i+1`, `s_{i+1} → s_{i+1}−1` (0 ≤ i ≤ p−2, s_{i+1} ≥ 2) ;
- *m-transfert en i* : `m_i → m_i+1`, `m_{i+1} → m_{i+1}−1` (m_{i+1} ≥ 2).

## 1. Théorème (formules de différence)

**T1 (s-transfert, tout i ∈ [0, p−2]) :**
```
R_0(P') − R_0(P) = 3^{M_{i+1}} · 2^{S_i + s_i} · (3^{m_{i+1}} − 2^{m_{i+1}})
```

**T2 (m-transfert, i ∈ [1, p−2]) :**
```
R_0(P') − R_0(P) = − 3^{M_i − 1} · 2^{S_i} · (2^{s_i} − 1)
```
*(`S_i = Σ_{u<i} σ_u`. Le cas de bord i = 0 du m-transfert touche le terme d'enroulement `σ_{p−1}` et n'a pas de forme close — on le ramène à l'intérieur par rotation, licite car la divisibilité par tout `d | q` est invariante par rotation. Première formule i=0 candidate REJETÉE par la vérification machine, conformément au protocole ; la réduction par rotation est vérifiée 605/605.)*

### Démonstration de T1 (à la main)

Le transfert préserve `σ_i + σ_{i+1}` donc `S_t` pour `t ≥ i+2`, et ne touche ni `M_t` ni les termes `t ≤ i−1`. Seuls bougent les termes `i` et `i+1` :
- terme i : `(2^{s_i+1}−1) − (2^{s_i}−1) = 2^{s_i}` → contribution `3^{M_i} 2^{S_i} 2^{s_i}` ;
- terme i+1 : `S_{i+1}` monte de 1 et `s_{i+1}` descend de 1 :
  `2^{S_{i+1}+1}(2^{s_{i+1}−1}−1) − 2^{S_{i+1}}(2^{s_{i+1}}−1) = 2^{S_{i+1}}[(2^{s_{i+1}}−2) − (2^{s_{i+1}}−1)] = −2^{S_{i+1}}`
  → contribution `−3^{M_{i+1}} 2^{S_{i+1}}`.

Somme, avec `M_i = M_{i+1} + m_{i+1}` et `S_{i+1} = S_i + s_i + m_{i+1}` :
`Δ = 3^{M_{i+1}} 2^{S_i+s_i} (3^{m_{i+1}} − 2^{m_{i+1}})`. ∎

### Démonstration de T2 (à la main)

Pour `i ≥ 1` : `M_i` descend de 1 ; `σ_{i−1}` monte de 1 et `σ_i` descend de 1, donc seul `S_i` monte de 1 (les `S_t`, `t ≥ i+1`, voient `σ_{i−1}+σ_i` inchangé). Seul le terme `i` bouge :
`3^{M_i−1} 2^{S_i+1}(2^{s_i}−1) − 3^{M_i} 2^{S_i}(2^{s_i}−1) = 3^{M_i−1} 2^{S_i} (2^{s_i}−1)(2−3) = −3^{M_i−1} 2^{S_i}(2^{s_i}−1)`. ∎

## 2. Corollaire (séparation du contenu)

Tout `d | q` est premier à 6. Si `d` divise `R_0(P)` **et** `R_0(P')`, alors `d | Δ`, et les facteurs `3^•`, `2^•` étant des unités mod d :

> **Le contenu partagé par deux mots voisins divise la mini-couture de la lettre locale :**
> `gcd(q, R_0(P), R_0(P'))` divise `3^{m_{i+1}} − 2^{m_{i+1}}` (s-transfert) resp. `2^{s_i} − 1` (m-transfert).

Auto-similarité : les portes de partage entre voisins sont **de la même espèce que la grande serrure** (`2^a − 3^b`, `2^a − 1`), mais à l'échelle d'une lettre. Cas extrême : `m_{i+1} = 1` donne `3−2 = 1` — **isolation totale** (aucun contenu partagé) ; mesuré : 553/560 tirages à partage = 1.

**Conséquence (la falaise est un théorème).** Une tour de contenu (ex. mot répété `B^j`, `C → 1` par la loi L-A2) ne « déborde » sur aucun voisin : tout le contenu au-delà de la mini-couture locale disparaît en un seul transfert. Vérifié frontalement : la tour `([1,2]|[3,1])^3` (gcd 20569, C = 0.683) partage au plus **1** avec chacun de ses voisins adjacents.

## 3. Reformulation point fixe (loi L-A2 en une ligne)

`F_{B^j} = (F_B)^j` et une application affine de rapport `≠ 1` a un unique point fixe ⇒ `x_{B^j} = x_B` : la répétition **fige le point fixe** (vérifié : dénominateur constant j = 2..5 sur trois bases). D'où `den(x_{B^j}) = q_red(B)` et `gcd(q_P, R_0(P)) = |q_P|/q_red(B)` — la loi des mots répétés retrouvée en une ligne. La répétition fabrique du contenu *sans créer de cycle* (descente L-A4) ; le paysage du contenu est : fond aléatoire + tours isolées sur le réseau des répétitions, **sans épaulements** (ceci est le théorème du présent document).

## 4. Ce qui est démontré / ce qui reste

**Démontré (main + machine)** : T1, T2, corollaire de séparation, réduction des bords par rotation, figement du point fixe sous répétition.
**Reste (le mur, sous sa forme la plus fine)** : qu'aucun mot **apériodique** n'atteint `C = 1`. La séparation contraint désormais toute tour hypothétique : elle serait un pic isolé dont *chaque* voisin retombe au fond — une conspiration sans voisinage, ce que le comptage (marge REQ-MATH-014) rend exponentiellement rare mais que seule une rigidité de type ×2×3 exclura.
**Suites naturelles** : formaliser T1/T2 en Lean (identités entières finies — très faisable) ; vérifier l'antériorité côté Macindoe ; proposer L-A5 (contenu + séparation) à la note commune après retour de Ben.
