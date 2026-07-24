# L'arbre jusqu'à la racine
### Méthode Merle : à chaque manque — inventaire, sinon construction, sinon on descend d'un cran

**2026-07-24 · A.R.E.S. · chaque nœud porte son artefact vérifié ou son statut honnête.**
Légende : **[ON A]** = démontré/mesuré chez nous · **[CONSTRUIT]** = assemblé ce soir · **[EXISTE AILLEURS]** = littérature · **[RACINE]** = personne, nulle part.

---

## Nœud 0 — LE BUT
**Aucun cycle non trivial positif.**
→ il faut : pour toute échelle `n`, aucune cellule `(n,K)` avec `q>0` n'héberge de mot à `q | R₀` réalisable.

## Nœud 1 — LES DEUX MOITIÉS DU PAYSAGE
- **1a. Mots structurés (répétitions).** **[ON A — kernel]** `ContentDescent.lean` : `cycle_iff` (un mot répété est un cycle ssi sa base l'est) + `gcd_climb`. Aucun cycle neuf n'y naît. **FERMÉ, gravé.**
- **1b. Mots primitifs.** → descendre.

## Nœud 2 — LES MOTS PRIMITIFS : deux régimes
- **2a. Petites échelles (finies).** **[ON A]** recensement exhaustif `n ≤ 20` (REQ-022/027) : exactement les 3 gratuits de Gersonides + l'orbite −17 + les puissances forcées. **FERMÉ par calcul.**
- **2b. Grandes échelles.** → descendre.

## Nœud 3 — GRANDES ÉCHELLES : que peut-on exclure SANS probabilité ?
- **3a. Exclusion par la taille (déterministe).** **[CONSTRUIT ce soir — REQ-030]** une cellule ne peut héberger un cycle d'élément minimal `≥ X₀` que si `q ≤ maxB/X₀`. Assemblé avec la règle d'individu (`ε_n ≥ c/n^{μ-1}`, Salikhov).
  **Portée mesurée de NOTRE chaîne : `n ≤ 76` seulement.** Cause identifiée : `maxB` est un proxy grossier — il ignore que **toutes** les rotations doivent passer la condition de taille.
  **[EXISTE AILLEURS — bien meilleur]** le vrai Product Bound exploite toutes les rotations : Hercher `k > 1.375·10¹¹`, soit ~2·10⁹ fois plus loin. **Notre assemblage est dominé par l'existant** (constat honnête).
- **3b. Au-delà de la portée déterministe.** → descendre.

## Nœud 4 — AU-DELÀ : que reste-t-il ?
- **4a. Borner l'espérance à toutes les échelles.** **[CONSTRUIT — REQ-029, L-A7]** la *règle de torsion* : `R(n) ≤ −c_gen·n + (μ−1)log₂n + C₀`, `C₀ = −5,77`. Masse de tickets bornée **par théorème pour tout n** ; queue `< 5,2·10⁻⁴` au-delà de `n = 600`. **Le kiosque ferme prouvablement.**
- **4b. Passer de « espérance ~0 » à « certitude 0 ».** → descendre. C'est le dernier nœud.

## Nœud 5 — LE DERNIER PAS : espérance → certitude
Il faut un énoncé qui vaille **par orbite individuelle**, pas en moyenne : que `R₀ mod q ≠ 0` pour *chaque* mot primitif, à *toute* échelle.

Inventaire de ce qu'on possède pour l'attaquer :
- côté fini (chiffres) : **[ON A]** séparation `T1/T2` (kernel), descente, contenu `C`, porte unique `L-A1`, obstruction locale aux premiers de la couture. **Mais** : tout cela est **aveugle au signe** (prouvé) — donc identique sur les deux rives, où le −17 existe. **Ne peut pas suffire seul.**
- côté infini (taille) : **[ON A / EXISTE AILLEURS]** mesure d'irrationalité effective (individuelle !), Product Bound, vérification Barina. **Mais** : portée **finie par nature** (nœud 3), car `ε_n` redevient minuscule aux convergents et `n^{−(μ−1)}` décroît trop lentement.
- côté couplage : **[ON A — mesuré]** REQ-028 : le couplage fini×infini est **trivial au signe** (définitionnel) et ne vit qu'à la taille asymptotique.

**→ [RACINE] Ce qui manque : une rigidité de type ×2×3 — un énoncé arithmétique individuel valable uniformément en `n`.** Personne, dans aucune branche, ne le possède pour cette classe. Furstenberg/Rudolph l'ont **sous hypothèse d'entropie positive** ; notre cas (orbites finies) est exactement le trou d'entropie nulle.

---

## Ce que la descente a démontré (le vrai résultat de la méthode)

1. **Chaque branche descendue se referme sur la même racine.** Structuré → fermé. Fini → fermé. Taille → portée finie *par nature*. Espérance → bornée mais jamais 0. Les quatre chemins convergent vers le même nœud 5.
2. **La racine n'est pas un manque d'assemblage.** Ce soir, on a *construit* deux instruments réels à partir de nos propres pièces (torsion, exclusion par taille). Ils ont amélioré la carte — pas franchi la racine. La racine est d'une **autre espèce** que tout ce qui est dans l'atelier : elle demande une rigidité individuelle uniforme, et aucune combinaison de moyennes + de bornes finies ne la produit.
3. **Corollaire méthodologique.** La méthode « construire l'ingrédient manquant » **fonctionne** — elle a produit la règle de torsion, premier énoncé trans-échelle du programme. Mais elle a une limite formelle : on ne peut assembler que ce que les pièces *engendrent*. Le nœud 5 n'est pas dans l'engendré. Il faudra une pièce venue du dehors.

## Honnêteté (protocole)
- Prédictions de REQ-030 **réfutées par la machine** : `A(n)` n'est pas constant (croît en `(3/2)ⁿ`), donc la portée annoncée `~3·10⁴` était fausse → corrigée à `76`. Consigné tel quel.
- `μ = 5.125` (Salikhov) vient du corpus local — **à re-sourcer** avant toute publication.
- Les bornes du nœud 4 portent sur l'espérance en unités-mots (majorent les unités-colliers).
