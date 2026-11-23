# Cadrage : formalisation Lean 4 des réductions clustering sous contrainte de rayon ⇔ MDS

Date : 2026-11-23. Statut : plan, rien n'est encore formalisé. Les affirmations sur d'autres dépôts
viennent d'une recherche automatisée (lecture des fichiers via l'API GitHub) et sont à revérifier
avant d'être citées dans un document public.

Niveaux de certitude : **[V]** vérifié dans une source, **[D]** déduit, **[I]** incertain.

## 1. Décisions prises

- Formaliser les réductions dans les **deux sens** : MDS ≤ clustering (transporte les résultats
  algorithmiques) et clustering ≤ MDS (transporte les bornes inférieures, fixe l'appartenance à NP).
- **Cas général : `d` et `τ` réels** (ou ordre total quelconque). La spécialisation sur ℕ n'existe que
  pour les énoncés destinés à pequalnp, reliée au cas général par un lemme d'invariance d'ordre.
- **Hypothèses fidèles à la déf. 1.2** : symétrie et `d x x = 0` (pas d'inégalité triangulaire), et
  `0 ≤ τ`. La forme plus faible `d x x ≤ τ` n'est qu'un lemme de généralisation.
- Objectif principal : proposer des énoncés à pequalnp si possible. Le dépôt reste utile sans cela.
- Ordre : combinatoire d'abord, puis chapitre 4 de la thèse (analyse axiomatique), puis prototype
  Python de recherche de contre-exemples.

## 2. Spécification mathématique

**Données.** `X` fini, `d : X → X → α` (α = ℝ, ou ordre total), `τ : α` avec `0 ≤ τ`,
symétrie, `d x x = 0`.

- Graphe de seuil `G_τ = fromRel (fun x y => d x y ≤ τ)` (x ~ y ⇔ x ≠ y ∧ d x y ≤ τ).
- `S` domine `G` si `∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v`.
- Clustering en au plus `k` clusters : `f : X → Fin k` (clusters vides permis).
- Contrainte de rayon (déf. 1.10, centre dans son cluster) :
  `∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ`.
- « Exactement k » : `f` surjective.

**Théorèmes cibles.**

- **T3a (pivot, version décision « au plus k »).** Pour tout `k` :
  (∃ f : X → Fin k valide) ⇔ (∃ S, |S| ≤ k ∧ S domine G_τ).
- **T1 (Th. 3.1, ⇒, version optimum).** Le nombre minimal de clusters (déf. 1.11) égale γ(G_τ).
- **T2 (Th. 3.1, ⇐).** Pour tout graphe fini G, avec `d_G(u,u) = 0`, `d_G = 1` sur les arêtes et `2`
  ailleurs : `G_1(d_G) = G`, `d_G` est une métrique, et γ(G) = nombre minimal de clusters de
  (V, d_G, 1).
- **T2' (réduction stricte).** Les centres d'un clustering valide de (V, d_G, 1) forment un ensemble
  dominant de cardinal ≤ nombre de clusters non vides. La taille d'instance est conservée.
- **T3b (« exactement k », raffinement).** Pour `k ≤ n`, existence d'un clustering valide surjectif
  ⇔ existence d'un clustering valide en au plus k. Preuve : détacher un point non-centre d'un cluster
  de taille ≥ 2 en singleton ne fait pas croître le rayon. Cas limites : `k = 0`, `k > n`.
- **T4 (Th. 3.4 corrigé, Prop. 3.5).** `t ↦ γ(G_t)` est antitone ; pour `1 ≤ k ≤ n`,
  `R*_k = min {t ∈ T | γ(G_t) ≤ k}` (T = valeurs prises par d), et optimum « exactement k » = optimum
  « au plus k ». La partition tirée d'un MDS peut avoir moins de k clusters : la raffiner (T3b).
  Prop. 3.5 : `R*_1 = min_y max_x d(y,x)`.
  Exemple de la fig. 3.4, vérifiable par calcul sur `Fin 4` : R*_1 = 4, R*_2 = 1, R*_3 = 1 (par
  exemple `{{x1,x3},{x2},{x4}}`), R*_4 = 0. La partition imprimée « P*_3 » a 4 clusters : c'est P*_4.
- **T5 (option, temps polynomial).** DS ≤p CLUST et CLUST ≤p DS, sur encodages binaires.
- **T6 (option, conditionnel).** Pour toute `α : ℕ → ℝ`, H_DS(α) ⇒ H_CLUST(α) (inapproximabilité),
  où l'hypothèse de Dinur–Steurer est un **argument** `Prop` explicite, jamais un `axiom`.

**Remarque d'unification [D].** Les problèmes de décision associés aux déf. 1.11 et 3.1 (« au plus k »)
sont le même langage : seule la quantité optimisée change.

**Remarque de rigueur.** La réduction MDS → clustering du Th. 3.1 définit `d` sur les paires de
sommets distincts ; la diagonale vient de la déf. 1.2 (i). Lean demande une fonction totale :
`d u v = if u = v then 0 else if G.Adj u v then 1 else 2`.

## 3. Modélisation Lean 4 / Mathlib

- Points : `{X : Type} [Fintype X] [DecidableEq X]` pour le cœur ; `Fin n` pour les versions « gap ».
- Dissimilarité : `d : X → X → α` avec `[LinearOrder α]` (pas de `MetricSpace`). ℕ seulement pour les
  énoncés pequalnp.
- Graphe de seuil : `SimpleGraph.fromRel` [V] (symétrisation incluse).
- Domination : **absente de Mathlib** au commit épinglé [V, grep sur `Combinatorics/SimpleGraph`]. À
  définir ici : `IsDominating G S := ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v`. Candidat à une contribution à
  Mathlib plus tard.
- Partitions : `f : X → Fin k` avec la contrainte en ligne ; lemme-pont optionnel vers `Finpartition`.
- Éviter `sInf` : énoncer les égalités d'optimum sous la forme `∀ k, (…) ↔ (…)`.
- Pièges : `sInf ∅ = 0` dans ℕ, clusters vides, perte du sens centre → point sans symétrie,
  distinction des centres lors du passage clusters → centres, coût d'élaboration de `Fin n → Fin k`.
- `native_decide` à éviter partout (interdit côté pequalnp).

## 4. Jalons

Critère commun : `lake build` sans `sorry`, et un fichier de contrôle qui affiche les axiomes de
chaque théorème clé (limités à `propext`, `Classical.choice`, `Quot.sound`).

- **J0.** Installer `elan`, `lake exe cache get`, `lake build` à vide ; CI GitHub Actions ; copie
  locale du vérificateur de pequalnp pour tester les fichiers au format gap [I].
- **J1.** Définitions et API de base : graphe de seuil, `IsDominating`, clustering valide.
- **J2.** T3a, puis T1, T2 et T2'.
- **J3.** T3b et cas limites.
- **J4.** T4, la fig. 3.4 par calcul, et le lemme d'invariance d'ordre (ℝ → ℕ).
- **J5.** Versions « gap » : un théorème, tout en ligne, Mathlib seule, acceptées par le vérificateur
  local de pequalnp.
- **Porte avant J6.** Choix du formalisme de complexité : (a) celui de pequalnp, (b) celui de
  cslib-frontier, (c) Mathlib seule. Recommandation : (a), car le but est pequalnp.
- **J6 (option).** T5 en machines de Turing : coût très incertain.
- **J7 (option).** T6 conditionnel.

## 5. Compatibilité avec pequalnp

Un énoncé de gap est lu contre Mathlib et `PEqualNP/Defs` uniquement : toute définition (domination,
clustering valide) doit être écrite **en ligne**. Un fichier = un théorème ; helpers dans un
`namespace` du même nom ; pas de `sorry`, `native_decide`, `#`-commande, `macro`, `notation`, `elab`
ni guillemets ; un type ou une instance maison déclenche une relecture humaine. Les énoncés avec temps
polynomial exigent des encodages de graphes qui n'existent pas dans leur dépôt.

## 6. Relation aux travaux existants

- [cslib-frontier](https://github.com/cslib-community/cslib-frontier) [V pour l'existence du dépôt et
  du fichier ; contenu non relu par moi] : `KCenter/DominatingSet.lean` (distances 0/1/2,
  « dominant de taille ≤ k ⇔ rayon k-center ≤ 1 », écart de Hsu–Nemhauser), NP-complétude de DS.
- [atlas-lean](https://github.com/facebookresearch/atlas-lean) : domination sur `SimpleGraph`,
  énoncés k-center « wanted » non prouvés.
- Isabelle : `wimmers/poly-reductions` (3SAT ≤ IS ≤ VC ≤ SetCover).
- Non trouvé (recherche non exhaustive) : version partition de la déf. 1.11, sens non métrique
  clustering ≤ MDS avec appartenance à NP, Th. 3.4.

Ce que ce dépôt vise à apporter : la version partition, le sens clustering ≤ MDS avec la sémantique
exacte de la thèse, le raffinement exact / au plus k, le Th. 3.4 corrigé, et le portage au
formalisme et à l'épinglage de pequalnp.

## 7. Première session

Installer `elan`, lancer `lake exe cache get` puis `lake build` à vide. Écrire ensuite, avec `sorry`
provisoire, les énoncés exacts de T3a, T2 et T3b, et les **faire relire** avant toute preuve : c'est
là que se jouent les écarts entre papier et Lean.
