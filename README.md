# radius-clustering-lean

Lean 4 / Mathlib formalisation of the equivalence between **radius-constrained clustering** and
**minimum dominating set** (MDS), in both directions.

**Status: J1–J4 proved; CLUST NP-complete in pequalnp's framework (below).** `lake build` succeeds with no `sorry`; the key theorems depend only on
`propext`, `Classical.choice` and `Quot.sound` (`STRICT=1 scripts/check_axioms.sh`, also run in
CI). Plan and the list of statements: `docs/cadrage.md` §7.

## CLUST is NP-complete, in pequalnp's framework

The decision problem CLUST (given an integer dissimilarity on `n` points as its upper triangle,
`k` and `τ`: is there a partition into at most `k` clusters, each with a centre inside it at
dissimilarity `≤ τ` from all its points?) is proved NP-complete on the definitions of
[pequalnp-proofs](https://github.com/brilliant-hq/pequalnp-proofs) (`P`, `NP`, polynomial-time
reductions on bit strings, built on Mathlib's Turing machines):

- CLUST ∈ NP, by a polynomial-time verifier;
- SAT reduces to CLUST in polynomial time, through a dominating-set gadget indexed by the items of
  the formula's encoding, then the graph dissimilarity (`1` on an edge, `2` otherwise, `τ = 1`);
- with their SAT NP-completeness (Cook–Levin, `L031`), CLUST is NP-complete, so a polynomial-time
  algorithm for CLUST is equivalent to `P = NP` in their framework (`L018`).

`pequalnp-bridge/L_clust_npc.lean` is the proof as one file in their contribution format; their
own checker accepts it (`ACCEPTED (check): PEqualNP.Outside.L_clust_npc`, axioms `propext`,
`Quot.sound`, `Classical.choice`; output in `pequalnp-bridge/checker-output.txt`). The
statement, and how to rerun the check: `docs/pequalnp.md`.

## Source and publications

- Q. Haenn, *Partitionnement sous contrainte de similarité* (Clustering under similarity
  constraints), PhD thesis, ISAE-ENSMA, 2025, in French. HAL:
  [tel-05465598](https://theses.hal.science/tel-05465598) (NNT 2025ESMA0015).
- Q. Haenn, B. Chardin, M. Baron, *Clustering Under Radius Constraints Using Minimum Dominating
  Sets*, ISMIS 2024 (27th International Symposium on Methodologies for Intelligent Systems,
  Poitiers), Lecture Notes in Computer Science 14670, Springer, pp. 14–23.
  [doi:10.1007/978-3-031-62700-2_2](https://doi.org/10.1007/978-3-031-62700-2_2),
  [hal-04533921](https://hal.science/hal-04533921).
- Q. Haenn, B. Chardin, M. Baron, *Partitionnement sous contrainte de similarité*, BDA 2024 (40e
  Conférence sur la Gestion de Données, Orléans), in French.
  [hal-04791528](https://hal.science/hal-04791528).
- Q. Haenn, B. Chardin, M. Baron, A. Hadjali, *Iterative Graph-Based Radius-Constrained
  Clustering*, Machine Learning with Graphs (MLG) Workshop at ECML PKDD 2025, Porto.
  [hal-05281748](https://hal.science/hal-05281748).
- Software: [scikit-learn-contrib/radius_clustering](https://github.com/scikit-learn-contrib/radius_clustering)
  ([hal-05039266](https://hal.science/hal-05039266)).

The thesis is the reference for definitions and statements (Def. 1.11, Def. 3.1, Th. 3.1, Th. 3.3,
Th. 3.4). This repository follows it and records, in the plan, the places where the Lean statement
has to be more explicit than the paper (for example the diagonal `d x x = 0`, and
"at most k" versus "exactly k" clusters).

## Planned content

1. Threshold graph, dominating sets, valid radius-constrained clusterings.
2. Pivot statement: a partition into at most `k` clusters of radius at most `τ` exists iff the
   threshold graph has a dominating set of size at most `k`.
3. Both reductions of Th. 3.1, the "exactly k" refinement, and the corrected breakpoint theorem
   behind the Curgraph algorithm.
4. Optional, later: polynomial-time reductions, and a conditional inapproximability corollary
   (the Dinur–Steurer hypothesis would be an explicit argument, never an axiom).

## Related formalisations

Part of the MDS-to-k-center direction already exists elsewhere, notably in
[cslib-frontier](https://github.com/cslib-community/cslib-frontier) (`KCenter/DominatingSet.lean`)
and [atlas-lean](https://github.com/facebookresearch/atlas-lean). What this repository aims to add
is the *partition* version of the problem (centre inside its cluster), the non-metric direction
clustering ≤ MDS, and the exact-versus-at-most-k refinement. See `docs/cadrage.md`.

## Toolchain

Pinned to the same Lean (`v4.36.0`) and Mathlib commit as
[pequalnp-proofs](https://github.com/brilliant-hq/pequalnp-proofs). Never run `lake update`.

## Licence

Apache-2.0, see `LICENSE`.
