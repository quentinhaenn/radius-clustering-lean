# Plan: Lean 4 formalisation of radius-constrained clustering ⇔ MDS

Date: 2026-11-23. Status: J0 done; J1 definitions written, statements of T3a, T2 and T3b written
with `sorry` and awaiting review (§7). No proof yet. Statements about other repositories
come from automated reading of their files through the GitHub API and must be re-checked before
being cited in any public document.

Certainty levels: **[V]** verified in a source, **[D]** deduced, **[U]** uncertain.

## 1. Decisions

- Formalise the reductions in **both directions**: MDS ≤ clustering (carries algorithmic results over
  to MDS/SAT) and clustering ≤ MDS (carries lower bounds, settles membership in NP).
- **General case: `d` and `τ` are real** (or any linear order). The specialisation to ℕ exists only
  for statements meant for pequalnp, tied to the general case by an order-invariance lemma.
- **Hypotheses faithful to Def. 1.2 of the thesis**: symmetry and `d x x = 0` (no triangle
  inequality), plus `0 ≤ τ`. The weaker `d x x ≤ τ` is only a generalisation lemma.
- Main goal: propose statements to pequalnp if possible. The repository stays useful without that.
- Order of work: combinatorics first, then thesis chapter 4 (axiomatic analysis), then a Python
  prototype that searches for counterexamples.

## 2. Mathematical specification

**Data.** A finite set `X`, `d : X → X → α` (α = ℝ, or a linear order), `τ : α` with `0 ≤ τ`,
symmetry, `d x x = 0`.

- Threshold graph `G_τ = fromRel (fun x y => d x y ≤ τ)` (x ~ y iff x ≠ y and d x y ≤ τ).
- `S` dominates `G` if `∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v`.
- Clustering into at most `k` clusters: `f : X → Fin k`; clusters are the non-empty fibres, unused labels allowed.
- Radius constraint (Def. 1.10, centre inside its cluster):
  `∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ`.
- "Exactly k": `f` is surjective.

**Target theorems.**

- **T3a (pivot, decision version "at most k").** For every `k`:
  (∃ f : X → Fin k valid) ⇔ (∃ S, |S| ≤ k ∧ S dominates G_τ).
- **T1 (Th. 3.1, ⇒, optimisation version).** The minimum number of clusters (Def. 1.11) equals γ(G_τ).
- **T2 (Th. 3.1, ⇐).** For every finite graph G, with `d_G(u,u) = 0`, `d_G = 1` on edges and `2`
  elsewhere: `G_1(d_G) = G`, `d_G` is a metric, and γ(G) is the minimum number of clusters of
  (V, d_G, 1).
- **T2' (strict reduction).** The centres of a valid clustering of (V, d_G, 1) form a dominating set
  of size at most the number of non-empty clusters. The instance size is preserved.
- **T3b ("exactly k" refinement).** For `k ≤ n`, a valid surjective clustering exists iff a valid
  clustering into at most k exists. Proof idea: detaching a non-centre point of a cluster of size ≥ 2
  as a singleton does not increase the radius. Edge cases: `k = 0`, `k > n`.
- **T4 (corrected Th. 3.4, Prop. 3.5).** `t ↦ γ(G_t)` is antitone; for `1 ≤ k ≤ n`,
  `R*_k = min {t ∈ T | γ(G_t) ≤ k}` (T = values taken by d), and the "exactly k" optimum equals the
  "at most k" optimum. The partition derived from an MDS may have fewer than k clusters: refine it
  (T3b). Prop. 3.5: `R*_1 = min_y max_x d(y,x)`.
  Example of Fig. 3.4, checkable by computation on `Fin 4`: R*_1 = 4, R*_2 = 1, R*_3 = 1 (for
  instance `{{x1,x3},{x2},{x4}}`), R*_4 = 0. The printed "P*_3" has 4 clusters: it is P*_4.
- **T5 (optional, polynomial time).** DS ≤p CLUST and CLUST ≤p DS on binary encodings.
- **T6 (optional, conditional).** For every `α : ℕ → ℝ`, H_DS(α) ⇒ H_CLUST(α) (inapproximability),
  where the Dinur–Steurer hypothesis is an explicit `Prop` **argument**, never an `axiom`.

**Unification [D].** The decision problems attached to Def. 1.11 and Def. 3.1 ("at most k") are the
same language: only the optimised quantity differs.

**Rigour note.** The MDS → clustering reduction of Th. 3.1 defines `d` on pairs of distinct vertices;
the diagonal comes from Def. 1.2 (i). Lean needs a total function:
`d u v = if u = v then 0 else if G.Adj u v then 1 else 2`.

## 3. Lean 4 / Mathlib modelling

- Points: `{X : Type} [Fintype X] [DecidableEq X]` for the core; `Fin n` for the "gap" versions.
- Dissimilarity: `d : X → X → α` with `[LinearOrder α]` (not a `MetricSpace`). ℕ only for pequalnp
  statements.
- Threshold graph: `SimpleGraph.fromRel` [V] (symmetrisation included).
- Domination: **absent from Mathlib** at the pinned commit [V, grep over `Combinatorics/SimpleGraph`].
  Define it here: `IsDominating G S := ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v`. A candidate for a later
  Mathlib contribution.
- Partitions: `f : X → Fin k` with the constraint written inline; optional bridge lemma to
  `Finpartition`.
- Avoid `sInf`: state optimum equalities as `∀ k, (…) ↔ (…)`.
- Pitfalls: `sInf ∅ = 0` in ℕ, empty clusters, losing the centre → point direction without symmetry,
  distinctness of centres when going from clusters to centres, elaboration cost of `Fin n → Fin k`.
- Avoid `native_decide` everywhere (forbidden on the pequalnp side).

## 4. Milestones

Common criterion: `lake build` without `sorry`, and a check file that prints the axioms of every key
theorem (limited to `propext`, `Classical.choice`, `Quot.sound`).

- **J0.** Install `elan`, `lake exe cache get`, empty `lake build`; GitHub Actions CI; local copy of
  the pequalnp checker to test gap-format files [U].
- **J1.** Definitions and basic API: threshold graph, `IsDominating`, valid clustering.
- **J2.** T3a, then T1, T2 and T2'.
- **J3.** T3b and edge cases.
- **J4.** T4, Fig. 3.4 by computation, and the order-invariance lemma (ℝ → ℕ).
- **J5.** "Gap" versions: one theorem, everything inline, Mathlib only, accepted by the local
  pequalnp checker.
- **Gate before J6.** Choice of complexity formalism: (a) pequalnp's, (b) cslib-frontier's,
  (c) Mathlib alone. Recommendation: (a), since the goal is pequalnp.
- **J6 (optional).** T5 with Turing machines: very uncertain cost.
- **J7 (optional).** Conditional T6.

## 5. Compatibility with pequalnp

A gap statement is read against Mathlib and `PEqualNP/Defs` only: every definition (domination, valid
clustering) must be written **inline**. One file = one theorem; helpers in a namespace of the same
name; no `sorry`, `native_decide`, `#` command, `macro`, `notation`, `elab` or string literals; a
custom type or instance triggers human review. Statements involving polynomial time need graph
encodings that do not exist in their repository.

## 6. Relation to existing work

- [cslib-frontier](https://github.com/cslib-community/cslib-frontier) [V for the existence of the
  repository and file; content not re-read by me]: `KCenter/DominatingSet.lean` (distances 0/1/2,
  "dominating set of size ≤ k iff k-center radius ≤ 1", Hsu–Nemhauser gap), NP-completeness of DS.
- [atlas-lean](https://github.com/facebookresearch/atlas-lean): domination on `SimpleGraph`,
  "wanted" k-center statements, not proved.
- Isabelle: `wimmers/poly-reductions` (3SAT ≤ IS ≤ VC ≤ SetCover).
- Not found (search not exhaustive): the partition version of Def. 1.11, the non-metric direction
  clustering ≤ MDS with membership in NP, Th. 3.4.

What this repository aims to add: the partition version, the clustering ≤ MDS direction with the
thesis's exact semantics, the exact / at-most-k refinement, the corrected Th. 3.4, and the port to
pequalnp's formalism and pin.

## 7. Statements as written (J1, pending review)

| Plan | Lean name | File |
|---|---|---|
| dissimilarity (Def. 1.2) | `IsDissimilarity` | `RadiusClustering/Basic.lean` |
| threshold graph | `thresholdGraph` | idem |
| domination (Def. 1.20) | `IsDominating` | idem |
| valid clustering, at most k | `IsValidClustering` | idem |
| `d_G` | `graphDissim` (values in ℕ) | idem |
| T3a | `exists_validClustering_iff_exists_dominating` | `Pivot.lean` |
| T1 | `minClusters_iff_minDominating` | `Pivot.lean` |
| T1c (constructive) | `IsDerivedFrom`, `exists_isDerivedFrom`, `isDerivedFrom_minDominating` | `Basic.lean`, `Pivot.lean` |
| T2 (i) | `thresholdGraph_graphDissim` | `FromGraph.lean` |
| T2 (ii) | `isDissimilarity_graphDissim`, `graphDissim_eq_zero_iff`, `graphDissim_comm`, `graphDissim_triangle` | idem |
| T2 (iii) | `exists_dominating_iff_exists_validClustering_graphDissim` | idem |
| T3b | `exists_surjective_validClustering_iff` (+ edge case `not_surjective_of_card_lt`) | `Exact.lean` |
| T3b + T3a | `exists_surjective_validClustering_iff_exists_dominating` | idem |

Modelling choices made at J1:

- Order type: `[LinearOrder α] [Zero α]`, covering ℝ and ℕ at once; no algebraic structure needed.
- Reviewed statements assume the full Def. 1.2, bundled as `IsDissimilarity d` (zero diagonal,
  non-negativity, symmetry), plus `0 ≤ τ`, even where the proof uses less (T3b needs neither
  symmetry nor non-negativity). Versions with fewer hypotheses may exist as internal lemmas; they
  are not part of the reviewed surface. (Decided at review, replacing "minimal hypotheses".)
- `graphDissim` is ℕ-valued (the pequalnp target); a real-valued copy is a cast.
- Files are not Lean `module`s (the build warns about it); revisit at J5 if pequalnp requires it.

Tooling (J0): `scripts/check_axioms.sh` fails on any axiom other than `propext`,
`Classical.choice`, `Quot.sound`; `sorryAx` is only a warning until `STRICT=1`, which CI will set
once the J1–J3 proofs are done. The local copy of the pequalnp checker is deferred to J5.

## 8. First session

Install `elan`, run `lake exe cache get` then an empty `lake build`. Then write, with provisional
`sorry`, the exact statements of T3a, T2 and T3b, and **have them reviewed** before any proof: this
is where paper/Lean discrepancies are decided.
