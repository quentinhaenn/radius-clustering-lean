# Candidate statement for pequalnp

Status: candidate, not posted by pequalnp. Written against `PEqualNP/Defs/Base.lean` of
`brilliant-hq/pequalnp-proofs` (same Lean and Mathlib pins as this repository); it type-checks
there with `sorry`. Nothing in it uses this repository: every definition is inline.

```lean
theorem PEqualNP.Outside.L_clust_npc :
    PEqualNP.Library.NPComplete
      {x : List Bool | ∃ (M : List (List ℕ)) (k τ : ℕ),
        x = (k.bits.flatMap fun b => [true, b]) ++ [false, true] ++
            ((τ.bits.flatMap fun b => [true, b]) ++ [false, true]) ++
            M.flatMap (fun row =>
              row.flatMap (fun a => (a.bits.flatMap fun b => [true, b]) ++ [false, true]) ++
                [false, false]) ∧
        (∀ i : Fin M.length, (M.get i).length = M.length - 1 - i.val) ∧
        let d : Fin M.length → Fin M.length → ℕ := fun i j =>
          if i < j then (M.get i).getD (j.val - i.val - 1) 0
          else if j < i then (M.get j).getD (i.val - j.val - 1) 0
          else 0
        ∃ f : Fin M.length → Fin k, ∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ}
```

## Reading

An instance is `(k, τ, M)`: `M` is the strict upper triangle of an integer dissimilarity on `n`
points (row `i` holds `d(i, j)` for `j > i`), so symmetry and the zero diagonal hold by
construction. The encoding is the one pequalnp uses for SAT (`PEqualNP/Defs/Search.lean`):
binary digits as `[true, b]`, `[false, true]` ends a number, `[false, false]` ends a row. A
string is in the language when it encodes an instance with a partition into at most `k`
clusters, each with a centre inside it at dissimilarity `≤ τ` from all its points.

## Checked here (`RadiusClustering/PEqualNP/`)

- `clustLang_eq_inline`: the inline set above is `clustLang`, by `rfl`.
- `mem_clustLang_iff`: a string is in `clustLang` iff it encodes `(k, τ, d)` with `d` an
  `IsDissimilarity` and an `IsValidClustering` into at most `k` clusters.
- `encInst_injective`: an encoding determines `k`, `τ` and the rows.
- `fig34_mem_clustLang`: Fig. 3.4 is in for `k = 2, τ = 1`, out for `τ = 0`.

## SAT → dominating set (`SatGadget.lean`, intermediate lemma)

Intermediate lemmas, not reviewed by the author: the statement to trust is the final
`NPComplete` one, built only from `clustLang` (reviewed) and pequalnp's own definitions.

`satisfiable_iff_exists_dominating`: for a CNF formula `φ` in pequalnp's format whose variables
are `< N`, `φ` is satisfiable iff its gadget graph has a dominating set of size `≤ N`. Gadget:
a triangle `{(i, true), (i, false), (i, none)}` per variable, a vertex per clause adjacent to its
literals. It holds for any CNF, so the chain can start from SAT (`L031`) rather than 3-SAT.
With T2 (MDS → clustering, `graphDissim`, `τ = 1`) this gives the correctness of SAT → CLUST:
`satisfiable_iff_mem_clustLang` (`SatToClust.lean`): `φ` is satisfiable iff
`encInst N 1 (toTri (gadgetDissim φ N)) ∈ clustLang`.

The candidate statement type-checks against pequalnp's own build (clone `58845ea`, full
`lake build PEqualNP` after a check that no file runs code at compile time).

## Remaining for a proof in pequalnp's framework (done since: see the last section)

Through their `L020` (NP-completeness transfers along a reduction into NP) from `L031` (SAT):
a reduction SAT → CLUST computable in polynomial time, and CLUST ∈ NP. With their `L018`, a
polynomial-time algorithm for CLUST would then give `P = NP` inside their framework.

## Feasibility notes for the two remaining pieces (read 2026-11-24, clone `58845ea`)

pequalnp writes a reduction as a plain function on bit strings, proves its correctness as pure
mathematics, and proves polynomial time by composing proven primitives (`cpt_comp`, `cpt_pair`,
`cpt_sel`, `cpt_iterLen`, `cpt_lookup`, `cpt_loop`, `cpt_flatMapRange`, finite-state transducers;
`Library/Machines/`, `Library/Universal/PrimsCPT.lean`, `Library/SearchHelpers/`). No machine
is written by hand. Their Cook–Levin tableau is built this way, so the nested loop that writes
the `n(n-1)/2` entries of `d_G` is within reach.

- **SAT → CLUST.** Variables are arbitrary natural numbers, so one triangle per variable below
  `N` (`SatGadget.lean`) can be exponential in the length of the encoding. `ItemGadget.lean`
  indexes the gadget by the items of the encoding instead (a literal or an end of clause): block
  `{3p, 3p+1, 3p+2}` for item `p`; a literal block is a triangle, an end block is an edge
  `3p–3p+1` plus the clause vertex `3p+2`; only the first occurrence of a variable (its
  representative) is joined to the clauses, so every block costs one vertex and `k` is the number
  of items. `satisfiable_iff_itemInst_mem` (proved, no hypothesis on `φ`): `φ` is satisfiable
  iff `itemInst φ ∈ clustLang`. What remains is a string function equal to `itemInst` on
  encodings, and its polynomial time.
- **CLUST ∈ NP.** A string verifier in the style of their `SatVerifier` (witness: one label per
  point), or a reduction CLUST → SAT, then closure of NP under reductions (used for 3-SAT).
- cslib-frontier has `DominatingSet_npComplete` (no `sorry` in its directory; Lean
  `v4.36.0-rc2`, its own machine model): a blueprint only, nothing transfers as is.

## Proofs in pequalnp's framework (`pequalnp-bridge/ClustNP/`)

These files import pequalnp's modules, so they are built inside a clone of
`brilliant-hq/pequalnp-proofs` (commit `58845ea`), not by this repository's `lake build`: symlink
`RadiusClustering/` and `pequalnp-bridge/ClustNP/` into the clone's `lean/` directory, add
`[[lean_lib]] name = "RadiusClustering"` and `[[lean_lib]] name = "ClustNP"` to its
`lakefile.toml`, then `lake build ClustNP.InNP`.

- `Defs.lean`: a verifier `CV` as string functions (comparison of binary numbers, reading of
  rows, triangularity, count of centres, covering), in the style of their `SatVerifierDefs`.
  Witness: one bit per point, `true` for a centre.
- `Read.lean`, `Wf.lean`: what these functions compute on encodings; `wfI_iff`: the acceptor
  recognises exactly the strings `encInst k τ M`.
- `CPT.lean`: `cpt_CV`, the verifier runs in polynomial time (their primitives only).
- `InNP.lean`: `CV_spec` (via T3a) and **`clustLang_mem_NP : clustLang ∈ PEqualNP.Library.NP`**.
- `RedDefs.lean`: the reduction `red` as a string function: on `encodeCNF φ` it writes
  `itemInst φ` (`ItemGadget.lean`), on any other string `[]`.
- `RedItems.lean`, `RedCorrect.lean`: `red (encodeCNF φ) = itemInst φ` (`red_encodeCNF`).
- `RedCPT.lean`: `cpt_red`, polynomial time.
- `NPC.lean`: `sat_reduces_clust`, **`clustLang_npComplete`** (their `L020` from `L031`),
  `clustLang_mem_P_iff : clustLang ∈ P ↔ P = NP` (their `L018`), and
  **`PEqualNP.Outside.L_clust_npc`**, the candidate statement above, proved.

All of them depend on `propext`, `Classical.choice`, `Quot.sound` only (`CheckAxioms.lean`).
The theorem is proved against pequalnp's definitions; it has not been run through their checker
(`tools/check-lean.mjs`), and their submission format (one file, imports limited to the modules a
posted gap lists) would require inlining these files.
