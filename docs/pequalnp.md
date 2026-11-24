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

## SAT → dominating set (`SatGadget.lean`, statement not yet reviewed by the author)

`satisfiable_iff_exists_dominating`: for a CNF formula `φ` in pequalnp's format whose variables
are `< N`, `φ` is satisfiable iff its gadget graph has a dominating set of size `≤ N`. Gadget:
a triangle `{(i, true), (i, false), (i, none)}` per variable, a vertex per clause adjacent to its
literals. It holds for any CNF, so the chain can start from SAT (`L031`) rather than 3-SAT.
With T2 (MDS → clustering, `graphDissim`, `τ = 1`) this gives the correctness of SAT → CLUST.

## Remaining for a proof in pequalnp's framework

Through their `L020` (NP-completeness transfers along a reduction into NP) from `L031` (SAT):
a reduction SAT → CLUST computable in polynomial time, and CLUST ∈ NP. With their `L018`, a
polynomial-time algorithm for CLUST would then give `P = NP` inside their framework.
