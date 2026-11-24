import RadiusClustering.Pivot

/-!
# T2: from a graph to a clustering instance (Th. 3.1, part 2)
-/

namespace RadiusClustering

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- **T2 (i).** Thresholding `graphDissim G` at `1` gives back `G`. -/
theorem thresholdGraph_graphDissim : thresholdGraph (graphDissim G) 1 = G := by
  ext u v
  simp only [thresholdGraph, SimpleGraph.fromRel_adj, graphDissim]
  by_cases h : u = v
  · subst h; simp
  · by_cases h1 : G.Adj u v
    · simp [h, h1]
    · have h2 : ¬ G.Adj v u := fun h' => h1 h'.symm
      have h3 : v ≠ u := Ne.symm h
      simp [h, h3, h1, h2]

omit [Fintype V] in
/-- **T2 (ii).** `graphDissim G` is a dissimilarity (Def. 1.2). -/
theorem isDissimilarity_graphDissim : IsDissimilarity (graphDissim G) := by
  refine ⟨fun x => by simp [graphDissim], fun x y => Nat.zero_le _, fun x y => ?_⟩
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := Ne.symm h
    have : G.Adj x y ↔ G.Adj y x := ⟨fun a => a.symm, fun a => a.symm⟩
    simp [graphDissim, h, h', this]

/-- **T2 (iii).** `G` has a dominating set of size `≤ k` iff its vertices split into at most `k`
clusters of radius `≤ 1` for `graphDissim G`. -/
theorem exists_dominating_iff_exists_validClustering_graphDissim (k : ℕ) :
    (∃ S : Finset V, S.card ≤ k ∧ IsDominating G S) ↔
      ∃ f : V → Fin k, IsValidClustering (graphDissim G) 1 f := by
  have h := exists_validClustering_iff_exists_dominating (graphDissim G) 1
    (isDissimilarity_graphDissim G) zero_le_one k
  rw [thresholdGraph_graphDissim] at h
  exact h.symm

/-- **T2c** (Th. 3.1 part 2, constructive form). The centres of a minimum valid partition of
`(V, graphDissim G, 1)` form a minimum dominating set of `G`. -/
theorem isCentreSet_minClustering_graphDissim
    {k : ℕ} (f : V → Fin k)
    (hmin : ∀ m < k, ¬ ∃ g : V → Fin m, IsValidClustering (graphDissim G) 1 g)
    (C : Finset V) (hC : IsCentreSet (graphDissim G) 1 f C) :
    IsDominating G C ∧ C.card = k ∧ ∀ S : Finset V, IsDominating G S → C.card ≤ S.card := by
  obtain ⟨hdom, hcard⟩ := hC.dominating_card (graphDissim G) 1
  rw [thresholdGraph_graphDissim] at hdom
  have hfew : ∀ S : Finset V, IsDominating G S → k ≤ S.card := by
    intro S hS
    by_contra hlt
    rw [not_le] at hlt
    have hS' : IsDominating (thresholdGraph (graphDissim G) 1) S := by
      rw [thresholdGraph_graphDissim]
      exact hS
    exact hmin _ hlt (exists_validClustering_of_dominating (graphDissim G) 1
      (fun x => by simp [graphDissim]) (isDissimilarity_graphDissim G).symm S le_rfl hS')
  have hle : C.card ≤ k := by
    rw [hcard]
    calc (Finset.univ.image f).card ≤ Fintype.card (Fin k) := Finset.card_le_univ _
      _ = k := Fintype.card_fin k
  have hCk : C.card = k := le_antisymm hle (hfew C hdom)
  refine ⟨hdom, hCk, fun S hS => ?_⟩
  rw [hCk]
  exact hfew S hS

end RadiusClustering
