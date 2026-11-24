import RadiusClustering.PEqualNP.SatGadget
import RadiusClustering.PEqualNP.Injective
import RadiusClustering.FromGraph

/-!
# SAT → CLUST, correctness (statement not yet reviewed by the author)

The gadget graph of `φ`, turned into `graphDissim` with `τ = 1` and `k = N`, then into the upper
triangle on `Fin n` (vertices numbered by `Fintype.equivFin`). Polynomial time is not addressed
here (`docs/pequalnp.md`).
-/

namespace RadiusClustering.PEqualNP

/-- Moving a clustering along a bijection of the points. -/
theorem isValidClustering_comp_equiv' {X Y : Type*} (e : X ≃ Y) {d : Y → Y → ℕ}
    {d' : X → X → ℕ} (hdd' : ∀ i j, d' i j = d (e i) (e j)) {τ k : ℕ} (f : Y → Fin k)
    (hf : IsValidClustering d τ f) : IsValidClustering d' τ (f ∘ e) := by
  intro y
  obtain ⟨c, hc, hcz⟩ := hf (e y)
  refine ⟨e.symm c, by simp [hc], fun z hz => ?_⟩
  rw [hdd', Equiv.apply_symm_apply]
  exact hcz (e z) hz

open Classical in
/-- The dissimilarity of the gadget of `φ`, on its vertices numbered `0, …, n - 1`. -/
noncomputable def gadgetDissim (φ : List (List (ℕ × Bool))) (N : ℕ) :
    Fin (Fintype.card (GadgetV N φ.length)) → Fin (Fintype.card (GadgetV N φ.length)) → ℕ :=
  fun i j => graphDissim (satGadget φ N) ((Fintype.equivFin _).symm i)
    ((Fintype.equivFin _).symm j)

/-- **SAT → CLUST.** If every variable of `φ` is `< N`, `φ` is satisfiable iff the instance
`(k = N, τ = 1, gadgetDissim φ N)` is in CLUST. -/
theorem satisfiable_iff_mem_clustLang (φ : List (List (ℕ × Bool))) (N : ℕ)
    (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) :
    (∃ σ : ℕ → Bool, (φ.all fun c => c.any fun l => σ l.1 == l.2) = true) ↔
      encInst N 1 (toTri (gadgetDissim φ N)) ∈ clustLang := by
  classical
  set e := (Fintype.equivFin (GadgetV N φ.length)).symm
  have hdis : IsDissimilarity (gadgetDissim φ N) := by
    have h := isDissimilarity_graphDissim (satGadget φ N)
    exact ⟨fun i => h.self _, fun _ _ => Nat.zero_le _, fun i j => h.symm _ _⟩
  rw [satisfiable_iff_exists_dominating φ N hN,
    exists_dominating_iff_exists_validClustering_graphDissim]
  constructor
  · rintro ⟨f, hf⟩
    refine (mem_clustLang_iff _).2 ⟨_, N, 1, gadgetDissim φ N, hdis, rfl, f ∘ e,
      isValidClustering_comp_equiv' e (fun i j => rfl) f hf⟩
  · rintro ⟨M, k, τ, h, -, f, hf⟩
    obtain ⟨rfl, rfl, rfl⟩ := encInst_injective h
    let e' : Fin (toTri (gadgetDissim φ N)).length ≃ GadgetV N φ.length :=
      (finCongr (length_toTri _)).trans e
    refine ⟨f ∘ e'.symm, isValidClustering_comp_equiv' e'.symm (d := triDissim _) ?_ f hf⟩
    intro u v
    rw [triDissim_toTri hdis]
    simp [gadgetDissim, e', e]

end RadiusClustering.PEqualNP
