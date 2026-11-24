import RadiusClustering.PEqualNP.Injective

/-!
# CLUST on the instance of Fig. 3.4
-/

namespace RadiusClustering.PEqualNP

/-- **Test on Fig. 3.4.** Its encoding is in CLUST for `k = 2`, `τ = 1`, and not for `τ = 0`. -/
theorem fig34_mem_clustLang :
    encInst 2 1 (toTri fig34) ∈ clustLang ∧ encInst 2 0 (toTri fig34) ∉ clustLang := by
  refine ⟨(mem_clustLang_iff _).2 ⟨4, 2, 1, fig34, fig34_isDissimilarity, rfl, ![0, 0, 0, 1],
    by unfold IsValidClustering; decide⟩, ?_⟩
  rintro ⟨M, k, τ, h, -, f, hf⟩
  obtain ⟨rfl, rfl, rfl⟩ := encInst_injective h
  let e : Fin 4 ≃ Fin (toTri fig34).length := (finCongr (length_toTri fig34)).symm
  have hf' := isValidClustering_comp_equiv e (d := triDissim (toTri fig34)) (d' := fig34)
    (fun i j => by rw [triDissim_toTri fig34_isDissimilarity]; rfl) f hf
  have := Fintype.card_le_of_injective _ (fig34_injective_of_valid_zero (by norm_num) hf')
  simp at this

end RadiusClustering.PEqualNP
