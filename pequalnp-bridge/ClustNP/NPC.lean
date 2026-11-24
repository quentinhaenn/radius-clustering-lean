import ClustNP.RedCorrect
import ClustNP.RedCPT
import PEqualNP.Library.L018
import PEqualNP.Library.L020
import PEqualNP.Library.L031

/-!
# CLUST is NP-complete, in pequalnp's framework

SAT (`L031`) reduces to CLUST (`sat_reduces_clust`: `red`, `cpt_red`, `red_correct`), CLUST is in
NP (`clustLang_mem_NP`), so CLUST is NP-complete (`L020`), and CLUST ∈ P ↔ P = NP (`L018`).
`L_clust_npc` is the candidate statement of `docs/pequalnp.md`, written inline.
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open RadiusClustering RadiusClustering.PEqualNP

theorem red_encodeCNF (φ : CNF) : red (encodeCNF φ) = itemInst φ := by
  have hwf : wfB (encodeCNF φ) = true := (wfB_iff _).2 ⟨φ, rfl⟩
  rw [red, hwf, encodeCNF_eq_items, itemsU_items, un_length, incB_iter, rowsOf_items, itemInst,
    encInst]
  simp [sel, bflag, encNat, PEqualNP.Library.SearchHelpers.S2D.dig]

theorem red_not {x : List Bool} (h : wfB x = false) : red x = [] := by
  simp [red, h, sel, bflag]

theorem nil_not_mem : ([] : List Bool) ∉ clustLang := by
  rintro ⟨M, k, τ, h, -⟩
  rw [encInst_eq] at h
  simp [encNat] at h

/-- **SAT reduces to CLUST in polynomial time.** -/
theorem sat_reduces_clust : PEqualNP.Library.PolyTimeReducible SAT clustLang := by
  refine ⟨red, cpt_red, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨φ, rfl, hs⟩
    rw [red_encodeCNF]
    exact (satisfiable_iff_itemInst_mem φ).1 hs
  · intro h
    cases hw : wfB x with
    | false => rw [red_not hw] at h; exact absurd h nil_not_mem
    | true =>
      obtain ⟨φ, rfl⟩ := (wfB_iff x).1 hw
      rw [red_encodeCNF] at h
      exact ⟨φ, rfl, (satisfiable_iff_itemInst_mem φ).2 h⟩

/-- **CLUST is NP-complete.** -/
theorem clustLang_npComplete : PEqualNP.Library.NPComplete clustLang :=
  PEqualNP.Library.L020 SAT clustLang PEqualNP.Library.L031 clustLang_mem_NP sat_reduces_clust

/-- A polynomial-time algorithm for CLUST is exactly as strong as `P = NP`. -/
theorem clustLang_mem_P_iff : clustLang ∈ PEqualNP.Library.P ↔ PEqualNP.Library.P = PEqualNP.Library.NP :=
  PEqualNP.Library.L018 clustLang clustLang_npComplete

end ClustNP

/-- The candidate statement for pequalnp (`docs/pequalnp.md`), proved. -/
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
        ∃ f : Fin M.length → Fin k, ∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ} := by
  have h := ClustNP.clustLang_npComplete
  rwa [RadiusClustering.PEqualNP.clustLang_eq_inline] at h
