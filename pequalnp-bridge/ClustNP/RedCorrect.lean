import ClustNP.RedItems

/-!
# The reduction writes the item instance

`red (encodeCNF φ) = itemInst φ` (`red_encodeCNF`), and `red x = []` on a string that encodes no
formula. Hence `x ∈ SAT ↔ red x ∈ CLUST` (`red_correct`).
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open PEqualNP.Library.SearchHelpers.S2D (incB dig)
open RadiusClustering RadiusClustering.PEqualNP

variable (its : List (Option (ℕ × Bool)))

/-! ### Adjacency -/

theorem div3_un (i : ℕ) : div3 (un i) = un (i / 3) := by simp [div3]

theorem crossAt_iff {i j : ℕ} (hi : i / 3 < its.length) (hj : j / 3 < its.length) :
    crossAt (un i) (un j) (its.flatMap encItem) = true ↔
      i % 3 < 2 ∧ j % 3 = 2 ∧ its[j / 3]? = some none ∧
        ∃ l, IsRep its (i / 3) l ∧ InSeg its (j / 3) (l.1, decide (i % 3 = 0)) := by
  simp only [crossAt, Bool.and_eq_true, Bool.not_eq_true', div3_un, isR2, isR0, un_length,
    decide_eq_true_eq, decide_eq_false_iff_not, endAt_items its hj]
  rw [List.getElem?_eq_getElem hj, Option.some.injEq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    obtain ⟨l, hl⟩ := (repAt_iff its hi).1 h4
    have hl' : its[i / 3] = some l := by
      have := hl.1; rwa [List.getElem?_eq_getElem hi, Option.some.injEq] at this
    rw [varAt_items its hi, hl', varCode] at h5
    have hlit : (true :: decide (i % 3 = 0) :: vcode l.1) = encodeLiteral (l.1, decide (i % 3 = 0)) := by
      rw [encodeLiteral_eq]
    rw [hlit, segAt_iff its hj] at h5
    exact ⟨by omega, h2, h3, l, hl, h5⟩
  · rintro ⟨h1, h2, h3, l, hl, h5⟩
    have hl' : its[i / 3] = some l := by
      have := hl.1; rwa [List.getElem?_eq_getElem hi, Option.some.injEq] at this
    refine ⟨⟨⟨⟨by omega, h2⟩, h3⟩, (repAt_iff its hi).2 ⟨l, hl⟩⟩, ?_⟩
    rw [varAt_items its hi, hl', varCode]
    have hlit : (true :: decide (i % 3 = 0) :: vcode l.1) = encodeLiteral (l.1, decide (i % 3 = 0)) := by
      rw [encodeLiteral_eq]
    rw [hlit, segAt_iff its hj]
    exact h5

theorem adjAt_iff {u v : Fin (3 * its.length)} (huv : u ≠ v) :
    adjAt (un u) (un v) (its.flatMap encItem) = true ↔ (itemGadget its).Adj u v := by
  have hu : u.val / 3 < its.length := by omega
  have hv : v.val / 3 < its.length := by omega
  rw [itemGadget, SimpleGraph.fromRel_adj, adjAt, div3_un, div3_un]
  simp only [ne_eq, huv, not_false_eq_true, true_and]
  have hun : (un (u.val / 3) = un (v.val / 3)) ↔ u.val / 3 = v.val / 3 :=
    ⟨fun h => un_inj h, fun h => by rw [h]⟩
  by_cases h : u.val / 3 = v.val / 3
  · simp only [show un (u.val / 3) = un (v.val / 3) from hun.2 h, ↓reduceIte]
    simp only [itemRel, h, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      isR2, un_length, decide_eq_false_iff_not, endAt_items its hv]
    rw [List.getElem?_eq_getElem hv]
    simp only [Option.some.injEq]
    rcases its[v.val / 3] with _ | l
    · simp; omega
    · simp
  · simp only [show ¬ un (u.val / 3) = un (v.val / 3) from fun h' => h (hun.1 h'), ↓reduceIte]
    rw [Bool.or_eq_true, crossAt_iff its hu hv,
      crossAt_iff its hv hu]
    simp only [itemRel, h, Ne.symm h, ↓reduceIte]

/-! ### Rows -/

theorem flatMap_ofFn {α β : Type*} : ∀ (n : ℕ) (f : Fin n → α) (g : α → List β) (F : ℕ → List β),
    (∀ i : Fin n, g (f i) = F i) → (List.ofFn f).flatMap g = (List.range n).flatMap F
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, F, h => by
    rw [List.ofFn_succ', List.concat_eq_append, List.flatMap_append, List.range_succ,
      List.flatMap_append, flatMap_ofFn n _ g F (fun i => h i.castSucc)]
    simp [h (Fin.last n)]

theorem tail_iter_length (m : ℕ) (l : List Bool) : (List.tail^[m] l).length = l.length - m := by
  rw [tail_iter_eq_drop, List.length_drop]

theorem vertsU_items : (vertsU (its.flatMap encItem)).length = 3 * its.length := by
  simp [vertsU, itemsU_items]; omega

open Classical in
theorem entryAt_items {u v : Fin (3 * its.length)} (huv : u < v) :
    entryAt (un u) (un v) (its.flatMap encItem) = encNat (graphDissim (itemGadget its) u v) := by
  have hne : u ≠ v := ne_of_lt huv
  rw [entryAt, graphDissim]
  by_cases h : (itemGadget its).Adj u v
  · simp only [hne, h, ↓reduceIte, (adjAt_iff its hne).2 h]; rfl
  · have h' : adjAt (un u) (un v) (its.flatMap encItem) = false := by
      rw [← Bool.not_eq_true]; exact fun h'' => h ((adjAt_iff its hne).1 h'')
    simp only [hne, h, ↓reduceIte, h']; rfl

open Classical in
theorem rowsOf_items :
    rowsOf (its.flatMap encItem) = (toTri (graphDissim (itemGadget its))).flatMap encRow := by
  rw [rowsOf, vertsU_items, toTri]
  symm
  refine flatMap_ofFn _ _ encRow _ (fun i => ?_)
  simp only [rowAt, unpairB_pairB, un_length, tail_iter_length, vertsU_items, encRow]
  congr 1
  rw [show 3 * its.length - (i.val + 1) = 3 * its.length - 1 - i.val by omega]
  refine flatMap_ofFn _ _ encNat _ (fun j => ?_)
  simp only [cell, unpairB_pairB, un_append_cons]
  exact (entryAt_items its (u := i) (v := ⟨i.val + 1 + j.val, by omega⟩)
    (by simp [Fin.lt_def]; omega)).symm

end ClustNP
