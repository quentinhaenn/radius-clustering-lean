import ClustNP.Wf
import ClustNP.CPT
import RadiusClustering.Pivot

/-!
# CLUST is in NP

The verifier `CV` accepts `(x, w)` exactly when `x` encodes an instance `(k, τ, M)` and the
points `s` with `w[s] = true` are at most `k` centres covering every point within `τ`
(`CV_iff`). With T3a this gives the witnesses of CLUST (`CV_spec`), and with `cpt_CV`
membership in pequalnp's NP.
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open RadiusClustering RadiusClustering.PEqualNP

/-! ### Flags -/

theorem bflag_eq_nil (b : Bool) : bflag b = [] ↔ b = false := by
  cases b <;> simp [bflag]

theorem isEmpty_flatMap_bflag (l : List ℕ) (f : ℕ → Bool) :
    (l.flatMap fun i => bflag (f i)).isEmpty = true ↔ ∀ i ∈ l, f i = false := by
  rw [List.isEmpty_iff, List.flatMap_eq_nil_iff]
  simp only [bflag_eq_nil]

theorem un_append_cons (a i : ℕ) : un a ++ true :: un i = un (a + 1 + i) := by
  simp only [un, List.replicate_add]
  simp [List.replicate_succ]

/-! ### Triangularity -/

theorem triBad_encInst (k τ : ℕ) (M : List (List ℕ)) :
    (triBad (encInst k τ M)).isEmpty = true ↔ IsTriangular M := by
  have hrow : ∀ i (hi : i < M.length), triRow (pairB (un i) (encInst k τ M)) =
      bflag (!decide (M[i].length + 1 + i = M.length)) := by
    intro i hi
    rw [triRow, unpairB_pairB, un_length, rowsS_encInst, dropRow_iter, endsU_encInst]
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons, rowLenU_encRow, un_append_cons]
    congr 3
    simp only [eq_iff_iff]
    exact ⟨fun h => un_inj h, fun h => by rw [h]⟩
  rw [triBad, endsU_encInst, un_length]
  have : ((List.range M.length).flatMap fun i => triRow (pairB (un i) (encInst k τ M))) =
      (List.range M.length).flatMap fun i =>
        bflag (if h : i < M.length then !decide (M[i].length + 1 + i = M.length) else false) := by
    apply List.flatMap_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    simp only [hrow i hi', hi', ↓reduceDIte]
  rw [this, isEmpty_flatMap_bflag]
  constructor
  · intro h i
    have := h i.val (List.mem_range.2 i.2)
    simp only [i.2, ↓reduceDIte, Bool.not_eq_false', decide_eq_true_eq] at this
    rw [List.get_eq_getElem]
    omega
  · intro h i hi
    have hi' := List.mem_range.1 hi
    simp only [hi', ↓reduceDIte, Bool.not_eq_false', decide_eq_true_eq]
    have := h ⟨i, hi'⟩
    rw [List.get_eq_getElem] at this
    simp only at this
    omega

/-! ### Covering -/

theorem tail_iter_eq_drop (w : List Bool) (s : ℕ) : List.tail^[s] w = w.drop s := by
  induction s generalizing w with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply, ih]; simp

theorem f1_drop (w : List Bool) (s : ℕ) :
    (f1 (w.drop s)).isEmpty = !(w.getD s false) := by
  rw [f1, List.head?_drop, List.getD_eq_getElem?_getD]
  rcases w[s]? with _ | b
  · simp
  · cases b <;> simp

theorem covers_encInst {k τ : ℕ} {M : List (List ℕ)} (hM : IsTriangular M) (w : List Bool)
    (s y : Fin M.length) :
    covers (un s) (un y) (encInst k τ M) w = true ↔
      w.getD s false = true ∧ (s = y ∨ triDissim M s y ≤ τ) := by
  rw [covers, Bool.and_eq_true, Bool.not_eq_true', tail_iter_eq_drop, un_length, f1_drop,
    Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq, un_length,
    headI_dropI_encInst]
  apply and_congr_right
  intro _
  have hsy : (un s = un y) ↔ s = y := ⟨fun h => Fin.ext (un_inj h), fun h => by rw [h]⟩
  rw [hsy]
  by_cases he : s = y
  · simp [he]
  · simp only [he, false_or]
    have hlt : s.val ≠ y.val := fun h => he (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hlt with h | h
    · simp only [h, ↓reduceIte]
      rw [entryS_encInst hM h y.2, leF_encNat]
      simp [bflag, triDissim, show s < y from h]
    · simp only [show ¬ s.val < y.val by omega, ↓reduceIte]
      rw [entryS_encInst hM h s.2, leF_encNat]
      simp [bflag, triDissim, show ¬ s < y from fun h' => by
        have : s.val < y.val := h'; omega, show y < s from h]

theorem uncovAll_encInst {k τ : ℕ} {M : List (List ℕ)} (w : List Bool) :
    (uncovAll (encInst k τ M) w).isEmpty = true ↔
      ∀ y < M.length, ∃ s < M.length, covers (un s) (un y) (encInst k τ M) w = true := by
  have hin : ∀ y, uncov (pairB (un y) (pairB (encInst k τ M) w)) =
      bflag ((List.range M.length).flatMap fun s =>
        bflag (covers (un s) (un y) (encInst k τ M) w)).isEmpty := by
    intro y
    simp only [uncov, unpairB_pairB, endsU_encInst, un_length, covRow]
  rw [uncovAll, endsU_encInst, un_length]
  simp only [hin]
  rw [isEmpty_flatMap_bflag]
  apply forall_congr'
  intro y
  rw [List.mem_range]
  apply imp_congr_right
  intro _
  rw [Bool.eq_false_iff, ne_eq, isEmpty_flatMap_bflag]
  simp only [List.mem_range, not_forall, Bool.not_eq_false, exists_prop]

/-! ### The verifier -/

theorem CV_iff (x w : List Bool) :
    CV (x, w) = true ↔ ∃ k τ M, x = encInst k τ M ∧ IsTriangular M ∧ w.count true ≤ k ∧
      ∀ y : Fin M.length, ∃ s : Fin M.length,
        w.getD s false = true ∧ (s = y ∨ triDissim M s y ≤ τ) := by
  simp only [CV, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨hwf, htri⟩, hcnt⟩, hcov⟩
    obtain ⟨k, τ, M, rfl⟩ := (wfI_iff x).1 hwf
    have hM := (triBad_encInst k τ M).1 htri
    refine ⟨k, τ, M, rfl, hM, ?_, fun y => ?_⟩
    · rw [cntS_eq, headI_encInst, leF_encNat] at hcnt
      simpa [bflag] using hcnt
    · obtain ⟨s, hs, hc⟩ := (uncovAll_encInst w).1 hcov y y.2
      exact ⟨⟨s, hs⟩, (covers_encInst hM w ⟨s, hs⟩ y).1 hc⟩
  · rintro ⟨k, τ, M, rfl, hM, hk, hcov⟩
    refine ⟨⟨⟨wfI_encInst k τ M, (triBad_encInst k τ M).2 hM⟩, ?_⟩, ?_⟩
    · rw [cntS_eq, headI_encInst, leF_encNat]
      simp [bflag, hk]
    · refine (uncovAll_encInst w).2 fun y hy => ?_
      obtain ⟨s, hs⟩ := hcov ⟨y, hy⟩
      exact ⟨s, s.2, (covers_encInst hM w s ⟨y, hy⟩).2 hs⟩

/-! ### Witnesses -/

theorem count_eq_card (w : List Bool) :
    w.count true = ((Finset.range w.length).filter fun i => w.getD i false = true).card := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [List.count_cons, ih, Finset.card_filter, Finset.card_filter, List.length_cons,
      Finset.sum_range_succ']
    cases b <;> simp

theorem length_le_rows (M : List (List ℕ)) : M.length ≤ (M.flatMap encRow).length := by
  induction M with
  | nil => simp
  | cons row M ih => simp [encRow]; omega

theorem length_le_encInst (k τ : ℕ) (M : List (List ℕ)) :
    M.length ≤ (encInst k τ M).length := by
  have := length_le_rows M
  rw [encInst_eq, List.length_append, List.length_append]; omega

theorem dominating_iff {n : ℕ} {d : Fin n → Fin n → ℕ} (hd : IsDissimilarity d) (τ : ℕ)
    (S : Finset (Fin n)) :
    IsDominating (thresholdGraph d τ) S ↔ ∀ y, ∃ s ∈ S, s = y ∨ d s y ≤ τ := by
  constructor
  · intro h y
    rcases h y with hy | ⟨s, hs, hadj⟩
    · exact ⟨y, hy, Or.inl rfl⟩
    · refine ⟨s, hs, Or.inr ?_⟩
      rw [thresholdGraph, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact h
      · rwa [hd.symm]
  · intro h y
    obtain ⟨s, hs, rfl | hle⟩ := h y
    · exact Or.inl hs
    · by_cases hsy : s = y
      · subst hsy; exact Or.inl hs
      · refine Or.inr ⟨s, hs, ?_⟩
        rw [thresholdGraph, SimpleGraph.fromRel_adj]
        exact ⟨hsy, Or.inl hle⟩

/-- **Witnesses for CLUST.** `x ∈ CLUST` iff some `w` no longer than `x` passes `CV`. -/
theorem CV_spec (x : List Bool) :
    x ∈ clustLang ↔ ∃ w : List Bool, w.length ≤ x.length ∧ CV (x, w) = true := by
  classical
  constructor
  · rintro ⟨M, k, τ, rfl, hM, f, hf⟩
    have hdis := isDissimilarity_triDissim M
    obtain ⟨S, hSk, hS⟩ := (exists_validClustering_iff_exists_dominating (triDissim M) τ hdis
      (Nat.zero_le _) k).1 ⟨f, hf⟩
    rw [dominating_iff hdis] at hS
    let w : List Bool := List.ofFn fun i : Fin M.length => decide (i ∈ S)
    have hget : ∀ i : Fin M.length, w.getD i false = decide (i ∈ S) := by
      intro i
      simp [w, List.getD_eq_getElem?_getD]
    refine ⟨w, by simp [w]; exact length_le_encInst k τ M, (CV_iff _ _).2
      ⟨k, τ, M, rfl, hM, ?_, fun y => ?_⟩⟩
    · rw [count_eq_card]
      have : ((Finset.range w.length).filter fun i => w.getD i false = true) =
          S.image Fin.val := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hi, hw⟩
          have hi' : i < M.length := by simpa [w] using hi
          refine ⟨⟨i, hi'⟩, ?_, rfl⟩
          have h2 : w.getD i false = decide (⟨i, hi'⟩ ∈ S) := hget ⟨i, hi'⟩
          rw [h2] at hw
          simpa using hw
        · rintro ⟨j, hj, rfl⟩
          exact ⟨by simp [w], by rw [hget j]; simpa using hj⟩
      rw [this, Finset.card_image_of_injective _ Fin.val_injective]
      exact hSk
    · obtain ⟨s, hs, h⟩ := hS y
      exact ⟨s, by rw [hget s]; simpa using hs, h⟩
  · rintro ⟨w, -, h⟩
    obtain ⟨k, τ, M, rfl, hM, hk, hcov⟩ := (CV_iff _ _).1 h
    have hdis := isDissimilarity_triDissim M
    refine ⟨M, k, τ, rfl, hM, ?_⟩
    let S : Finset (Fin M.length) := Finset.univ.filter fun i => w.getD i false = true
    refine (exists_validClustering_iff_exists_dominating (triDissim M) τ hdis
      (Nat.zero_le _) k).2 ⟨S, ?_, (dominating_iff hdis τ S).2 fun y => ?_⟩
    · refine le_trans ?_ hk
      rw [count_eq_card, ← Finset.card_image_of_injective S Fin.val_injective]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      have hj' : w.getD j false = true := (Finset.mem_filter.1 hj).2
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hj'⟩
      by_contra hlen
      rw [List.getD_eq_default _ _ (by omega)] at hj'
      exact absurd hj' (by simp)
    · obtain ⟨s, hs, h⟩ := hcov y
      exact ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩, h⟩

/-- **CLUST is in NP**, in pequalnp's sense. -/
theorem clustLang_mem_NP : clustLang ∈ PEqualNP.Library.NP := by
  refine ⟨{p | CV p = true}, Polynomial.X, ⟨CV, fun _ => Iff.rfl, cpt_CV⟩, fun x => ?_⟩
  exact (CV_spec x).trans (by simp)

end ClustNP
