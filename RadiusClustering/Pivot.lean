import RadiusClustering.Basic
import Mathlib.Data.Finset.Max

/-!
# T3a: clustering into at most `k` clusters ⇔ dominating set of size at most `k`

Also T1, T1c and the existence half of T2c. Unreviewed helper lemmas take weaker hypotheses than
Def. 1.2 (`docs/cadrage.md` §7).
-/

namespace RadiusClustering

section Helpers

variable {X α : Type*} [Fintype X] [LE α] (d : X → X → α) (τ : α)

/-- Every valid clustering has a set of centres (no hypothesis on `d`). -/
theorem exists_isCentreSet_of_valid {k : ℕ} (f : X → Fin k) (hf : IsValidClustering d τ f) :
    ∃ C : Finset X, IsCentreSet d τ f C := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, by simp, fun v => isEmptyElim v⟩
  have h : ∀ i : Fin k, ∃ c : X, (∃ y, f y = i) → f c = i ∧ ∀ z, f z = i → d c z ≤ τ := by
    intro i
    by_cases hi : ∃ y, f y = i
    · obtain ⟨y, rfl⟩ := hi
      obtain ⟨c, hc, hcz⟩ := hf y
      exact ⟨c, fun _ => ⟨hc, hcz⟩⟩
    · exact ⟨Classical.arbitrary X, fun h' => absurd h' hi⟩
  choose cen hcen using h
  refine ⟨(Finset.univ.image f).image cen, ?_, fun y => ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image,
      Set.mem_range] at ha hb
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := ha
    obtain ⟨_, ⟨x', rfl⟩, rfl⟩ := hb
    rw [(hcen _ ⟨x, rfl⟩).1, (hcen _ ⟨x', rfl⟩).1] at hab
    rw [hab]
  · obtain ⟨hc, hcz⟩ := hcen (f y) ⟨y, rfl⟩
    exact ⟨cen (f y), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ y)),
      hc, hcz⟩

/-- A set of centres dominates `G_τ` and has one element per non-empty cluster. -/
theorem IsCentreSet.dominating_card {k : ℕ} {f : X → Fin k} {C : Finset X}
    (hC : IsCentreSet d τ f C) :
    IsDominating (thresholdGraph d τ) C ∧ C.card = (Finset.univ.image f).card := by
  classical
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨c, hcC, -, hcz⟩ := hC.2 v
    by_cases hc : c = v
    · exact Or.inl (hc ▸ hcC)
    · refine Or.inr ⟨c, hcC, ?_⟩
      simp only [thresholdGraph, SimpleGraph.fromRel_adj]
      exact ⟨hc, Or.inl (hcz v rfl)⟩
  · rw [← Finset.card_image_of_injOn hC.1]
    congr 1
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, -, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨c, hcC, hc, -⟩ := hC.2 y
      exact ⟨c, hcC, hc⟩

/-- T3a (⇒) with no hypothesis on `d`: the centres of a valid clustering dominate `G_τ`. -/
theorem exists_dominating_of_validClustering
    {k : ℕ} (f : X → Fin k) (hf : IsValidClustering d τ f) :
    ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  obtain ⟨C, hC⟩ := exists_isCentreSet_of_valid d τ f hf
  obtain ⟨hdom, hcard⟩ := hC.dominating_card d τ
  refine ⟨C, ?_, hdom⟩
  rw [hcard]
  calc (Finset.univ.image f).card ≤ Fintype.card (Fin k) := Finset.card_le_univ _
    _ = k := Fintype.card_fin k

omit [Fintype X] in
/-- T3a (⇐) assuming only `d x x ≤ τ` and symmetry: one cluster per element of `S`. -/
theorem exists_validClustering_of_dominating
    (hself : ∀ x, d x x ≤ τ) (hsymm : ∀ x y, d x y = d y x)
    {k : ℕ} (S : Finset X) (hk : S.card ≤ k) (hS : IsDominating (thresholdGraph d τ) S) :
    ∃ f : X → Fin k, IsValidClustering d τ f := by
  classical
  have h : ∀ v, ∃ s ∈ S, (v ∈ S → s = v) ∧ d s v ≤ τ := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨v, hv, fun _ => rfl, hself v⟩
    · rcases hS v with hv' | ⟨s, hs, hadj⟩
      · exact absurd hv' hv
      · simp only [thresholdGraph, SimpleGraph.fromRel_adj] at hadj
        refine ⟨s, hs, fun h => absurd h hv, ?_⟩
        rcases hadj.2 with h | h
        · exact h
        · rwa [hsymm] at h
  choose σ hσS hσfix hσd using h
  let f : X → Fin k := fun v => Fin.castLE hk (S.equivFin ⟨σ v, hσS v⟩)
  have hf : ∀ v w, f v = f w → σ v = σ w := fun v w hvw =>
    congrArg Subtype.val (S.equivFin.injective (Fin.castLE_injective hk hvw))
  refine ⟨f, fun y => ⟨σ y, ?_, fun z hz => ?_⟩⟩
  · exact congrArg (fun s => Fin.castLE hk (S.equivFin s)) (Subtype.ext (hσfix _ (hσS y)))
  · rw [← hf z y hz]
    exact hσd z

end Helpers

/-- **T3a.** `X` splits into at most `k` clusters of radius `≤ τ` iff the threshold graph `G_τ`
has a dominating set of size `≤ k`. -/
theorem exists_validClustering_iff_exists_dominating
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ) (k : ℕ) :
    (∃ f : X → Fin k, IsValidClustering d τ f) ↔
      ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  constructor
  · rintro ⟨f, hf⟩
    exact exists_dominating_of_validClustering d τ f hf
  · rintro ⟨S, hk, hS⟩
    exact exists_validClustering_of_dominating d τ
      (fun x => by rw [hd.self x]; exact hτ) hd.symm S hk hS

/-- **T1** (Th. 3.1, optimisation form). `k` is the minimum number of clusters of radius `≤ τ`
iff `k` is the size of a minimum dominating set of `G_τ`. -/
theorem minClusters_iff_minDominating
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ) (k : ℕ) :
    ((∃ f : X → Fin k, IsValidClustering d τ f) ∧
        ∀ m < k, ¬ ∃ f : X → Fin m, IsValidClustering d τ f) ↔
      ((∃ S : Finset X, S.card = k ∧ IsDominating (thresholdGraph d τ) S) ∧
        ∀ S : Finset X, IsDominating (thresholdGraph d τ) S → k ≤ S.card) := by
  simp only [exists_validClustering_iff_exists_dominating d τ hd hτ]
  constructor
  · rintro ⟨⟨S, hSk, hS⟩, hmin⟩
    have hge : ∀ S' : Finset X, IsDominating (thresholdGraph d τ) S' → k ≤ S'.card :=
      fun S' hS' => not_lt.1 fun hlt => hmin _ hlt ⟨S', le_rfl, hS'⟩
    exact ⟨⟨S, le_antisymm hSk (hge S hS), hS⟩, hge⟩
  · rintro ⟨⟨S, hSk, hS⟩, hge⟩
    refine ⟨⟨S, hSk.le, hS⟩, fun m hm ⟨S', hS'm, hS'⟩ => ?_⟩
    have := hge S' hS'
    omega

-- `hd`, `hτ` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- **T2c** (existence). Every valid partition has a set of centres. -/
theorem exists_isCentreSet
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α) (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (f : X → Fin k) (hf : IsValidClustering d τ f) :
    ∃ C : Finset X, IsCentreSet d τ f C := by
  exact exists_isCentreSet_of_valid d τ f hf

-- `hd`, `hτ` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- **T1c** (existence). A dominating set `S` always has a partition derived from it, with `|S|`
labels. -/
theorem exists_isDerivedFrom
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α) (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    (S : Finset X) (hS : IsDominating (thresholdGraph d τ) S) :
    ∃ f : X → Fin S.card, IsDerivedFrom d S f := by
  classical
  have h : ∀ x, ∃ c ∈ S, (x ∈ S → c = x) ∧ (x ∉ S → ∀ c' ∈ S, d x c ≤ d x c') := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨x, hx, fun _ => rfl, fun h => absurd hx h⟩
    · have hne : S.Nonempty := by
        rcases hS x with h | ⟨s, hs, -⟩
        · exact absurd h hx
        · exact ⟨s, hs⟩
      obtain ⟨c, hc, hmin⟩ := S.exists_min_image (d x) hne
      exact ⟨c, hc, fun h => absurd h hx, fun _ => hmin⟩
  choose σ hσS hσfix hσmin using h
  refine ⟨fun x => S.equivFin ⟨σ x, hσS x⟩, fun a ha b hb hab => ?_, fun x hx => ?_⟩
  · have := congrArg Subtype.val (S.equivFin.injective hab)
    simpa [hσfix a ha, hσfix b hb] using this
  · refine ⟨σ x, hσS x, ?_, hσmin x hx⟩
    exact congrArg S.equivFin (Subtype.ext (hσfix _ (hσS x)).symm)

/-- A partition derived from a dominating set `S` has `S` as a set of centres. -/
theorem IsDerivedFrom.isCentreSet
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    {d : X → X → α} {τ : α} (hd : IsDissimilarity d) (hτ : 0 ≤ τ) {S : Finset X}
    (hS : IsDominating (thresholdGraph d τ) S) {k : ℕ} {f : X → Fin k}
    (hf : IsDerivedFrom d S f) : IsCentreSet d τ f S := by
  have hrad : ∀ c ∈ S, ∀ w, f w = f c → d c w ≤ τ := by
    intro c hc w hw
    by_cases hwS : w ∈ S
    · rw [hf.1 hwS hc hw, hd.self]
      exact hτ
    · obtain ⟨c', hc'S, hwc', hnear⟩ := hf.2 w hwS
      have hcc' : c' = c := hf.1 hc'S hc (hwc'.symm.trans hw)
      subst hcc'
      rcases hS w with h | ⟨s, hs, hadj⟩
      · exact absurd h hwS
      · simp only [thresholdGraph, SimpleGraph.fromRel_adj] at hadj
        have hsw : d w s ≤ τ := by
          rcases hadj.2 with h | h
          · rwa [hd.symm] at h
          · exact h
        rw [hd.symm]
        exact (hnear s hs).trans hsw
  refine ⟨hf.1, fun y => ?_⟩
  by_cases hyS : y ∈ S
  · exact ⟨y, hyS, rfl, hrad y hyS⟩
  · obtain ⟨c, hcS, hyc, -⟩ := hf.2 y hyS
    exact ⟨c, hcS, hyc.symm, fun w hw => hrad c hcS w (hw.trans hyc)⟩

/-- **T1c** (Th. 3.1, constructive form). The partition derived from a minimum dominating set of
`G_τ` is valid, has exactly `|S|` clusters, and no valid partition has fewer. -/
theorem isDerivedFrom_minDominating
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ) (S : Finset X)
    (hS : IsDominating (thresholdGraph d τ) S)
    (hmin : ∀ S' : Finset X, IsDominating (thresholdGraph d τ) S' → S.card ≤ S'.card)
    {k : ℕ} (f : X → Fin k) (hf : IsDerivedFrom d S f) :
    IsValidClustering d τ f ∧ (Finset.univ.image f).card = S.card ∧
      ∀ m < S.card, ¬ ∃ g : X → Fin m, IsValidClustering d τ g := by
  have hC := hf.isCentreSet hd hτ hS
  refine ⟨fun y => ?_, (hC.dominating_card d τ).2.symm, fun m hm ⟨g, hg⟩ => ?_⟩
  · obtain ⟨c, -, hc, hcz⟩ := hC.2 y
    exact ⟨c, hc, hcz⟩
  · obtain ⟨S', hS'm, hS'⟩ := exists_dominating_of_validClustering d τ g hg
    have := hmin S' hS'
    omega

end RadiusClustering
