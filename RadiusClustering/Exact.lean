import RadiusClustering.Pivot

/-!
# T3b: "exactly `k`" versus "at most `k`" clusters
-/

namespace RadiusClustering

variable {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]

omit [Zero α] in
/-- One step of T3b: with a free label and `k ≤ |X|`, detach a non-centre point into it. -/
theorem exists_valid_card_image_lt
    (d : X → X → α) (τ : α) (hself : ∀ x, d x x ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) (f : X → Fin k) (hf : IsValidClustering d τ f)
    (hlt : (Finset.univ.image f).card < k) :
    ∃ g : X → Fin k, IsValidClustering d τ g ∧
      (Finset.univ.image f).card < (Finset.univ.image g).card := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.image f) (t := (Finset.univ : Finset (Fin k)))
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hlt)
  have hj' : ∀ x, f x ≠ j := fun x hx =>
    hj (hx ▸ Finset.mem_image_of_mem f (Finset.mem_univ x))
  have hninj : ¬ Function.Injective f := by
    intro hinj
    have := Finset.card_image_of_injective (Finset.univ : Finset X) hinj
    rw [Finset.card_univ] at this
    omega
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hninj
    obtain ⟨a, b, h, hne⟩ := hninj
    exact ⟨a, b, h, hne⟩
  obtain ⟨c, hca, hcr⟩ := hf a
  obtain ⟨z, hzc, hfz⟩ : ∃ z, z ≠ c ∧ f z = f a := by
    by_cases h : a = c
    · exact ⟨b, fun hb => hne (h.trans hb.symm), hab.symm⟩
    · exact ⟨a, h, rfl⟩
  have hcz : c ≠ z := Ne.symm hzc
  let g : X → Fin k := fun x => if x = z then j else f x
  have hgz : g z = j := by simp [g]
  have hg : ∀ x, x ≠ z → g x = f x := fun x hx => by simp [g, hx]
  refine ⟨g, fun y => ?_, ?_⟩
  · by_cases hyz : y = z
    · subst hyz
      refine ⟨y, rfl, fun w hw => ?_⟩
      by_cases hwz : w = y
      · rw [hwz]
        exact hself y
      · rw [hg w hwz, hgz] at hw
        exact absurd hw (hj' w)
    · by_cases hya : f y = f a
      · refine ⟨c, by rw [hg c hcz, hg y hyz, hca, hya], fun w hw => ?_⟩
        by_cases hwz : w = z
        · rw [hwz, hgz, hg y hyz] at hw
          exact absurd hw.symm (hj' y)
        · rw [hg w hwz, hg y hyz] at hw
          exact hcr w (hw.trans hya)
      · obtain ⟨c', hc', hcr'⟩ := hf y
        have hc'z : c' ≠ z := fun h => hya (by rw [← hc', h, hfz])
        refine ⟨c', by rw [hg c' hc'z, hg y hyz, hc'], fun w hw => ?_⟩
        by_cases hwz : w = z
        · rw [hwz, hgz, hg y hyz] at hw
          exact absurd hw.symm (hj' y)
        · rw [hg w hwz, hg y hyz] at hw
          exact hcr' w hw
  · have hsub : insert j (Finset.univ.image f) ⊆ Finset.univ.image g := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_image] at hi
      rw [Finset.mem_image]
      rcases hi with rfl | ⟨x, -, rfl⟩
      · exact ⟨z, Finset.mem_univ _, hgz⟩
      · by_cases hxz : x = z
        · exact ⟨c, Finset.mem_univ _, by rw [hg c hcz, hca, hxz, hfz]⟩
        · exact ⟨x, Finset.mem_univ _, hg x hxz⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hj] at this
    omega

omit [Zero α] in
/-- T3b (⇐) by induction on the number of free labels, assuming only `d x x ≤ τ`. -/
theorem exists_surjective_of_valid
    (d : X → X → α) (τ : α) (hself : ∀ x, d x x ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) :
    ∀ n, ∀ f : X → Fin k, k - (Finset.univ.image f).card ≤ n → IsValidClustering d τ f →
      ∃ g : X → Fin k, Function.Surjective g ∧ IsValidClustering d τ g := by
  classical
  intro n
  induction n with
  | zero =>
    intro f hn hf
    refine ⟨f, fun i => ?_, hf⟩
    have hle : (Finset.univ.image f).card ≤ Fintype.card (Fin k) := Finset.card_le_univ _
    have heq : Finset.univ.image f = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Fintype.card_fin] at hle ⊢; omega)
    have hi : i ∈ Finset.univ.image f := heq ▸ Finset.mem_univ i
    simpa using hi
  | succ n ih =>
    intro f hn hf
    by_cases hlt : (Finset.univ.image f).card < k
    · obtain ⟨g, hg, hcard⟩ := exists_valid_card_image_lt d τ hself hk f hf hlt
      exact ih g (by omega) hg
    · exact ih f (by omega) hf

/-- **T3b.** For `k ≤ |X|`, a valid clustering with exactly `k` non-empty clusters (surjective `f`)
exists iff a valid clustering into at most `k` clusters exists. -/
theorem exists_surjective_validClustering_iff
    (d : X → X → α) (τ : α) (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) :
    (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f) ↔
      ∃ f : X → Fin k, IsValidClustering d τ f := by
  constructor
  · rintro ⟨f, -, hf⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact exists_surjective_of_valid d τ (fun x => by rw [hd.self x]; exact hτ) hk _ f le_rfl hf

/-- Edge case `k > |X|`: no clustering has exactly `k` non-empty clusters. -/
theorem not_surjective_of_card_lt {k : ℕ} (hk : Fintype.card X < k) (f : X → Fin k) :
    ¬ Function.Surjective f := fun h => by
  have := Fintype.card_le_of_surjective f h
  simp at this
  omega

/-- **T3b + T3a.** For `k ≤ |X|`: exactly `k` clusters of radius `≤ τ` iff `G_τ` has a
dominating set of size `≤ k`. -/
theorem exists_surjective_validClustering_iff_exists_dominating
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) :
    (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f) ↔
      ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  rw [exists_surjective_validClustering_iff d τ hd hτ hk]
  exact exists_validClustering_iff_exists_dominating d τ hd hτ k

end RadiusClustering
