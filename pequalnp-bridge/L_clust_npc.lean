import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.SearchHelpers.SearchToDecision
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Digits.Lemmas
import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.TwoSatStr
import PEqualNP.Library.L018
import PEqualNP.Library.L020
import PEqualNP.Library.L031

namespace PEqualNP.Outside.L_clust_npc

section M_RadiusClustering_Basic

namespace RadiusClustering

variable {X α : Type*}

structure IsDissimilarity [LE α] [Zero α] (d : X → X → α) : Prop where
  self : ∀ x, d x x = 0
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x

def thresholdGraph [LE α] (d : X → X → α) (τ : α) : SimpleGraph X :=
  SimpleGraph.fromRel fun x y => d x y ≤ τ

def IsDominating {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v

def IsValidClustering [LE α] {k : ℕ} (d : X → X → α) (τ : α) (f : X → Fin k) : Prop :=
  ∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ

def IsDerivedFrom [LE α] {k : ℕ} (d : X → X → α) (S : Finset X) (f : X → Fin k) : Prop :=
  Set.InjOn f S ∧ ∀ x ∉ S, ∃ c ∈ S, f x = f c ∧ ∀ c' ∈ S, d x c ≤ d x c'

def IsCentreSet [LE α] {k : ℕ} (d : X → X → α) (τ : α) (f : X → Fin k) (C : Finset X) : Prop :=
  Set.InjOn f C ∧ ∀ y, ∃ c ∈ C, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ

def graphDissim {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℕ :=
  if u = v then 0 else if G.Adj u v then 1 else 2

end RadiusClustering

end M_RadiusClustering_Basic
section M_RadiusClustering_Pivot

namespace RadiusClustering

section Helpers

variable {X α : Type*} [Fintype X] [LE α] (d : X → X → α) (τ : α)

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

theorem exists_isCentreSet
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α) (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (f : X → Fin k) (hf : IsValidClustering d τ f) :
    ∃ C : Finset X, IsCentreSet d τ f C := by
  exact exists_isCentreSet_of_valid d τ f hf

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

end M_RadiusClustering_Pivot
section M_RadiusClustering_Exact

namespace RadiusClustering

variable {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]

omit [Zero α] in

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

theorem not_surjective_of_card_lt {k : ℕ} (hk : Fintype.card X < k) (f : X → Fin k) :
    ¬ Function.Surjective f := fun h => by
  have := Fintype.card_le_of_surjective f h
  simp at this
  omega

theorem exists_surjective_validClustering_iff_exists_dominating
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) :
    (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f) ↔
      ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  rw [exists_surjective_validClustering_iff d τ hd hτ hk]
  exact exists_validClustering_iff_exists_dominating d τ hd hτ k

end RadiusClustering

end M_RadiusClustering_Exact
section M_RadiusClustering_Curgraph

namespace RadiusClustering

variable {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]

def IsMinRadius (d : X → X → α) (k : ℕ) (r : α) : Prop :=
  (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d r f) ∧
    ∀ τ < r, ¬ ∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f

omit [Fintype X] [Zero α] in

theorem thresholdGraph_congr (d : X → X → α) {τ τ' : α}
    (h : ∀ u v, d u v ≤ τ ↔ d u v ≤ τ') : thresholdGraph d τ = thresholdGraph d τ' := by
  ext u v
  simp only [thresholdGraph, SimpleGraph.fromRel_adj, h]

omit [Fintype X] in

theorem IsDominating.thresholdGraph_mono {d : X → X → α} (hd : IsDissimilarity d)
    {t t' : α} (ht : 0 ≤ t) (htt' : t ≤ t')
    {S : Finset X} (hS : IsDominating (thresholdGraph d t) S) :
    IsDominating (thresholdGraph d t') S := by
  intro v
  rcases hS v with h | ⟨s, hs, hadj⟩
  · exact Or.inl h
  · refine Or.inr ⟨s, hs, ?_⟩
    simp only [thresholdGraph, SimpleGraph.fromRel_adj] at hadj ⊢
    exact ⟨hadj.1, hadj.2.imp (fun h => h.trans htt') (fun h => h.trans htt')⟩

theorem isMinRadius_of_lastDominable
    (d : X → X → α) (hd : IsDissimilarity d) {k : ℕ} (hk : k ≤ Fintype.card X) (t : α)
    (htT : ∃ x y, d x y = t)
    (ht : ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d t) S)
    (hprev : ∀ x y, d x y < t →
      ¬ ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d (d x y)) S) :
    IsMinRadius d k t := by
  classical
  obtain ⟨x0, y0, hxy⟩ := htT
  have ht0 : 0 ≤ t := by rw [← hxy]; exact hd.nonneg x0 y0
  refine ⟨?_, fun τ hτt hex => ?_⟩
  · rw [exists_surjective_validClustering_iff d t hd ht0 hk]
    exact (exists_validClustering_iff_exists_dominating d t hd ht0 k).2 ht
  · obtain ⟨f, -, hf⟩ := hex
    obtain ⟨c, hcx, hc⟩ := hf x0
    have hτ0 : 0 ≤ τ := by
      have := hc c hcx
      rwa [hd.self] at this
    obtain ⟨S, hSk, hS⟩ := exists_dominating_of_validClustering d τ f hf
    obtain ⟨p, hp, hpmax⟩ :=
      (Finset.univ.filter (fun p : X × X => d p.1 p.2 ≤ τ)).exists_max_image
        (fun p => d p.1 p.2) ⟨(x0, x0), by simp [hd.self, hτ0]⟩
    have hpτ : d p.1 p.2 ≤ τ := (Finset.mem_filter.1 hp).2
    have hG : thresholdGraph d (d p.1 p.2) = thresholdGraph d τ :=
      thresholdGraph_congr d fun u v =>
        ⟨fun h => h.trans hpτ, fun h => hpmax (u, v) (by simp [h])⟩
    refine hprev p.1 p.2 (lt_of_le_of_lt hpτ hτt) ⟨S, hSk, ?_⟩
    rw [hG]
    exact hS

theorem isDerivedFrom_lastDominable
    (d : X → X → α) (hd : IsDissimilarity d) {k : ℕ} (t : α)
    (htT : ∃ x y, d x y = t)
    (hprev : ∀ x y, d x y < t →
      ¬ ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d (d x y)) S)
    (S : Finset X) (hS : IsDominating (thresholdGraph d t) S) (hSk : S.card = k)
    (hmin : ∀ S' : Finset X, IsDominating (thresholdGraph d t) S' → S.card ≤ S'.card)
    {m : ℕ} (f : X → Fin m) (hf : IsDerivedFrom d S f) :
    IsValidClustering d t f ∧ (Finset.univ.image f).card = k ∧ IsMinRadius d k t := by
  obtain ⟨x0, y0, hxy⟩ := htT
  have ht0 : 0 ≤ t := by rw [← hxy]; exact hd.nonneg x0 y0
  have hC := hf.isCentreSet hd ht0 hS
  obtain ⟨-, hcard⟩ := hC.dominating_card d t
  refine ⟨fun y => ?_, by rw [← hcard]; exact hSk,
    isMinRadius_of_lastDominable d hd ?_ t ⟨x0, y0, hxy⟩ ⟨S, hSk.le, hS⟩ hprev⟩
  · obtain ⟨c, -, hc, hcz⟩ := hC.2 y
    exact ⟨c, hc, hcz⟩
  · rw [← hSk]
    exact Finset.card_le_univ S

omit [Fintype X] in

theorem exists_validClustering_one_iff [Nonempty X] (d : X → X → α) (hd : IsDissimilarity d)
    (τ : α) (hτ : 0 ≤ τ) :
    (∃ f : X → Fin 1, IsValidClustering d τ f) ↔ ∃ y, ∀ x, d y x ≤ τ := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨c, -, hc⟩ := hf (Classical.arbitrary X)
    exact ⟨c, fun x => hc x (Subsingleton.elim _ _)⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => 0, fun _ => ⟨y, rfl, fun z _ => hy z⟩⟩

end RadiusClustering

end M_RadiusClustering_Curgraph
section M_RadiusClustering_Fig34

namespace RadiusClustering

def fig34 : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 1, 4],
    ![2, 0, 1, 4],
    ![1, 1, 0, 4],
    ![4, 4, 4, 0]]

theorem fig34_isDissimilarity : IsDissimilarity fig34 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem fig34_eq_of_le_zero : ∀ x y : Fin 4, fig34 x y ≤ 0 → x = y := by
  decide

theorem fig34_injective_of_valid_zero {k : ℕ} {τ : ℕ} (hτ : τ < 1) {f : Fin 4 → Fin k}
    (hf : IsValidClustering fig34 τ f) : Function.Injective f := by
  intro a b hab
  obtain ⟨c, -, hc⟩ := hf a
  have ha := fig34_eq_of_le_zero c a (by have := hc a rfl; omega)
  have hb := fig34_eq_of_le_zero c b (by have := hc b hab.symm; omega)
  rw [← ha, ← hb]

theorem fig34_minRadius :
    IsMinRadius fig34 1 4 ∧ IsMinRadius fig34 2 1 ∧ IsMinRadius fig34 4 0 := by
  refine ⟨⟨⟨fun _ => 0, fun i => ⟨0, Subsingleton.elim _ _⟩, ?_⟩, fun τ hτ hex => ?_⟩,
    ⟨⟨![0, 0, 0, 1], by decide, ?_⟩, fun τ hτ hex => ?_⟩,
    ⟨⟨id, Function.surjective_id, ?_⟩, fun τ hτ => absurd hτ (Nat.not_lt_zero τ)⟩⟩
  · unfold IsValidClustering
    decide
  · obtain ⟨f, -, hf⟩ := hex
    obtain ⟨c, -, hc⟩ := hf 0
    have h0 := hc 0 (Subsingleton.elim _ _)
    have h3 := hc 3 (Subsingleton.elim _ _)
    fin_cases c <;> simp [fig34] at h0 h3 <;> omega
  · unfold IsValidClustering
    decide
  · obtain ⟨f, -, hf⟩ := hex
    have := Fintype.card_le_of_injective f (fig34_injective_of_valid_zero hτ hf)
    simp at this
  · unfold IsValidClustering
    decide

end RadiusClustering

end M_RadiusClustering_Fig34
section M_RadiusClustering_PEqualNP_Clust

namespace RadiusClustering.Clust

def encNat (a : ℕ) : List Bool :=
  (a.bits.flatMap fun b => [true, b]) ++ [false, true]

def encRow (row : List ℕ) : List Bool :=
  row.flatMap encNat ++ [false, false]

def encInst (k τ : ℕ) (M : List (List ℕ)) : List Bool :=
  encNat k ++ encNat τ ++ M.flatMap encRow

def IsTriangular (M : List (List ℕ)) : Prop :=
  ∀ i : Fin M.length, (M.get i).length = M.length - 1 - i.val

def triDissim (M : List (List ℕ)) (i j : Fin M.length) : ℕ :=
  if i < j then (M.get i).getD (j.val - i.val - 1) 0
  else if j < i then (M.get j).getD (i.val - j.val - 1) 0
  else 0

def clustLang : Set (List Bool) :=
  {x | ∃ (M : List (List ℕ)) (k τ : ℕ), x = encInst k τ M ∧ IsTriangular M ∧
    ∃ f : Fin M.length → Fin k, IsValidClustering (triDissim M) τ f}

def toTri {n : ℕ} (d : Fin n → Fin n → ℕ) : List (List ℕ) :=
  List.ofFn fun i : Fin n => List.ofFn fun j : Fin (n - 1 - i.val) =>
    d i ⟨i.val + 1 + j.val, by omega⟩

theorem clustLang_eq_inline :
    clustLang =
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
        ∃ f : Fin M.length → Fin k, ∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ} :=
  rfl

theorem isDissimilarity_triDissim (M : List (List ℕ)) : IsDissimilarity (triDissim M) := by
  refine ⟨fun i => by simp [triDissim], fun _ _ => Nat.zero_le _, fun i j => ?_⟩
  unfold triDissim
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.2 h.le]
  · subst h; simp
  · simp [h, not_lt.2 h.le]

theorem length_toTri {n : ℕ} (d : Fin n → Fin n → ℕ) : (toTri d).length = n := by
  simp [toTri]

theorem getElem_toTri {n : ℕ} (d : Fin n → Fin n → ℕ) (i : ℕ) (hi : i < (toTri d).length) :
    (toTri d)[i] = List.ofFn fun j : Fin (n - 1 - i) =>
      d ⟨i, by simp [length_toTri] at hi; exact hi⟩ ⟨i + 1 + j.val, by omega⟩ := by
  simp [toTri]

theorem isTriangular_toTri {n : ℕ} (d : Fin n → Fin n → ℕ) : IsTriangular (toTri d) := by
  intro i
  rw [List.get_eq_getElem, getElem_toTri, List.length_ofFn]
  simp [length_toTri]

theorem triDissim_toTri {n : ℕ} {d : Fin n → Fin n → ℕ} (hd : IsDissimilarity d)
    (i j : Fin (toTri d).length) :
    triDissim (toTri d) i j = d (i.cast (length_toTri d)) (j.cast (length_toTri d)) := by
  have hn := length_toTri d
  unfold triDissim
  rcases lt_trichotomy i j with h | h | h
  · have h' : i.val < j.val := h
    simp only [h, ↓reduceIte, List.get_eq_getElem, getElem_toTri, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn]
    simp only [show (j : ℕ) - i - 1 < n - 1 - i by omega, ↓reduceDIte, Option.getD_some]
    congr 1
    simp [Fin.ext_iff]
    omega
  · subst h
    simp [hd.self]
  · have h' : j.val < i.val := h
    simp only [not_lt.2 h.le, h, ↓reduceIte, List.get_eq_getElem, getElem_toTri,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [show (i : ℕ) - j - 1 < n - 1 - j by omega, ↓reduceDIte, Option.getD_some]
    rw [hd.symm]
    congr 1
    simp [Fin.ext_iff]
    omega

theorem toTri_triDissim {M : List (List ℕ)} (hM : IsTriangular M) :
    toTri (triDissim M) = M := by
  apply List.ext_getElem (length_toTri _)
  intro i h₁ h₂
  have hrow := hM ⟨i, h₂⟩
  simp only [List.get_eq_getElem] at hrow
  rw [getElem_toTri]
  apply List.ext_getElem
  · simp [hrow]
  · intro j hj₁ hj₂
    simp only [List.getElem_ofFn, triDissim]
    have hlt : (⟨i, h₂⟩ : Fin M.length) < ⟨i + 1 + j, by simp at hj₁; omega⟩ := by
      simp [Fin.lt_def]; omega
    simp only [hlt, ↓reduceIte, List.get_eq_getElem, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1
    omega

theorem isValidClustering_comp_equiv {m n k : ℕ} (e : Fin m ≃ Fin n) {d : Fin n → Fin n → ℕ}
    {d' : Fin m → Fin m → ℕ} (hdd' : ∀ i j, d' i j = d (e i) (e j)) {τ : ℕ} (f : Fin n → Fin k)
    (hf : IsValidClustering d τ f) : IsValidClustering d' τ (f ∘ e) := by
  intro y
  obtain ⟨c, hc, hcz⟩ := hf (e y)
  refine ⟨e.symm c, by simp [hc], fun z hz => ?_⟩
  rw [hdd', Equiv.apply_symm_apply]
  exact hcz (e z) hz

theorem mem_clustLang_iff (x : List Bool) :
    x ∈ clustLang ↔ ∃ (n k τ : ℕ) (d : Fin n → Fin n → ℕ), IsDissimilarity d ∧
      x = encInst k τ (toTri d) ∧ ∃ f : Fin n → Fin k, IsValidClustering d τ f := by
  constructor
  · rintro ⟨M, k, τ, rfl, hM, f, hf⟩
    exact ⟨M.length, k, τ, triDissim M, isDissimilarity_triDissim M, by rw [toTri_triDissim hM],
      f, hf⟩
  · rintro ⟨n, k, τ, d, hd, rfl, f, hf⟩
    refine ⟨toTri d, k, τ, rfl, isTriangular_toTri d, ?_⟩
    let e : Fin (toTri d).length ≃ Fin n := finCongr (length_toTri d)
    exact ⟨f ∘ e, isValidClustering_comp_equiv e (fun i j => triDissim_toTri hd i j) f hf⟩

end RadiusClustering.Clust

end M_RadiusClustering_PEqualNP_Clust
section M_ClustNP_Defs

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.S2D (incB dig)

def leP : List Bool → List Bool → Bool → Bool
  | true :: x :: A, true :: y :: B, acc => leP A B (if x == y then acc else y)
  | true :: _, _, _ => false
  | _, true :: _, _ => true
  | _, _, acc => acc

def f1 (s : List Bool) : List Bool := if s.head? = some true then [true] else []

def leStep (s : List Bool) : List Bool :=
  sel (hd (unpairB s).1)
    (sel (hd (unpairB (unpairB s).2).1)
      (pairB [] (pairB [] (unpairB (unpairB s).2).2))
      (pairB [] (pairB [] [true])))
    (sel (hd (unpairB (unpairB s).2).1)
      (pairB [] (pairB [] []))
      (pairB (unpairB s).1.tail.tail (pairB (unpairB (unpairB s).2).1.tail.tail
        (sel (bflag (decide (f1 (unpairB s).1.tail = f1 (unpairB (unpairB s).2).1.tail)))
          (f1 (unpairB (unpairB s).2).1.tail) (unpairB (unpairB s).2).2))))

def leF (A B : List Bool) : List Bool :=
  (unpairB (unpairB (leStep^[(A ++ B).length] (pairB A (pairB B [true])))).2).2

def endsU : List Bool → List Bool
  | false :: false :: r => true :: endsU r
  | _ :: _ :: r => endsU r
  | _ => []

def dropRow : List Bool → List Bool
  | false :: false :: r => r
  | _ :: _ :: r => dropRow r
  | _ => []

def rowLenU : List Bool → List Bool
  | false :: false :: _ => []
  | false :: true :: r => true :: rowLenU r
  | _ :: _ :: r => rowLenU r
  | _ => []

def rowsS (x : List Bool) : List Bool := dropI (dropI x)

def entryS (us uy x : List Bool) : List Bool :=
  headI (dropI^[(List.tail^[(true :: us).length] uy).length] (dropRow^[us.length] (rowsS x)))

inductive Ph : Type
  | kC | kD | tC | tD | R | O | rC | rD | dead
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{.kC, .kD, .tC, .tD, .R, .O, .rC, .rD, .dead}, fun q => by cases q <;> simp⟩

def phD : Ph → Bool → Bool → Ph
  | .kC, true, d => if d then .kC else .kD
  | .kC, false, true => .tC
  | .kD, true, d => if d then .kC else .kD
  | .tC, true, d => if d then .tC else .tD
  | .tC, false, true => .R
  | .tD, true, d => if d then .tC else .tD
  | .R, true, d => if d then .rC else .rD
  | .R, false, true => .O
  | .R, false, false => .R
  | .O, true, d => if d then .rC else .rD
  | .O, false, true => .O
  | .O, false, false => .R
  | .rC, true, d => if d then .rC else .rD
  | .rC, false, true => .O
  | .rD, true, d => if d then .rC else .rD
  | _, _, _ => .dead

def wfD : Ph × Option Bool → Bool → Ph × Option Bool
  | (p, none), a => (p, some a)
  | (p, some a), b => (phD p a b, none)

def wfI (x : List Bool) : Bool := decide (x.foldl wfD (.kC, none) = (.R, none))

def triRow (z : List Bool) : List Bool :=
  bflag (!decide (rowLenU (dropRow^[(unpairB z).1.length] (rowsS (unpairB z).2)) ++
    true :: (unpairB z).1 = endsU (unpairB z).2))

def triBad (x : List Bool) : List Bool :=
  (List.range (endsU x).length).flatMap fun i => triRow (pairB (un i) x)

def trues (w : List Bool) : List Bool := w.filter id

def cntS (w : List Bool) : List Bool := dig (incB^[(trues w).length] []) ++ [false, true]

def covers (us uy x w : List Bool) : Bool :=
  !(f1 (List.tail^[us.length] w)).isEmpty &&
    (decide (us = uy) ||
      !(leF (if us.length < uy.length then entryS us uy x else entryS uy us x)
        (headI (dropI x))).isEmpty)

def covRow (z : List Bool) : List Bool :=
  bflag (covers (unpairB z).1 (unpairB (unpairB z).2).1
    (unpairB (unpairB (unpairB z).2).2).1 (unpairB (unpairB (unpairB z).2).2).2)

def uncov (z : List Bool) : List Bool :=
  bflag ((List.range (endsU (unpairB (unpairB z).2).1).length).flatMap
    (fun s => covRow (pairB (un s) z))).isEmpty

def uncovAll (x w : List Bool) : List Bool :=
  (List.range (endsU x).length).flatMap fun y => uncov (pairB (un y) (pairB x w))

def CV (p : List Bool × List Bool) : Bool :=
  wfI p.1 && (triBad p.1).isEmpty && !(leF (cntS p.2) (headI p.1)).isEmpty &&
    (uncovAll p.1 p.2).isEmpty

end ClustNP

end M_ClustNP_Defs
section M_RadiusClustering_PEqualNP_SatGadget

namespace RadiusClustering.Clust

abbrev GadgetV (N m : ℕ) : Type := (Fin N × Option Bool) ⊕ Fin m

def gadgetRel (φ : List (List (ℕ × Bool))) (N : ℕ) :
    GadgetV N φ.length → GadgetV N φ.length → Prop
  | .inl (i, _), .inl (i', _) => i = i'
  | .inl (i, some b), .inr j => ((i : ℕ), b) ∈ φ.get j
  | _, _ => False

def satGadget (φ : List (List (ℕ × Bool))) (N : ℕ) : SimpleGraph (GadgetV N φ.length) :=
  SimpleGraph.fromRel (gadgetRel φ N)

theorem satisfiable_iff_exists_dominating (φ : List (List (ℕ × Bool))) (N : ℕ)
    (hN : ∀ c ∈ φ, ∀ l ∈ c, l.1 < N) :
    (∃ σ : ℕ → Bool, (φ.all fun c => c.any fun l => σ l.1 == l.2) = true) ↔
      ∃ S : Finset (GadgetV N φ.length), S.card ≤ N ∧ IsDominating (satGadget φ N) S := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨Finset.univ.image fun i : Fin N =>
      (Sum.inl (i, some (σ i)) : GadgetV N φ.length), Finset.card_image_le.trans (by simp), ?_⟩
    intro v
    rcases v with ⟨i, o⟩ | j
    · by_cases ho : o = some (σ i)
      · subst ho
        exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      · refine Or.inr ⟨Sum.inl (i, some (σ i)), Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩
        simp only [satGadget, SimpleGraph.fromRel_adj]
        refine ⟨fun h => ho (by simp at h; exact h.symm), Or.inl ?_⟩
        simp [gadgetRel]
    · have hc : (φ.get j).any (fun l => σ l.1 == l.2) = true := by
        rw [List.all_eq_true] at hσ
        exact hσ _ (List.get_mem _ _)
      rw [List.any_eq_true] at hc
      obtain ⟨l, hl, hσl⟩ := hc
      have hlN := hN _ (List.get_mem _ _) l hl
      refine Or.inr ⟨Sum.inl (⟨l.1, hlN⟩, some (σ l.1)),
        Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      simp only [satGadget, SimpleGraph.fromRel_adj]
      refine ⟨Sum.inl_ne_inr, Or.inl ?_⟩
      have hσl' : σ l.1 = l.2 := by simpa using hσl
      simpa [gadgetRel, hσl'] using hl
  · rintro ⟨S, hSN, hS⟩
    have h1 : ∀ i : Fin N, ∃ o, (Sum.inl (i, o) : GadgetV N φ.length) ∈ S := by
      intro i
      rcases hS (Sum.inl (i, none)) with h | ⟨s, hs, hadj⟩
      · exact ⟨none, h⟩
      · simp only [satGadget, SimpleGraph.fromRel_adj] at hadj
        rcases s with ⟨i', o'⟩ | j
        · have hii : i' = i := by
            rcases hadj.2 with h | h
            · simpa [gadgetRel] using h
            · simpa [gadgetRel] using h.symm
          subst hii
          exact ⟨o', hs⟩
        · rcases hadj.2 with h | h <;> simp [gadgetRel] at h
    choose o ho using h1
    let G : Finset (GadgetV N φ.length) := Finset.univ.image fun i => Sum.inl (i, o i)
    have hGS : G ⊆ S := by
      intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact ho i
    have hGcard : G.card = N := by
      rw [Finset.card_image_of_injective _ (fun a b h => by simp at h; exact h.1)]
      simp
    have hGeq : G = S := Finset.eq_of_subset_of_card_le hGS (by omega)
    refine ⟨fun n => if h : n < N then o ⟨n, h⟩ == some true else false, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hc
    rcases hS (Sum.inr j) with h | ⟨s, hs, hadj⟩
    · rw [← hGeq] at h
      simp [G] at h
    · rw [← hGeq] at hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      simp only [satGadget, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · cases hoi : o i with
        | none =>
          rw [hoi] at h
          simp [gadgetRel] at h
        | some b =>
          rw [hoi] at h
          simp only [gadgetRel] at h
          rw [List.any_eq_true]
          refine ⟨((i : ℕ), b), h, ?_⟩
          cases b <;> simp [hoi]
      · simp [gadgetRel] at h

end RadiusClustering.Clust

end M_RadiusClustering_PEqualNP_SatGadget
section M_RadiusClustering_PEqualNP_Injective

namespace RadiusClustering.Clust

private theorem digits_prefix (L L' : List Bool) (r s : List Bool)
    (h : (L.flatMap fun b => [true, b]) ++ [false, true] ++ r
      = (L'.flatMap fun b => [true, b]) ++ [false, true] ++ s) : L = L' ∧ r = s := by
  induction L generalizing L' with
  | nil => cases L' <;> simp_all
  | cons x L ih =>
    cases L' with
    | nil => simp at h
    | cons y L' =>
      simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.cons.injEq,
        true_and] at h
      obtain ⟨rfl, h⟩ := h
      have := ih L' (by simpa [List.append_assoc] using h)
      simp [this]

private theorem bits_inj {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  have : Nat.digits 2 a = Nat.digits 2 b := by
    rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits, h]
  exact Nat.digits_inj_iff.mp this

private theorem encNat_prefix {a b : ℕ} {r s : List Bool}
    (h : encNat a ++ r = encNat b ++ s) : a = b ∧ r = s := by
  unfold encNat at h
  obtain ⟨h1, h2⟩ := digits_prefix _ _ _ _ (by simpa [List.append_assoc] using h)
  exact ⟨bits_inj h1, h2⟩

private theorem encNat_cons (a : ℕ) (r : List Bool) :
    (∃ t, encNat a ++ r = true :: t) ∨ encNat a ++ r = false :: true :: r := by
  unfold encNat
  cases a.bits <;> simp

private theorem encRow_prefix (row row' : List ℕ) (r s : List Bool)
    (h : encRow row ++ r = encRow row' ++ s) : row = row' ∧ r = s := by
  induction row generalizing row' with
  | nil =>
    cases row' with
    | nil => simpa [encRow] using h
    | cons b row' =>
      exfalso
      simp only [encRow, List.flatMap_cons, List.flatMap_nil, List.nil_append,
        List.append_assoc] at h
      rcases encNat_cons b (row'.flatMap encNat ++ ([false, false] ++ s)) with ⟨t, ht⟩ | ht
      · rw [ht] at h
        simp at h
      · rw [ht] at h
        simp at h
  | cons a row ih =>
    cases row' with
    | nil =>
      exfalso
      simp only [encRow, List.flatMap_cons, List.flatMap_nil, List.nil_append,
        List.append_assoc] at h
      rcases encNat_cons a (row.flatMap encNat ++ ([false, false] ++ r)) with ⟨t, ht⟩ | ht
      · rw [ht] at h
        simp at h
      · rw [ht] at h
        simp at h
    | cons b row' =>
      simp only [encRow, List.flatMap_cons, List.append_assoc] at h
      obtain ⟨e, h3⟩ := encNat_prefix h
      obtain ⟨h1, h2⟩ := ih row' (by simpa [encRow, List.append_assoc] using h3)
      simp [e, h1, h2]

private theorem flatMap_encRow_inj (M M' : List (List ℕ))
    (h : M.flatMap encRow = M'.flatMap encRow) : M = M' := by
  induction M generalizing M' with
  | nil =>
    cases M' with
    | nil => rfl
    | cons b M' => simp [encRow] at h
  | cons a M ih =>
    cases M' with
    | nil => simp [encRow] at h
    | cons b M' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨e, h2⟩ := encRow_prefix _ _ _ _ h
      rw [e, ih M' h2]

theorem encInst_injective {k τ k' τ' : ℕ} {M M' : List (List ℕ)}
    (h : encInst k τ M = encInst k' τ' M') : k = k' ∧ τ = τ' ∧ M = M' := by
  unfold encInst at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨e1, h2⟩ := encNat_prefix h
  obtain ⟨e2, h3⟩ := encNat_prefix h2
  exact ⟨e1, e2, flatMap_encRow_inj _ _ h3⟩

end RadiusClustering.Clust

end M_RadiusClustering_PEqualNP_Injective
section M_RadiusClustering_FromGraph

namespace RadiusClustering

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in

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

theorem isDissimilarity_graphDissim : IsDissimilarity (graphDissim G) := by
  refine ⟨fun x => by simp [graphDissim], fun x y => Nat.zero_le _, fun x y => ?_⟩
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := Ne.symm h
    have : G.Adj x y ↔ G.Adj y x := ⟨fun a => a.symm, fun a => a.symm⟩
    simp [graphDissim, h, h', this]

theorem exists_dominating_iff_exists_validClustering_graphDissim (k : ℕ) :
    (∃ S : Finset V, S.card ≤ k ∧ IsDominating G S) ↔
      ∃ f : V → Fin k, IsValidClustering (graphDissim G) 1 f := by
  have h := exists_validClustering_iff_exists_dominating (graphDissim G) 1
    (isDissimilarity_graphDissim G) zero_le_one k
  rw [thresholdGraph_graphDissim] at h
  exact h.symm

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

end M_RadiusClustering_FromGraph
section M_RadiusClustering_PEqualNP_SatToClust

namespace RadiusClustering.Clust

theorem isValidClustering_comp_equiv' {X Y : Type*} (e : X ≃ Y) {d : Y → Y → ℕ}
    {d' : X → X → ℕ} (hdd' : ∀ i j, d' i j = d (e i) (e j)) {τ k : ℕ} (f : Y → Fin k)
    (hf : IsValidClustering d τ f) : IsValidClustering d' τ (f ∘ e) := by
  intro y
  obtain ⟨c, hc, hcz⟩ := hf (e y)
  refine ⟨e.symm c, by simp [hc], fun z hz => ?_⟩
  rw [hdd', Equiv.apply_symm_apply]
  exact hcz (e z) hz

open Classical in

noncomputable def gadgetDissim (φ : List (List (ℕ × Bool))) (N : ℕ) :
    Fin (Fintype.card (GadgetV N φ.length)) → Fin (Fintype.card (GadgetV N φ.length)) → ℕ :=
  fun i j => graphDissim (satGadget φ N) ((Fintype.equivFin _).symm i)
    ((Fintype.equivFin _).symm j)

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

end RadiusClustering.Clust

end M_RadiusClustering_PEqualNP_SatToClust
section M_RadiusClustering_PEqualNP_ItemGadget

namespace RadiusClustering.Clust

def items (φ : List (List (ℕ × Bool))) : List (Option (ℕ × Bool)) :=
  φ.flatMap fun c => c.map some ++ [none]

def IsRep (its : List (Option (ℕ × Bool))) (p : ℕ) (l : ℕ × Bool) : Prop :=
  its[p]? = some (some l) ∧ ∀ q < p, ∀ l', its[q]? = some (some l') → l'.1 ≠ l.1

def InSeg (its : List (Option (ℕ × Bool))) (p : ℕ) (l : ℕ × Bool) : Prop :=
  ∃ r < p, its[r]? = some (some l) ∧ ∀ r', r < r' → r' < p → its[r']? ≠ some none

def itemRel (its : List (Option (ℕ × Bool))) (i j : ℕ) : Prop :=
  if i / 3 = j / 3 then (i % 3 < 2 ∧ j % 3 < 2) ∨ ∃ l, its[i / 3]? = some (some l)
  else i % 3 < 2 ∧ j % 3 = 2 ∧ its[j / 3]? = some none ∧
    ∃ l, IsRep its (i / 3) l ∧ InSeg its (j / 3) (l.1, decide (i % 3 = 0))

def itemGadget (its : List (Option (ℕ × Bool))) : SimpleGraph (Fin (3 * its.length)) :=
  SimpleGraph.fromRel fun i j => itemRel its i j

private theorem getElem?_pre_lt {c : List (ℕ × Bool)} {rest : List (Option (ℕ × Bool))}
    {r : ℕ} (hr : r < c.length) : (c.map some ++ none :: rest)[r]? = some (some c[r]) := by
  rw [List.getElem?_append_left (by simpa using hr)]
  simp [hr]

private theorem getElem?_pre_eq {c : List (ℕ × Bool)} {rest : List (Option (ℕ × Bool))} :
    (c.map some ++ none :: rest)[c.length]? = some none := by
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem getElem?_pre_gt {c : List (ℕ × Bool)} {rest : List (Option (ℕ × Bool))}
    (p : ℕ) : (c.map some ++ none :: rest)[p + c.length + 1]? = rest[p]? := by
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map]
  rw [show p + c.length + 1 - c.length = p + 1 by omega]
  simp

private theorem inSeg_here (c : List (ℕ × Bool)) (rest : List (Option (ℕ × Bool)))
    (l : ℕ × Bool) : InSeg (c.map some ++ none :: rest) c.length l ↔ l ∈ c := by
  constructor
  · rintro ⟨r, hr, hl, -⟩
    rw [getElem?_pre_lt hr] at hl
    simp only [Option.some.injEq] at hl
    rw [← hl]
    exact List.getElem_mem hr
  · intro hl
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hl
    refine ⟨r, hr, getElem?_pre_lt hr, fun r' _ hr' => ?_⟩
    rw [getElem?_pre_lt hr']
    simp

private theorem inSeg_shift (c : List (ℕ × Bool)) (rest : List (Option (ℕ × Bool)))
    (p : ℕ) (l : ℕ × Bool) :
    InSeg (c.map some ++ none :: rest) (p + c.length + 1) l ↔ InSeg rest p l := by
  constructor
  · rintro ⟨r, hr, hl, hno⟩
    by_cases hrc : r ≤ c.length
    · exfalso
      rcases Nat.lt_or_eq_of_le hrc with h | h
      · exact hno c.length h (by omega) getElem?_pre_eq
      · subst h
        rw [getElem?_pre_eq] at hl
        simp at hl
    · obtain ⟨r, rfl⟩ : ∃ r', r = r' + c.length + 1 := ⟨r - c.length - 1, by omega⟩
      refine ⟨r, by omega, by rwa [getElem?_pre_gt] at hl, fun r' h1 h2 => ?_⟩
      have := hno (r' + c.length + 1) (by omega) (by omega)
      rwa [getElem?_pre_gt] at this
  · rintro ⟨r, hr, hl, hno⟩
    refine ⟨r + c.length + 1, by omega, by rwa [getElem?_pre_gt], fun r' h1 h2 => ?_⟩
    obtain ⟨r', rfl⟩ : ∃ r'', r' = r'' + c.length + 1 := ⟨r' - c.length - 1, by omega⟩
    rw [getElem?_pre_gt]
    exact hno r' (by omega) (by omega)

private theorem items_cons (c : List (ℕ × Bool)) (φ : List (List (ℕ × Bool))) :
    items (c :: φ) = c.map some ++ none :: items φ := by
  simp [items]

theorem exists_inSeg_of_mem (φ : List (List (ℕ × Bool))) :
    ∀ c ∈ φ, ∃ p, (items φ)[p]? = some none ∧ ∀ l, InSeg (items φ) p l ↔ l ∈ c := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    intro c' hc'
    rw [items_cons]
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨c'.length, getElem?_pre_eq, inSeg_here c' _⟩
    · obtain ⟨p, hp, hseg⟩ := ih c' hc'
      refine ⟨p + c.length + 1, by rwa [getElem?_pre_gt], fun l => ?_⟩
      rw [inSeg_shift]
      exact hseg l

theorem exists_mem_of_inSeg (φ : List (List (ℕ × Bool))) :
    ∀ p, (items φ)[p]? = some none → ∃ c ∈ φ, ∀ l, InSeg (items φ) p l ↔ l ∈ c := by
  induction φ with
  | nil => simp [items]
  | cons c φ ih =>
    intro p hp
    rw [items_cons] at hp ⊢
    rcases lt_trichotomy p c.length with h | rfl | h
    · rw [getElem?_pre_lt h] at hp
      simp at hp
    · exact ⟨c, List.mem_cons_self .., inSeg_here c _⟩
    · obtain ⟨p, rfl⟩ : ∃ p', p = p' + c.length + 1 := ⟨p - c.length - 1, by omega⟩
      rw [getElem?_pre_gt] at hp
      obtain ⟨c', hc', hseg⟩ := ih p hp
      refine ⟨c', List.mem_cons_of_mem _ hc', fun l => ?_⟩
      rw [inSeg_shift]
      exact hseg l

theorem exists_isRep {its : List (Option (ℕ × Bool))} {q : ℕ} {l : ℕ × Bool}
    (hq : its[q]? = some (some l)) : ∃ r l', IsRep its r l' ∧ l'.1 = l.1 := by
  classical
  have hex : ∃ r, ∃ l' : ℕ × Bool, its[r]? = some (some l') ∧ l'.1 = l.1 := ⟨q, l, hq, rfl⟩
  obtain ⟨l', hl', hv⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, l', ⟨hl', fun q' hq' l'' hl'' he => ?_⟩, hv⟩
  exact Nat.find_min hex hq' ⟨l'', hl'', he.trans hv⟩

theorem IsRep.unique {its : List (Option (ℕ × Bool))} {r r' : ℕ} {l l' : ℕ × Bool}
    (h : IsRep its r l) (h' : IsRep its r' l') (hv : l.1 = l'.1) : r = r' := by
  rcases lt_trichotomy r r' with hlt | heq | hlt
  · exact absurd hv (h'.2 r hlt l h.1)
  · exact heq
  · exact absurd hv.symm (h.2 r' hlt l' h'.1)

private theorem getElem?_isSome {its : List (Option (ℕ × Bool))} {p : ℕ} (hp : p < its.length) :
    (∃ l, its[p]? = some (some l)) ∨ its[p]? = some none := by
  rw [List.getElem?_eq_getElem hp]
  rcases its[p] with _ | l
  · exact Or.inr rfl
  · exact Or.inl ⟨l, rfl⟩

private theorem adj_iff {its : List (Option (ℕ × Bool))} (u v : Fin (3 * its.length)) :
    (itemGadget its).Adj u v ↔ u ≠ v ∧ (itemRel its u v ∨ itemRel its v u) :=
  SimpleGraph.fromRel_adj _ _ _

private theorem block_of_adj {its : List (Option (ℕ × Bool))} {s v : Fin (3 * its.length)}
    (hadj : (itemGadget its).Adj s v)
    (hv : (v.val % 3 = 2 ∧ ∃ l, its[v.val / 3]? = some (some l)) ∨
      (v.val % 3 = 1 ∧ its[v.val / 3]? = some none)) : s.val / 3 = v.val / 3 := by
  by_contra hne
  have hne' : v.val / 3 ≠ s.val / 3 := Ne.symm hne
  rw [adj_iff] at hadj
  rcases hadj.2 with h | h
  · simp only [itemRel, hne, ↓reduceIte] at h
    obtain ⟨-, h2, hnone, -⟩ := h
    rcases hv with ⟨-, l, hl⟩ | ⟨h1, -⟩
    · rw [hl] at hnone; simp at hnone
    · omega
  · simp only [itemRel, hne', ↓reduceIte] at h
    obtain ⟨h1, -, -, l, hrep, -⟩ := h
    rcases hv with ⟨h2, -⟩ | ⟨-, hnone⟩
    · omega
    · rw [hrep.1] at hnone; simp at hnone

theorem satisfiable_iff_exists_dominating_items (φ : List (List (ℕ × Bool))) :
    (∃ σ : ℕ → Bool, (φ.all fun c => c.any fun l => σ l.1 == l.2) = true) ↔
      ∃ S : Finset (Fin (3 * (items φ).length)), S.card ≤ (items φ).length ∧
        IsDominating (itemGadget (items φ)) S := by
  classical
  set its := items φ with hits
  set L := its.length

  let vx : ∀ p, p < L → ∀ t, t < 3 → Fin (3 * L) := fun p hp t ht => ⟨3 * p + t, by omega⟩
  have vx_div : ∀ p hp t ht, (vx p hp t ht).val / 3 = p := fun p _ t _ => by
    simp only [vx]; omega
  have vx_mod : ∀ p hp t ht, (vx p hp t ht).val % 3 = t := fun p _ t _ => by
    simp only [vx]; omega
  constructor
  · rintro ⟨σ, hσ⟩

    let role : ℕ → ℕ := fun p => match its[p]? with
      | some (some l) => if σ l.1 then 0 else 1
      | _ => 0
    have role_lt : ∀ p, role p < 3 := fun p => by
      simp only [role]; split <;> (try split) <;> omega
    let pick : Fin L → Fin (3 * L) := fun p => vx p p.2 (role p) (role_lt p)
    have pick_div : ∀ q : Fin L, (pick q).val / 3 = q.val := fun q => vx_div q q.2 _ (role_lt q)
    have pick_mod : ∀ q : Fin L, (pick q).val % 3 = role q := fun q => vx_mod q q.2 _ (role_lt q)
    refine ⟨Finset.univ.image pick, Finset.card_image_le.trans (by simp [L]), fun v => ?_⟩
    have hvL : v.val / 3 < L := by omega
    by_cases hin : v ∈ Finset.univ.image pick
    · exact Or.inl hin
    right
    have hpv : (pick ⟨v.val / 3, hvL⟩).val / 3 = v.val / 3 := pick_div _
    have hne : pick ⟨v.val / 3, hvL⟩ ≠ v := fun h => hin (h ▸ Finset.mem_image_of_mem _ (by simp))
    rcases getElem?_isSome hvL with ⟨l, hl⟩ | hnone
    ·
      refine ⟨pick ⟨v.val / 3, hvL⟩, Finset.mem_image_of_mem _ (by simp), ?_⟩
      rw [adj_iff]
      refine ⟨hne, Or.inl ?_⟩
      simp only [itemRel, hpv, ↓reduceIte]
      exact Or.inr ⟨l, hl⟩
    · have hpick : (pick ⟨v.val / 3, hvL⟩).val % 3 = 0 := by
        rw [pick_mod]; simp [role, hnone]
      by_cases hv2 : v.val % 3 = 2
      ·
        obtain ⟨c, hc, hseg⟩ := exists_mem_of_inSeg φ _ hnone
        rw [← hits] at hseg
        have hcσ : (c.any fun l => σ l.1 == l.2) = true := List.all_eq_true.1 hσ c hc
        obtain ⟨l, hlc, hlσ⟩ := List.any_eq_true.1 hcσ
        have hlσ' : σ l.1 = l.2 := by simpa using hlσ
        obtain ⟨r0, hr0, hr0l, -⟩ := (hseg l).2 hlc
        obtain ⟨r, l', hrep, hvar⟩ := exists_isRep hr0l
        have hrL : r < L := by
          by_contra h
          have := hrep.1
          rw [List.getElem?_eq_none (by omega)] at this
          simp at this
        refine ⟨pick ⟨r, hrL⟩, Finset.mem_image_of_mem _ (by simp), ?_⟩
        have hpr : (pick ⟨r, hrL⟩).val / 3 = r := pick_div _
        have hpm : (pick ⟨r, hrL⟩).val % 3 = if σ l'.1 then 0 else 1 := by
          rw [pick_mod]; simp [role, hrep.1]
        have hrv : r ≠ v.val / 3 := by
          intro h
          have := hrep.1
          rw [h, hnone] at this
          simp at this
        rw [adj_iff]
        refine ⟨fun h => hrv (by rw [← hpr, h]), Or.inl ?_⟩
        simp only [itemRel, hpr, hrv, ↓reduceIte, hpm]
        refine ⟨by split <;> omega, hv2, hnone, l', hrep, ?_⟩
        have hpol : decide ((if σ l'.1 = true then 0 else 1) = 0) = l.2 := by
          rw [hvar, hlσ']; cases l.2 <;> simp
        rw [hpol, hvar]
        exact (hseg l).2 hlc
      ·
        refine ⟨pick ⟨v.val / 3, hvL⟩, Finset.mem_image_of_mem _ (by simp), ?_⟩
        rw [adj_iff]
        refine ⟨hne, Or.inl ?_⟩
        simp only [itemRel, hpv, ↓reduceIte]
        exact Or.inl ⟨by omega, by omega⟩
  · rintro ⟨S, hSL, hS⟩

    have hblock : ∀ p, p < L → ∃ s ∈ S, s.val / 3 = p := by
      intro p hp
      rcases getElem?_isSome hp with ⟨l, hl⟩ | hnone
      · have hv := vx_div p hp 2 (by omega)
        rcases hS (vx p hp 2 (by omega)) with h | ⟨s, hs, hadj⟩
        · exact ⟨_, h, hv⟩
        · refine ⟨s, hs, ?_⟩
          rw [block_of_adj hadj (Or.inl ⟨vx_mod p hp 2 (by omega), l, by rw [hv]; exact hl⟩), hv]
      · have hv := vx_div p hp 1 (by omega)
        rcases hS (vx p hp 1 (by omega)) with h | ⟨s, hs, hadj⟩
        · exact ⟨_, h, hv⟩
        · refine ⟨s, hs, ?_⟩
          rw [block_of_adj hadj (Or.inr ⟨vx_mod p hp 1 (by omega), by rw [hv]; exact hnone⟩), hv]

    have himg : S.image (fun s => s.val / 3) = Finset.range L := by
      apply Finset.eq_of_subset_of_card_le
      · intro p hp
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hp
        simp only [Finset.mem_range]; omega
      · apply Finset.card_le_card
        intro p hp
        obtain ⟨s, hs, rfl⟩ := hblock p (Finset.mem_range.1 hp)
        exact Finset.mem_image_of_mem _ hs
    have hinj : Set.InjOn (fun s : Fin (3 * L) => s.val / 3) S := by
      apply Finset.card_image_iff.1
      have := Finset.card_image_le (s := S) (f := fun s : Fin (3 * L) => s.val / 3)
      rw [himg, Finset.card_range] at this ⊢
      omega
    have huniq : ∀ s ∈ S, ∀ s' ∈ S, s.val / 3 = s'.val / 3 → s = s' :=
      fun s hs s' hs' h => hinj hs hs' h

    refine ⟨fun v => decide (∃ r l, IsRep its r l ∧ l.1 = v ∧ ∃ s ∈ S, s.val = 3 * r), ?_⟩
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨p, hp, hseg⟩ := exists_inSeg_of_mem φ c hc
    rw [← hits] at hp hseg
    have hpL : p < L := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hp
      simp at hp
    have hw2 := vx_div p hpL 2 (by omega)
    have hw1 := vx_div p hpL 1 (by omega)
    rcases hS (vx p hpL 2 (by omega)) with hw | ⟨s, hs, hadj⟩
    ·
      exfalso
      rcases hS (vx p hpL 1 (by omega)) with hu | ⟨s, hs, hadj⟩
      · have := congrArg Fin.val (huniq _ hu _ hw (by rw [hw1, hw2]))
        simp [vx] at this
      · have hsb := block_of_adj hadj (Or.inr ⟨vx_mod p hpL 1 (by omega), by rw [hw1]; exact hp⟩)
        obtain rfl := huniq _ hs _ hw (by rw [hsb, hw1, hw2])
        rw [adj_iff] at hadj
        rcases hadj.2 with h | h <;>
          simp only [itemRel, hw1, hw2, vx_mod, ↓reduceIte, hp] at h <;> simp at h
    · have hsp : s.val / 3 ≠ p := by
        intro h
        rw [adj_iff] at hadj
        rcases hadj.2 with h' | h' <;>
          simp only [itemRel, h, hw2, vx_mod, ↓reduceIte, hp] at h' <;> simp at h'
      rw [adj_iff] at hadj
      rcases hadj.2 with h | h
      · simp only [itemRel, hw2, hsp, ↓reduceIte, vx_mod] at h
        obtain ⟨hs2, -, -, l, hrep, hin⟩ := h
        rw [List.any_eq_true]
        refine ⟨_, (hseg _).1 hin, ?_⟩
        simp only [beq_iff_eq, decide_eq_decide]
        constructor
        · rintro ⟨r, l', hrep', hv, s', hs', hs'r⟩
          obtain rfl := hrep'.unique hrep hv
          obtain rfl := huniq _ hs' _ hs (by omega)
          omega
        · intro h0
          exact ⟨s.val / 3, l, hrep, rfl, s, hs, by omega⟩
      · simp only [itemRel, hw2, Ne.symm hsp, ↓reduceIte, vx_mod] at h
        omega

end RadiusClustering.Clust

namespace RadiusClustering.Clust

open Classical in

noncomputable def itemInst (φ : List (List (ℕ × Bool))) : List Bool :=
  encInst (items φ).length 1 (toTri (graphDissim (itemGadget (items φ))))

theorem satisfiable_iff_itemInst_mem (φ : List (List (ℕ × Bool))) :
    (∃ σ : ℕ → Bool, (φ.all fun c => c.any fun l => σ l.1 == l.2) = true) ↔
      itemInst φ ∈ clustLang := by
  classical
  have hdis := isDissimilarity_graphDissim (itemGadget (items φ))
  rw [satisfiable_iff_exists_dominating_items,
    exists_dominating_iff_exists_validClustering_graphDissim, itemInst]
  constructor
  · rintro ⟨f, hf⟩
    exact (mem_clustLang_iff _).2 ⟨_, _, 1, _, hdis, rfl, f, hf⟩
  · rintro ⟨M, k, τ, h, -, f, hf⟩
    obtain ⟨rfl, rfl, rfl⟩ := encInst_injective h
    let e : Fin (toTri (graphDissim (itemGadget (items φ)))).length ≃
        Fin (3 * (items φ).length) := finCongr (length_toTri _)
    refine ⟨f ∘ e.symm, isValidClustering_comp_equiv e.symm (d := triDissim _) ?_ f hf⟩
    intro u v
    rw [triDissim_toTri hdis]
    simp [e]

end RadiusClustering.Clust

end M_RadiusClustering_PEqualNP_ItemGadget
section M_ClustNP_RedDefs

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.S2D (incB dig)

def itemsU : List Bool → List Bool
  | false :: _ :: r => true :: itemsU r
  | _ :: _ :: r => itemsU r
  | _ => []

def vertsU (x : List Bool) : List Bool := itemsU x ++ itemsU x ++ itemsU x

def div3 (u : List Bool) : List Bool := un (u.length / 3)

def isR0 (u : List Bool) : Bool := decide (u.length % 3 = 0)

def isR2 (u : List Bool) : Bool := decide (u.length % 3 = 2)

def restAt (up x : List Bool) : List Bool := dropI^[up.length] x

def endAt (up x : List Bool) : Bool := isEnd (restAt up x)

def varAt (up x : List Bool) : List Bool := (headI (restAt up x)).tail.tail

def sameVar (z : List Bool) : List Bool :=
  bflag (decide (varAt (unpairB z).1 (unpairB (unpairB z).2).2 =
    varAt (unpairB (unpairB z).2).1 (unpairB (unpairB z).2).2))

def repAt (up x : List Bool) : Bool :=
  !endAt up x &&
    ((List.range up.length).flatMap fun q => sameVar (pairB (un q) (pairB up x))).isEmpty

def segHit (z : List Bool) : List Bool :=
  let r := (unpairB z).1
  let up := (unpairB (unpairB z).2).1
  let lit := (unpairB (unpairB (unpairB z).2).2).1
  let x := (unpairB (unpairB (unpairB z).2).2).2
  bflag (decide (headI (restAt r x) = lit) &&
    decide (endsU (restAt r x) = endsU (restAt up x)))

def segAt (up lit x : List Bool) : Bool :=
  !((List.range up.length).flatMap fun r => segHit (pairB (un r) (pairB up (pairB lit x)))).isEmpty

def crossAt (ui uj x : List Bool) : Bool :=
  !isR2 ui && isR2 uj && endAt (div3 uj) x && repAt (div3 ui) x &&
    segAt (div3 uj) (true :: isR0 ui :: varAt (div3 ui) x) x

def adjAt (ui uj x : List Bool) : Bool :=
  if div3 ui = div3 uj then (!isR2 ui && !isR2 uj) || !endAt (div3 ui) x
  else crossAt ui uj x || crossAt uj ui x

def entryAt (ui uj x : List Bool) : List Bool :=
  sel (bflag (adjAt ui uj x)) [true, false, true, true, false, true] [true, true, false, true]

def cell (z : List Bool) : List Bool :=
  entryAt (unpairB (unpairB z).2).1 ((unpairB (unpairB z).2).1 ++ true :: (unpairB z).1)
    (unpairB (unpairB z).2).2

def rowAt (z : List Bool) : List Bool :=
  ((List.range (List.tail^[((unpairB z).1).length + 1] (vertsU (unpairB z).2)).length).flatMap
    fun j => cell (pairB (un j) z)) ++ [false, false]

def rowsOf (x : List Bool) : List Bool :=
  (List.range (vertsU x).length).flatMap fun i => rowAt (pairB (un i) x)

def red (x : List Bool) : List Bool :=
  sel (bflag (wfB x)) []
    (dig (incB^[(itemsU x).length] []) ++ [false, true] ++ [true, true, false, true] ++ rowsOf x)

end ClustNP

end M_ClustNP_RedDefs
section M_ClustNP_Read

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.S2D (incB dig bits_succ)
open RadiusClustering.Clust

theorem encNat_eq_vcode (a : ℕ) : encNat a = vcode a := rfl

theorem encNat_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    encNat (Nat.bit b n) = true :: b :: encNat n := vcode_bit b n h

theorem encNat_zero : encNat 0 = [false, true] := rfl

theorem headI_encNat (a : ℕ) (r : List Bool) : headI (encNat a ++ r) = encNat a :=
  headI_vcode a r

theorem dropI_encNat (a : ℕ) (r : List Bool) : dropI (encNat a ++ r) = r := dropI_vcode a r

private theorem bit_val' (b : Bool) (n : ℕ) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit_val]

private theorem bit_decomp (a : ℕ) (ha : a ≠ 0) :
    ∃ x a', (a' = 0 → x = true) ∧ a = Nat.bit x a' ∧ a' < a := by
  refine ⟨decide (a % 2 = 1), a / 2, fun h => by simp; omega, ?_, by omega⟩
  rw [bit_val']
  by_cases h : a % 2 = 1 <;> simp [h] <;> omega

theorem leP_encNat : ∀ (a b : ℕ) (acc : Bool),
    leP (encNat a) (encNat b) acc = (decide (a < b) || (decide (a = b) && acc)) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b acc
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [encNat_zero, leP]
    · obtain ⟨y, b', hb', rfl, -⟩ := bit_decomp b (by omega)
      rw [encNat_zero, encNat_bit y b' hb']
      simp [leP, hb]
  · obtain ⟨x, a', hx, rfl, ha'⟩ := bit_decomp a (by omega)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [encNat_bit x a' hx, encNat_zero]
      have h0 : Nat.bit x a' ≠ 0 := by omega
      simp [leP, h0]
    · obtain ⟨y, b', hb', rfl, -⟩ := bit_decomp b (by omega)
      rw [encNat_bit x a' hx, encNat_bit y b' hb', leP, ih a' ha']
      rw [bit_val' x a', bit_val' y b']
      rw [Bool.eq_iff_iff]
      cases x <;> cases y <;> cases acc <;>
        simp only [Bool.toNat_false, Bool.toNat_true, beq_self_eq_true, ↓reduceIte,
          Bool.false_eq_true, Bool.true_eq_false, beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, and_true, and_false, or_false] <;> omega

private theorem leStep_digits (x y : Bool) (A B F : List Bool) :
    leStep (pairB (true :: x :: A) (pairB (true :: y :: B) F)) =
      pairB A (pairB B (if x = y then F else bflag y)) := by
  simp only [leStep, unpairB_pairB, hd, List.takeWhile_cons, id, ↓reduceIte, sel,
    List.tail_cons, f1, List.head?_cons]
  cases x <;> cases y <;> simp [bflag]

private theorem leStep_fix (F : List Bool) : leStep (pairB [] (pairB [] F)) = pairB [] (pairB [] F) := by
  simp [leStep, unpairB_pairB, hd, sel]

private theorem leStep_fix_iter (F : List Bool) (n : ℕ) :
    leStep^[n] (pairB [] (pairB [] F)) = pairB [] (pairB [] F) :=
  Function.iterate_fixed (leStep_fix F) n

theorem leStep_iter : ∀ (a b : ℕ) (c : Bool) (n : ℕ), (encNat a).length ≤ n →
    leStep^[n] (pairB (encNat a) (pairB (encNat b) (bflag c))) =
      pairB [] (pairB [] (bflag (leP (encNat a) (encNat b) c))) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b c n hn
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [encNat_zero] at hn; omega⟩
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have : leStep (pairB (encNat 0) (pairB (encNat 0) (bflag c))) =
          pairB [] (pairB [] (bflag c)) := by
        simp [leStep, encNat_zero, unpairB_pairB, hd, sel]
      rw [this, leStep_fix_iter]
      simp [encNat_zero, leP]
    · obtain ⟨y, b', hb', rfl, -⟩ := bit_decomp b (by omega)
      have : leStep (pairB (encNat 0) (pairB (encNat (Nat.bit y b')) (bflag c))) =
          pairB [] (pairB [] [true]) := by
        rw [encNat_bit y b' hb']
        simp [leStep, encNat_zero, unpairB_pairB, hd, sel]
      rw [this, leStep_fix_iter, encNat_bit y b' hb']
      simp [encNat_zero, leP, bflag]
  · obtain ⟨x, a', hx, rfl, ha'⟩ := bit_decomp a (by omega)
    rw [encNat_bit x a' hx] at hn ⊢
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have : leStep (pairB (true :: x :: encNat a') (pairB (encNat 0) (bflag c))) =
          pairB [] (pairB [] []) := by
        simp [leStep, encNat_zero, unpairB_pairB, hd, sel]
      rw [this, leStep_fix_iter]
      simp [encNat_zero, leP, bflag]
    · obtain ⟨y, b', hb', rfl, -⟩ := bit_decomp b (by omega)
      rw [encNat_bit y b' hb', leStep_digits]
      have hc : (if x = y then bflag c else bflag y) = bflag (if x == y then c else y) := by
        cases x <;> cases y <;> simp
      rw [hc, ih a' ha' b' _ n (by simp at hn; omega)]
      simp [leP]

theorem leF_encNat (a b : ℕ) : leF (encNat a) (encNat b) = bflag (decide (a ≤ b)) := by
  rw [leF, show [true] = bflag true from rfl, leStep_iter a b true _ (by simp),
    unpairB_pairB, unpairB_pairB, leP_encNat]
  by_cases h : a ≤ b
  · rcases Nat.lt_or_eq_of_le h with h' | h' <;> simp [h, h']
  · simp [h, show ¬ a < b by omega, show a ≠ b by omega]

private theorem digits_cons (ds : List Bool) (r : List Bool) :
    (ds.flatMap fun d => [true, d]) ++ r = ds.foldr (fun d acc => true :: d :: acc) r := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih]

theorem endsU_encNat (a : ℕ) (r : List Bool) : endsU (encNat a ++ r) = endsU r := by
  have : ∀ ds : List Bool, endsU ((ds.flatMap fun d => [true, d]) ++ false :: true :: r) =
      endsU r := by
    intro ds
    induction ds with
    | nil => simp [endsU]
    | cons d ds ih => simpa [endsU] using ih
  simpa [encNat] using this a.bits

theorem endsU_encRow (row : List ℕ) (r : List Bool) :
    endsU (encRow row ++ r) = true :: endsU r := by
  induction row with
  | nil => simp [encRow, endsU]
  | cons a row ih =>
    simp only [encRow, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [endsU_encNat, ih]

theorem endsU_rows (M : List (List ℕ)) : endsU (M.flatMap encRow) = un M.length := by
  induction M with
  | nil => simp [endsU]
  | cons row M ih => rw [List.flatMap_cons, endsU_encRow, ih, List.length_cons, un_succ]

theorem encInst_eq (k τ : ℕ) (M : List (List ℕ)) :
    encInst k τ M = encNat k ++ (encNat τ ++ M.flatMap encRow) := by
  simp [encInst]

theorem endsU_encInst (k τ : ℕ) (M : List (List ℕ)) :
    endsU (encInst k τ M) = un M.length := by
  rw [encInst_eq, endsU_encNat, endsU_encNat, endsU_rows]

theorem rowsS_encInst (k τ : ℕ) (M : List (List ℕ)) :
    rowsS (encInst k τ M) = M.flatMap encRow := by
  rw [rowsS, encInst_eq, dropI_encNat, dropI_encNat]

theorem headI_encInst (k τ : ℕ) (M : List (List ℕ)) : headI (encInst k τ M) = encNat k := by
  rw [encInst_eq, headI_encNat]

theorem headI_dropI_encInst (k τ : ℕ) (M : List (List ℕ)) :
    headI (dropI (encInst k τ M)) = encNat τ := by
  rw [encInst_eq, dropI_encNat, headI_encNat]

theorem dropRow_encNat (a : ℕ) (r : List Bool) : dropRow (encNat a ++ r) = dropRow r := by
  have : ∀ ds : List Bool, dropRow ((ds.flatMap fun d => [true, d]) ++ false :: true :: r) =
      dropRow r := by
    intro ds
    induction ds with
    | nil => simp [dropRow]
    | cons d ds ih => simpa [dropRow] using ih
  simpa [encNat] using this a.bits

theorem dropRow_encRow (row : List ℕ) (r : List Bool) : dropRow (encRow row ++ r) = r := by
  induction row with
  | nil => simp [encRow, dropRow]
  | cons a row ih =>
    simp only [encRow, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [dropRow_encNat, ih]

theorem dropRow_iter (M : List (List ℕ)) (i : ℕ) :
    dropRow^[i] (M.flatMap encRow) = (M.drop i).flatMap encRow := by
  induction i generalizing M with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    rcases M with _ | ⟨row, M⟩
    · simp only [List.flatMap_nil, List.drop_nil]
      exact Function.iterate_fixed (f := dropRow) rfl _
    · rw [List.flatMap_cons, dropRow_encRow, ih]
      simp

theorem rowLenU_encNat (a : ℕ) (r : List Bool) :
    rowLenU (encNat a ++ r) = true :: rowLenU r := by
  have : ∀ ds : List Bool, rowLenU ((ds.flatMap fun d => [true, d]) ++ false :: true :: r) =
      true :: rowLenU r := by
    intro ds
    induction ds with
    | nil => simp [rowLenU]
    | cons d ds ih => simpa [rowLenU] using ih
  simpa [encNat] using this a.bits

theorem rowLenU_encRow (row : List ℕ) (r : List Bool) :
    rowLenU (encRow row ++ r) = un row.length := by
  induction row with
  | nil => simp [encRow, rowLenU]
  | cons a row ih =>
    simp only [encRow, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [rowLenU_encNat, ih, List.length_cons, un_succ]

theorem dropI_iter (row : List ℕ) (r : List Bool) (j : ℕ) (hj : j ≤ row.length) :
    dropI^[j] (row.flatMap encNat ++ r) = (row.drop j).flatMap encNat ++ r := by
  induction j generalizing row with
  | zero => simp
  | succ j ih =>
    rcases row with _ | ⟨a, row⟩
    · simp at hj
    · rw [Function.iterate_succ_apply, List.flatMap_cons, List.append_assoc, dropI_encNat,
        ih row (by simp at hj; omega)]
      simp

theorem tail_iter_un (m n : ℕ) : List.tail^[m] (un n) = un (n - m) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have : (un n).tail = un (n - 1) := by
      rcases n with _ | n
      · rfl
      · rfl
    rw [this, ih]
    congr 1
    omega

theorem entryS_encInst {k τ : ℕ} {M : List (List ℕ)} (hM : IsTriangular M) {s y : ℕ}
    (hsy : s < y) (hy : y < M.length) :
    entryS (un s) (un y) (encInst k τ M) =
      encNat ((M.get ⟨s, by omega⟩).getD (y - s - 1) 0) := by
  have hrow := hM ⟨s, by omega⟩
  have hlen : y - s - 1 < (M.get ⟨s, by omega⟩).length := by rw [hrow]; simp; omega
  rw [entryS, rowsS_encInst, dropRow_iter, un_length]
  have hcons : (true :: un s) = un (s + 1) := rfl
  rw [hcons, un_length, tail_iter_un, un_length]
  have hdrop : M.drop s = M.get ⟨s, by omega⟩ :: M.drop (s + 1) := by
    rw [List.get_eq_getElem]; exact List.drop_eq_getElem_cons _
  rw [hdrop, List.flatMap_cons, encRow, List.append_assoc,
    dropI_iter _ _ _ (show y - (s + 1) ≤ _ by omega)]
  rw [List.drop_eq_getElem_cons (show y - (s + 1) < _ by omega), List.flatMap_cons,
    List.append_assoc, headI_encNat]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  have e : y - (s + 1) = y - s - 1 := by omega
  simp only [e]

theorem incB_iter (c : ℕ) : incB^[c] [] = Nat.bits c := by
  induction c with
  | zero => simp
  | succ c ih => rw [Function.iterate_succ_apply', ih, bits_succ]

theorem cntS_eq (w : List Bool) : cntS w = encNat (w.count true) := by
  rw [cntS, incB_iter, encNat, dig]
  congr 3
  simp [trues, List.count_eq_length_filter]
  rfl

end ClustNP

end M_ClustNP_Read
section M_ClustNP_Wf

namespace ClustNP

open PEqualNP.Library.SearchHelpers.SatV
open RadiusClustering.Clust

def Acc (p : Ph) (s : List Bool) : Prop := s.foldl wfD (p, none) = (Ph.R, none)

theorem foldl_pair (p : Ph) (a b : Bool) (r : List Bool) :
    (a :: b :: r).foldl wfD (p, none) = r.foldl wfD (phD p a b, none) := rfl

theorem foldl_dead (s : List Bool) (o : Option Bool) : (s.foldl wfD (Ph.dead, o)).1 = Ph.dead := by
  induction s generalizing o with
  | nil => rfl
  | cons a s ih =>
    rcases o with _ | b
    · exact ih (some a)
    · simp only [List.foldl_cons, wfD]
      exact ih none

theorem not_acc_dead (s : List Bool) : ¬ Acc Ph.dead s := by
  intro h
  have := foldl_dead s none
  rw [Acc] at h
  rw [h] at this
  exact absurd this (by decide)

theorem acc_nil {p : Ph} (h : Acc p []) : p = Ph.R := by
  simpa [Acc] using h

theorem not_acc_one (p : Ph) (a : Bool) : ¬ Acc p [a] := by
  simp [Acc, wfD]

theorem fold_num (C D nxt : Ph) (hC : ∀ d, phD C true d = if d then C else D)
    (hD : ∀ d, phD D true d = if d then C else D) (hCE : phD C false true = nxt) :
    ∀ (a : ℕ) (p : Ph), (∀ d, phD p true d = if d then C else D) →
      (a = 0 → phD p false true = nxt) → ∀ r : List Bool,
      (encNat a ++ r).foldl wfD (p, none) = r.foldl wfD (nxt, none) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro p hp hpE r
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [encNat_zero, List.cons_append, List.cons_append, List.nil_append, foldl_pair,
      hpE rfl]
  · obtain ⟨x, a', hx, rfl, ha'⟩ : ∃ x a', (a' = 0 → x = true) ∧ a = Nat.bit x a' ∧ a' < a := by
      refine ⟨decide (a % 2 = 1), a / 2, fun h => by simp; omega, ?_, by omega⟩
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h, Nat.bit_val] <;> omega
    rw [encNat_bit x a' hx, List.cons_append, List.cons_append, foldl_pair, hp]
    refine ih a' ha' _ (fun d => ?_) (fun h0 => ?_) r
    · cases x <;> simp [hC, hD]
    · rw [hx h0]; simpa using hCE

theorem fold_row (r : List Bool) : ∀ (row : List ℕ) (p : Ph), p = Ph.R ∨ p = Ph.O →
    (encRow row ++ r).foldl wfD (p, none) = r.foldl wfD (Ph.R, none) := by
  intro row
  induction row with
  | nil =>
    rintro p (rfl | rfl) <;> rfl
  | cons a row ih =>
    intro p hp
    simp only [encRow, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [fold_num Ph.rC Ph.rD Ph.O (fun d => by cases d <;> rfl) (fun d => by cases d <;> rfl) rfl
      a p (fun d => by rcases hp with rfl | rfl <;> cases d <;> rfl)
      (fun _ => by rcases hp with rfl | rfl <;> rfl)]
    exact ih Ph.O (Or.inr rfl)

theorem fold_rows (M : List (List ℕ)) : (M.flatMap encRow).foldl wfD (Ph.R, none) = (Ph.R, none) := by
  induction M with
  | nil => rfl
  | cons row M ih => rw [List.flatMap_cons, fold_row _ row Ph.R (Or.inl rfl), ih]

theorem wfI_encInst (k τ : ℕ) (M : List (List ℕ)) : wfI (encInst k τ M) = true := by
  rw [wfI, decide_eq_true_eq, encInst_eq,
    fold_num Ph.kC Ph.kD Ph.tC (fun d => by cases d <;> rfl) (fun d => by cases d <;> rfl) rfl
      k Ph.kC (fun d => by cases d <;> rfl) (fun _ => rfl),
    fold_num Ph.tC Ph.tD Ph.R (fun d => by cases d <;> rfl) (fun d => by cases d <;> rfl) rfl
      τ Ph.tC (fun d => by cases d <;> rfl) (fun _ => rfl), fold_rows]

theorem exists_bits (ds : List Bool) (h : ds = [] ∨ ds.getLast? = some true) :
    ∃ a : ℕ, a.bits = ds := by
  induction ds with
  | nil => exact ⟨0, Nat.zero_bits⟩
  | cons d ds ih =>
    rcases ds with _ | ⟨e, ds⟩
    · have hd : d = true := by simpa using h
      exact ⟨1, by rw [hd]; rfl⟩
    · obtain ⟨a', ha'⟩ := ih (Or.inr (by
        rcases h with h | h
        · simp at h
        · simpa [List.getLast?_cons] using h))
      have hne : a' ≠ 0 := by rintro rfl; simp at ha'
      exact ⟨Nat.bit d a', by rw [Nat.bits_append_bit a' d (fun h => absurd h hne), ha']⟩

theorem encNat_of_bits {a : ℕ} {ds : List Bool} (h : a.bits = ds) :
    encNat a = (List.flatMap (fun d => [true, d]) ds) ++ [false, true] := by
  rw [encNat, h]

theorem num_parse (C D nxt : Ph) (hC : ∀ d, phD C true d = if d then C else D)
    (hD : ∀ d, phD D true d = if d then C else D) (hCE : phD C false true = nxt)
    (hCF : phD C false false = Ph.dead) (hDF : ∀ b, phD D false b = Ph.dead)
    (hCR : C ≠ Ph.R) (hDR : D ≠ Ph.R) :
    ∀ (n : ℕ) (s : List Bool), s.length ≤ n →
      (Acc C s → ∃ ds r, s = (List.flatMap (fun d => [true, d]) ds) ++ false :: true :: r ∧
        (ds = [] ∨ ds.getLast? = some true) ∧ Acc nxt r) ∧
      (Acc D s → ∃ ds r, s = (List.flatMap (fun d => [true, d]) ds) ++ false :: true :: r ∧ ds.getLast? = some true ∧
        Acc nxt r) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨fun h => absurd (acc_nil h) hCR, fun h => absurd (acc_nil h) hDR⟩
  | succ n ih =>
    intro s hs
    rcases s with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact ⟨fun h => absurd (acc_nil h) hCR, fun h => absurd (acc_nil h) hDR⟩
    · exact ⟨fun h => absurd h (not_acc_one _ _), fun h => absurd h (not_acc_one _ _)⟩
    · have hr : r.length ≤ n := by simp at hs; omega
      have step : ∀ q, (∀ d, phD q true d = if d then C else D) → a = true →
          Acc q (a :: b :: r) → ∃ ds r', a :: b :: r = (List.flatMap (fun d => [true, d]) ds) ++ false :: true :: r' ∧
            ds.getLast? = some true ∧ Acc nxt r' := by
        rintro q hq rfl h
        rw [Acc, foldl_pair, hq] at h
        cases b
        · obtain ⟨ds, r', rfl, hl, hacc⟩ := (ih r hr).2 h
          refine ⟨false :: ds, r', by simp, ?_, hacc⟩
          rw [List.getLast?_cons, hl]; rfl
        · obtain ⟨ds, r', rfl, hl, hacc⟩ := (ih r hr).1 h
          refine ⟨true :: ds, r', by simp, ?_, hacc⟩
          rcases hl with rfl | hl
          · rfl
          · rw [List.getLast?_cons, hl]; rfl
      constructor
      · intro h
        cases a
        · cases b
          · rw [Acc, foldl_pair, hCF] at h; exact absurd h (not_acc_dead r)
          · rw [Acc, foldl_pair, hCE] at h
            exact ⟨[], r, rfl, Or.inl rfl, h⟩
        · obtain ⟨ds, r', e, hl, hacc⟩ := step C hC rfl h
          exact ⟨ds, r', e, Or.inr hl, hacc⟩
      · intro h
        cases a
        · rw [Acc, foldl_pair, hDF] at h; exact absurd h (not_acc_dead r)
        · exact step D hD rfl h

theorem rows_parse : ∀ (n : ℕ) (s : List Bool), s.length ≤ n →
    (Acc Ph.R s → ∃ M : List (List ℕ), s = M.flatMap encRow) ∧
    (Acc Ph.O s → ∃ (row : List ℕ) (M : List (List ℕ)),
      s = row.flatMap encNat ++ [false, false] ++ M.flatMap encRow) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs
  rcases s with _ | ⟨a, _ | ⟨b, r⟩⟩
  · exact ⟨fun _ => ⟨[], rfl⟩, fun h => absurd (acc_nil h) (by decide)⟩
  · exact ⟨fun h => absurd h (not_acc_one _ _), fun h => absurd h (not_acc_one _ _)⟩
  · have hlen : r.length < n := by simp at hs; omega

    have num : ∀ q, (q = Ph.R ∨ q = Ph.O) → Acc q (a :: b :: r) → phD q a b ≠ Ph.R →
        ∃ x r', a :: b :: r = encNat x ++ r' ∧ r'.length < n ∧ Acc Ph.O r' := by
      intro q hq h hR
      rw [Acc, foldl_pair] at h
      cases a
      · cases b
        · rcases hq with rfl | rfl <;> exact absurd rfl hR
        · refine ⟨0, r, rfl, hlen, ?_⟩
          rcases hq with rfl | rfl <;> exact h
      · have hp := num_parse Ph.rC Ph.rD Ph.O (fun d => by cases d <;> rfl)
          (fun d => by cases d <;> rfl) rfl rfl (fun b => by cases b <;> rfl) (by decide)
          (by decide) r.length r le_rfl
        have hq' : phD q true b = if b then Ph.rC else Ph.rD := by
          rcases hq with rfl | rfl <;> cases b <;> rfl
        rw [hq'] at h
        obtain ⟨ds, r', rfl, hl, hacc⟩ : ∃ ds r', r = (List.flatMap (fun d => [true, d]) ds) ++ false :: true :: r' ∧
            (b :: ds).getLast? = some true ∧ Acc Ph.O r' := by
          cases b
          · obtain ⟨ds, r', e, hl, hacc⟩ := hp.2 h
            exact ⟨ds, r', e, by rw [List.getLast?_cons, hl]; rfl, hacc⟩
          · obtain ⟨ds, r', e, hl, hacc⟩ := hp.1 h
            refine ⟨ds, r', e, ?_, hacc⟩
            rcases hl with rfl | hl
            · rfl
            · rw [List.getLast?_cons, hl]; rfl
        obtain ⟨x, hx⟩ := exists_bits (b :: ds) (Or.inr hl)
        refine ⟨x, r', ?_, by simp at hlen ⊢; omega, hacc⟩
        rw [encNat_of_bits hx]
        simp
    constructor
    · intro h
      by_cases hend : a = false ∧ b = false
      · obtain ⟨rfl, rfl⟩ := hend
        rw [Acc, foldl_pair] at h
        obtain ⟨M, rfl⟩ := (ih r.length hlen r le_rfl).1 h
        exact ⟨[] :: M, by simp [encRow]⟩
      · obtain ⟨x, r', e, hr', hacc⟩ := num Ph.R (Or.inl rfl) h (by
          cases a <;> cases b <;> simp_all <;> decide)
        obtain ⟨row, M, rfl⟩ := (ih r'.length hr' r' le_rfl).2 hacc
        exact ⟨(x :: row) :: M, by rw [e]; simp [encRow]⟩
    · intro h
      by_cases hend : a = false ∧ b = false
      · obtain ⟨rfl, rfl⟩ := hend
        rw [Acc, foldl_pair] at h
        obtain ⟨M, rfl⟩ := (ih r.length hlen r le_rfl).1 h
        exact ⟨[], M, by simp⟩
      · obtain ⟨x, r', e, hr', hacc⟩ := num Ph.O (Or.inr rfl) h (by
          cases a <;> cases b <;> simp_all <;> decide)
        obtain ⟨row, M, rfl⟩ := (ih r'.length hr' r' le_rfl).2 hacc
        exact ⟨x :: row, M, by rw [e]; simp⟩

theorem wfI_iff (x : List Bool) : wfI x = true ↔ ∃ k τ M, x = encInst k τ M := by
  constructor
  · intro h
    have h : Acc Ph.kC x := by simpa [wfI, Acc] using h
    obtain ⟨ds, r, rfl, hl, hr⟩ := (num_parse Ph.kC Ph.kD Ph.tC (fun d => by cases d <;> rfl)
      (fun d => by cases d <;> rfl) rfl rfl (fun b => by cases b <;> rfl) (by decide) (by decide)
      _ x le_rfl).1 h
    obtain ⟨ds', r', rfl, hl', hr'⟩ := (num_parse Ph.tC Ph.tD Ph.R (fun d => by cases d <;> rfl)
      (fun d => by cases d <;> rfl) rfl rfl (fun b => by cases b <;> rfl) (by decide) (by decide)
      _ r le_rfl).1 hr
    obtain ⟨M, rfl⟩ := (rows_parse _ r' le_rfl).1 hr'
    obtain ⟨k, hk⟩ := exists_bits ds hl
    obtain ⟨τ, hτ⟩ := exists_bits ds' hl'
    refine ⟨k, τ, M, ?_⟩
    rw [encInst_eq, encNat_of_bits hk, encNat_of_bits hτ]
    simp
  · rintro ⟨k, τ, M, rfl⟩
    exact wfI_encInst k τ M

end ClustNP

end M_ClustNP_Wf
section M_ClustNP_CPT

namespace ClustNP

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
  PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Library.SearchHelpers.S2D
  PEqualNP.Library.SearchHelpers.KSat.Hard

inductive PS : Type
  | b | h (a : Bool) | c
  deriving DecidableEq, Fintype

def f1D : PS → Bool → PS × Option Bool
  | .b, a => (.c, if a then some true else none)
  | q, _ => (q, none)

theorem f1D_c (l : List Bool) : fstRun f1D (fun _ => none) PS.c l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, f1D, ih]

theorem f1D_run (s : List Bool) : fstRun f1D (fun _ => none) PS.b s = f1 s := by
  cases s with
  | nil => rfl
  | cons a l => cases a <;> simp [f1, fstRun, f1D, f1D_c]

theorem cpt_f1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) f1 :=
  fst_polyTime _ _ _ f1D (fun _ => none) PS.b (fun s => (f1D_run s).symm)

def trD : Unit → Bool → Unit × Option Bool
  | _, a => ((), if a then some true else none)

theorem trD_run (w : List Bool) : fstRun trD (fun _ => none) () w = trues w := by
  induction w with
  | nil => rfl
  | cons a l ih => cases a <;> simp [fstRun, trD, trues] at ih ⊢ <;> exact ih

theorem cpt_trues : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) trues :=
  fst_polyTime _ _ _ trD (fun _ => none) () (fun s => (trD_run s).symm)

def euD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, false => (.b, some true)
  | _, _ => (.b, none)

theorem euD_run : ∀ s : List Bool, fstRun euD (fun _ => none) PS.b s = endsU s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: false :: r => by simp [fstRun, euD, endsU, euD_run r]
  | false :: true :: r => by simp [fstRun, euD, endsU, euD_run r]
  | true :: b :: r => by cases b <;> simp [fstRun, euD, endsU, euD_run r]

theorem cpt_endsU : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) endsU :=
  fst_polyTime _ _ _ euD (fun _ => none) PS.b (fun s => (euD_run s).symm)

def drD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, false => (.c, none)
  | .h _, _ => (.b, none)
  | .c, a => (.c, some a)

theorem drD_c (l : List Bool) : fstRun drD (fun _ => none) PS.c l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, drD, ih]

theorem drD_run : ∀ s : List Bool, fstRun drD (fun _ => none) PS.b s = dropRow s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: false :: r => by simp [fstRun, drD, dropRow, drD_c]
  | false :: true :: r => by simp [fstRun, drD, dropRow, drD_run r]
  | true :: b :: r => by cases b <;> simp [fstRun, drD, dropRow, drD_run r]

theorem cpt_dropRow : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) dropRow :=
  fst_polyTime _ _ _ drD (fun _ => none) PS.b (fun s => (drD_run s).symm)

def rlD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, false => (.c, none)
  | .h false, true => (.b, some true)
  | .h true, _ => (.b, none)
  | .c, _ => (.c, none)

theorem rlD_c (l : List Bool) : fstRun rlD (fun _ => none) PS.c l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, rlD, ih]

theorem rlD_run : ∀ s : List Bool, fstRun rlD (fun _ => none) PS.b s = rowLenU s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: false :: r => by simp [fstRun, rlD, rowLenU, rlD_c]
  | false :: true :: r => by simp [fstRun, rlD, rowLenU, rlD_run r]
  | true :: b :: r => by cases b <;> simp [fstRun, rlD, rowLenU, rlD_run r]

theorem cpt_rowLenU : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) rowLenU :=
  fst_polyTime _ _ _ rlD (fun _ => none) PS.b (fun s => (rlD_run s).symm)

def wfFin : Ph × Option Bool → Option Bool
  | q => if q = (.R, none) then some true else none

theorem wfI_run (l : List Bool) : ∀ q : Ph × Option Bool,
    fstRun (fun q a => (wfD q a, (none : Option Bool))) wfFin q l =
      bflag (decide (l.foldl wfD q = (.R, none))) := by
  induction l with
  | nil => intro q; by_cases h : q = (.R, none) <;> simp [fstRun, wfFin, bflag, h]
  | cons a l ih => intro q; simp only [fstRun, Option.toList_none, List.nil_append, List.foldl_cons]; exact ih _

theorem cpt_wfI : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun x => bflag (wfI x)) :=
  fst_polyTime _ _ _ (fun q a => (wfD q a, (none : Option Bool))) wfFin (.kC, none)
    (fun s => (wfI_run s _).symm)

theorem cpt_rowsS : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) rowsS := by
  have := cpt_comp cpt_dropI cpt_dropI
  exact this

theorem dropRow_length (s : List Bool) : (dropRow s).length ≤ s.length := by
  induction s using dropRow.induct <;> simp [dropRow] <;> omega

theorem tail_iter (n : ℕ) (l : List Bool) : List.tail^[n] l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, List.drop_tail]

theorem f1_length (s : List Bool) : (f1 s).length ≤ 1 := by
  unfold f1; split_ifs <;> simp

theorem leStep_length (s : List Bool) : (leStep s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := f1_length (unpairB (unpairB s).2).1.tail
  have h4 : (unpairB s).1.tail.tail.length ≤ (unpairB s).1.length := by simp; omega
  have h5 : (unpairB (unpairB s).2).1.tail.tail.length ≤ (unpairB (unpairB s).2).1.length := by
    simp; omega
  unfold leStep
  simp only [sel]
  split_ifs <;> simp only [pairB_length, List.length_nil, List.length_singleton] <;> omega

theorem cpt_leStep : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) leStep := by
  have hA : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1) := cpt_unpairB1
  have hR : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).2) := cpt_unpairB2
  have hB : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hR
  have hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hR
  have hhA := cpt_hd1 hA
  have hhB := cpt_hd1 hB
  have c0 := cpt_const ([] : List Bool)
  have e1 := cpt_pairB2 c0 (cpt_pairB2 c0 hF)
  have e2 := cpt_pairB2 c0 (cpt_pairB2 c0 (cpt_const [true]))
  have e3 := cpt_pairB2 c0 (cpt_pairB2 c0 c0)
  have fA : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => f1 (unpairB s).1.tail) := cpt_comp (cpt_tail1 hA) cpt_f1
  have fB : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => f1 (unpairB (unpairB s).2).1.tail) := cpt_comp (cpt_tail1 hB) cpt_f1
  have q := cpt_sel (cpt_eqF fA fB) fB hF
  have e4 := cpt_pairB2 (cpt_tail1 (cpt_tail1 hA))
    (cpt_pairB2 (cpt_tail1 (cpt_tail1 hB)) q)
  exact cptE (cpt_sel hhA (cpt_sel hhB e1 e2) (cpt_sel hhB e3 e4)) (fun _ => rfl)

theorem cpt_leF {a b : List Bool → List Bool} (ha : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) a) (hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) b) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => leF (a s) (b s)) := by
  have hit := cpt_iterGrow cpt_leStep 3 leStep_length (cpt_app2 ha hb)
    (cpt_pairB2 ha (cpt_pairB2 hb (cpt_const [true])))
  exact cptE (cpt_unpairB2_1 (cpt_unpairB2_1 hit)) (fun _ => rfl)

theorem cpt_entryS {a b x : List Bool → List Bool} (ha : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) a) (hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) b) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => entryS (a s) (b s) (x s)) := by
  have h1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => dropRow^[(a s).length] (rowsS (x s))) :=
    cpt_iterLen cpt_dropRow dropRow_length ha (cpt_comp hx cpt_rowsS)
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => List.tail^[(true :: a s).length] (b s)) :=
    cpt_iterLen cpt_tail (fun s => by simp) (cpt_cons1 true ha) hb
  have h3 := cpt_iterLen cpt_dropI dropI_length h2 h1
  exact cptE (cpt_comp h3 cpt_headI) (fun _ => rfl)

theorem flag_em (F : List Bool) : sel F [true] [] = bflag F.isEmpty := by
  cases F <;> simp [sel, bflag]

theorem sel_ent (us uy e1 e2 : List Bool) :
    sel (List.tail^[us.length] uy) e1 e2 = if us.length < uy.length then e2 else e1 := by
  rw [tail_iter]
  unfold sel
  by_cases h : us.length < uy.length
  · have : uy.drop us.length ≠ [] := by simpa [List.drop_eq_nil_iff] using h
    simp [this, h]
  · have : uy.drop us.length = [] := by simpa [List.drop_eq_nil_iff] using h
    simp [this, h]

theorem covers_flag (us uy x w : List Bool) :
    bflag (covers us uy x w) =
      sel (f1 (List.tail^[us.length] w)) []
        (sel (bflag (decide (us = uy)))
          (sel (leF (sel (List.tail^[us.length] uy) (entryS uy us x) (entryS us uy x))
            (headI (dropI x))) [] [true]) [true]) := by
  rw [sel_ent]
  unfold covers
  generalize (if us.length < uy.length then entryS us uy x else entryS uy us x) = E
  generalize f1 (List.tail^[us.length] w) = P
  generalize leF E (headI (dropI x)) = L
  cases P <;> cases L <;> by_cases h : us = uy <;> simp [sel, bflag, h]

theorem cpt_covers {us uy x w : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) us) (hy : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) uy)
    (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) (hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) w) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (covers (us s) (uy s) (x s) (w s))) := by
  have P : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => f1 (List.tail^[(us s).length] (w s))) :=
    cpt_comp (cpt_iterLen cpt_tail (fun s => by simp) hu hw) cpt_f1
  have lt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => List.tail^[(us s).length] (uy s)) :=
    cpt_iterLen cpt_tail (fun s => by simp) hu hy
  have ent := cpt_sel lt (cpt_entryS hy hu hx) (cpt_entryS hu hy hx)
  have lim : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => headI (dropI (x s))) := cpt_comp (cpt_comp hx cpt_dropI) cpt_headI
  have L := cpt_leF ent lim
  exact cptE (cpt_sel P (cpt_const []) (cpt_sel (cpt_eqF hu hy)
    (cpt_sel L (cpt_const []) (cpt_const [true])) (cpt_const [true])))
    (fun s => (covers_flag _ _ _ _).symm)

theorem cpt_covRow : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) covRow := by
  have h2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun z => (unpairB z).2) := cpt_unpairB2
  have h3 := cpt_unpairB2_1 h2
  exact cpt_covers cpt_unpairB1 (cpt_unpairB1_1 h2) (cpt_unpairB1_1 h3) (cpt_unpairB2_1 h3)

theorem cpt_uncov : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) uncov := by
  have hc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun z => endsU (unpairB (unpairB z).2).1) :=
    cpt_comp (cpt_unpairB1_1 cpt_unpairB2) cpt_endsU
  have hl := cpt_flatMapRange cpt_covRow hc cpt_id
  exact cptE (cpt_sel hl (cpt_const [true]) (cpt_const [])) (fun z => flag_em _)

theorem cpt_uncovS : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (List.range (endsU (unpairB s).1).length).flatMap
    fun y => uncov (pairB (un y) s)) :=
  cpt_flatMapRange cpt_uncov (cpt_comp cpt_unpairB1 cpt_endsU) cpt_id

theorem cpt_triRow : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) triRow := by
  have hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun z => (unpairB z).1) := cpt_unpairB1
  have hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun z => (unpairB z).2) := cpt_unpairB2
  have hd : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun z => dropRow^[(unpairB z).1.length] (rowsS (unpairB z).2)) :=
    cpt_iterLen cpt_dropRow dropRow_length hu (cpt_comp hx cpt_rowsS)
  have hl := cpt_app2 (cpt_comp hd cpt_rowLenU) (cpt_cons1 true hu)
  have he := cpt_comp hx cpt_endsU
  exact cptE (cpt_sel (cpt_eqF hl he) (cpt_const [true]) (cpt_const [])) (fun z => by
    unfold triRow; cases decide (rowLenU (dropRow^[(unpairB z).1.length] (rowsS (unpairB z).2)) ++
      true :: (unpairB z).1 = endsU (unpairB z).2) <;> simp [sel, bflag])

theorem cpt_triBad : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) triBad :=
  cpt_flatMapRange cpt_triRow cpt_endsU cpt_id

theorem cpt_cntS {w : List Bool → List Bool} (hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) w) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => cntS (w s)) := by
  have hi := cpt_iterGrow cpt_incB 1 incB_length (cpt_comp hw cpt_trues) (cpt_const [])
  exact cptE (cpt_app2 (cpt_comp hi cpt_dig) (cpt_const [false, true])) (fun _ => rfl)

theorem flag_CV (a : Bool) (T L U : List Bool) :
    (!(sel (bflag a) [] (sel T (sel L [] (sel U [true] [])) [])).isEmpty) =
      (a && T.isEmpty && !L.isEmpty && U.isEmpty) := by
  cases a <;> cases T <;> cases L <;> cases U <;> simp [sel, bflag]

theorem cpt_CVS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
    (fun s : List Bool => !(sel (bflag (wfI (unpairB s).1)) []
      (sel (triBad (unpairB s).1) (sel (leF (cntS (unpairB s).2) (headI (unpairB s).1)) []
        (sel ((List.range (endsU (unpairB s).1).length).flatMap
          fun y => uncov (pairB (un y) s)) [true] [])) [])).isEmpty) := by
  have hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => (unpairB s).2) := cpt_unpairB2
  have F1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => bflag (wfI (unpairB s).1)) := cpt_comp (g := fun x => bflag (wfI x)) hx cpt_wfI
  have T : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => triBad (unpairB s).1) := cpt_comp hx cpt_triBad
  have hh : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun s => headI (unpairB s).1) := cpt_comp hx cpt_headI
  have L := cpt_leF (cpt_cntS hw) hh
  have G := cpt_sel F1 (cpt_const [])
    (cpt_sel T (cpt_sel L (cpt_const []) (cpt_sel cpt_uncovS (cpt_const [true]) (cpt_const [])))
      (cpt_const []))
  exact cpt_comp (g := fun l : List Bool => !l.isEmpty) G cpt_neS

theorem cpt_CV : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool CV :=
  cptG (cpt_comp cpt_pairB cpt_CVS) (fun p => by
    obtain ⟨x, w⟩ := p
    simp only [unpairB_pairB]
    rw [flag_CV]
    rfl)

end ClustNP

end M_ClustNP_CPT
section M_ClustNP_InNP

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open RadiusClustering RadiusClustering.Clust

theorem bflag_eq_nil (b : Bool) : bflag b = [] ↔ b = false := by
  cases b <;> simp [bflag]

theorem isEmpty_flatMap_bflag (l : List ℕ) (f : ℕ → Bool) :
    (l.flatMap fun i => bflag (f i)).isEmpty = true ↔ ∀ i ∈ l, f i = false := by
  rw [List.isEmpty_iff, List.flatMap_eq_nil_iff]
  simp only [bflag_eq_nil]

theorem un_append_cons (a i : ℕ) : un a ++ true :: un i = un (a + 1 + i) := by
  simp only [un, List.replicate_add]
  simp [List.replicate_succ]

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

theorem clustLang_mem_NP : clustLang ∈ PEqualNP.Library.NP := by
  refine ⟨{p | CV p = true}, Polynomial.X, ⟨CV, fun _ => Iff.rfl, cpt_CV⟩, fun x => ?_⟩
  exact (CV_spec x).trans (by simp)

end ClustNP

end M_ClustNP_InNP
section M_ClustNP_RedItems

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open RadiusClustering RadiusClustering.Clust

def encItem : Option (ℕ × Bool) → List Bool
  | some l => encodeLiteral l
  | none => [false, false]

theorem encodeCNF_eq_items (φ : CNF) : encodeCNF φ = (items φ).flatMap encItem := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [encodeCNF, items, List.flatMap_cons, List.flatMap_append, List.flatMap_map] at ih ⊢
    rw [ih]
    simp [encodeClause, encItem]

theorem headI_encItem (o : Option (ℕ × Bool)) (r : List Bool) :
    headI (encItem o ++ r) = encItem o := by
  cases o with
  | none => simp [encItem, headI]
  | some l => exact headI_lit l r

theorem dropI_encItem (o : Option (ℕ × Bool)) (r : List Bool) : dropI (encItem o ++ r) = r := by
  cases o with
  | none => simp [encItem, dropI]
  | some l => exact dropI_lit l r

theorem isEnd_encItem (o : Option (ℕ × Bool)) (r : List Bool) :
    isEnd (encItem o ++ r) = decide (o = none) := by
  cases o with
  | none => simp [encItem, isEnd]
  | some l => simp [encItem, isEnd_lit]

private theorem digits_skip (f : List Bool → List Bool)
    (hf : ∀ d r, f (true :: d :: r) = f r) (ds r : List Bool) :
    f ((ds.flatMap fun d => [true, d]) ++ r) = f r := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [hf, ih]

theorem itemsU_true (d : Bool) (r : List Bool) : itemsU (true :: d :: r) = itemsU r := rfl

theorem endsU_true (d : Bool) (r : List Bool) : endsU (true :: d :: r) = endsU r := rfl

theorem itemsU_encItem (o : Option (ℕ × Bool)) (r : List Bool) :
    itemsU (encItem o ++ r) = true :: itemsU r := by
  cases o with
  | none => rfl
  | some l =>
    simp only [encItem, encodeLiteral_eq, vcode, List.cons_append, List.append_assoc]
    rw [itemsU_true, digits_skip itemsU itemsU_true]
    rfl

theorem endsU_encItem (o : Option (ℕ × Bool)) (r : List Bool) :
    endsU (encItem o ++ r) = if o = none then true :: endsU r else endsU r := by
  cases o with
  | none => rfl
  | some l =>
    simp only [encItem, encodeLiteral_eq, vcode, List.cons_append, List.append_assoc,
      reduceCtorEq, ↓reduceIte]
    rw [endsU_true, digits_skip endsU endsU_true]
    rfl

theorem itemsU_items (its : List (Option (ℕ × Bool))) :
    itemsU (its.flatMap encItem) = un its.length := by
  induction its with
  | nil => simp [itemsU]
  | cons o its ih => rw [List.flatMap_cons, itemsU_encItem, ih]; rfl

theorem endsU_items (its : List (Option (ℕ × Bool))) :
    endsU (its.flatMap encItem) = un (its.count none) := by
  induction its with
  | nil => simp [endsU]
  | cons o its ih =>
    rw [List.flatMap_cons, endsU_encItem, ih]
    cases o <;> simp [un_succ]

theorem restAt_items (its : List (Option (ℕ × Bool))) (p : ℕ) :
    restAt (un p) (its.flatMap encItem) = (its.drop p).flatMap encItem := by
  rw [restAt, un_length]
  induction p generalizing its with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply]
    rcases its with _ | ⟨o, its⟩
    · simp only [List.flatMap_nil, List.drop_nil]
      exact Function.iterate_fixed (f := dropI) rfl _
    · rw [List.flatMap_cons, dropI_encItem, ih]
      simp

variable (its : List (Option (ℕ × Bool)))

theorem headI_restAt {p : ℕ} (hp : p < its.length) :
    headI (restAt (un p) (its.flatMap encItem)) = encItem its[p] := by
  rw [restAt_items, List.drop_eq_getElem_cons hp, List.flatMap_cons, headI_encItem]

theorem endAt_items {p : ℕ} (hp : p < its.length) :
    endAt (un p) (its.flatMap encItem) = decide (its[p] = none) := by
  rw [endAt, restAt_items, List.drop_eq_getElem_cons hp, List.flatMap_cons, isEnd_encItem]

def varCode : Option (ℕ × Bool) → List Bool
  | some l => vcode l.1
  | none => []

theorem varAt_items {p : ℕ} (hp : p < its.length) :
    varAt (un p) (its.flatMap encItem) = varCode its[p] := by
  rw [varAt, headI_restAt its hp]
  cases its[p] with
  | none => rfl
  | some l => simp [encItem, encodeLiteral_eq, varCode]

theorem varCode_eq_vcode_iff (o : Option (ℕ × Bool)) (l : ℕ × Bool) :
    varCode o = vcode l.1 ↔ ∃ l', o = some l' ∧ l'.1 = l.1 := by
  cases o with
  | none => simp [varCode, (vcode_ne_nil l.1).symm]
  | some l' =>
    simp only [varCode, Option.some.injEq, exists_eq_left']
    exact ⟨fun h => vcode_injective h, fun h => by rw [h]⟩

theorem repAt_iff {p : ℕ} (hp : p < its.length) :
    repAt (un p) (its.flatMap encItem) = true ↔ ∃ l, IsRep its p l := by
  rw [repAt, Bool.and_eq_true, Bool.not_eq_true', endAt_items its hp, decide_eq_false_iff_not]
  have hloop : ((List.range (un p).length).flatMap fun q =>
      sameVar (pairB (un q) (pairB (un p) (its.flatMap encItem)))) =
      (List.range p).flatMap fun q => bflag (decide (varAt (un q) (its.flatMap encItem) =
        varAt (un p) (its.flatMap encItem))) := by
    rw [un_length]
    simp only [sameVar, unpairB_pairB]
  rw [hloop, isEmpty_flatMap_bflag]
  constructor
  · rintro ⟨hlit, hno⟩
    obtain ⟨l, hl⟩ : ∃ l, its[p] = some l := Option.ne_none_iff_exists'.1 hlit
    refine ⟨l, by rw [List.getElem?_eq_getElem hp, hl], fun q hq l' hl' he => ?_⟩
    have hqL : q < its.length := by omega
    have := hno q (List.mem_range.2 hq)
    rw [decide_eq_false_iff_not, varAt_items its hqL, varAt_items its hp, hl] at this
    apply this
    rw [List.getElem?_eq_getElem hqL, Option.some.injEq] at hl'
    rw [hl']
    simp [varCode, he]
  · rintro ⟨l, hl, hno⟩
    rw [List.getElem?_eq_getElem hp, Option.some.injEq] at hl
    refine ⟨by rw [hl]; simp, fun q hq => ?_⟩
    have hq' := List.mem_range.1 hq
    have hqL : q < its.length := by omega
    rw [decide_eq_false_iff_not, varAt_items its hqL, varAt_items its hp, hl]
    intro h
    obtain ⟨l', hl', hv⟩ := (varCode_eq_vcode_iff _ l).1 h
    exact hno q hq' l' (by rw [List.getElem?_eq_getElem hqL, hl']) hv

theorem count_drop_split {r p : ℕ} (hrp : r ≤ p) :
    (its.drop r).count none = ((its.drop r).take (p - r)).count none + (its.drop p).count none := by
  conv_lhs => rw [← List.take_append_drop (p - r) (its.drop r)]
  rw [List.count_append, List.drop_drop]
  congr 3
  omega

theorem inSeg_iff_count {p : ℕ} (l : ℕ × Bool) :
    InSeg its p l ↔ ∃ r < p, its[r]? = some (some l) ∧
      (its.drop r).count none = (its.drop p).count none := by
  constructor
  · rintro ⟨r, hr, hl, hno⟩
    refine ⟨r, hr, hl, ?_⟩
    rw [count_drop_split its hr.le, Nat.add_eq_right, List.count_eq_zero]
    intro hmem
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
    simp only [List.length_take, List.length_drop] at hi
    simp only [List.getElem_take, List.getElem_drop] at he
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : its[r]? = some none := by
        rw [List.getElem?_eq_getElem (by omega)]; simp at he ⊢; exact he
      rw [this] at hl; simp at hl
    · exact hno (r + i) (by omega) (by omega)
        (by rw [List.getElem?_eq_getElem (by omega)]; simp [he])
  · rintro ⟨r, hr, hl, hc⟩
    refine ⟨r, hr, hl, fun r' h1 h2 hnone => ?_⟩
    rw [count_drop_split its hr.le, Nat.add_eq_right, List.count_eq_zero] at hc
    apply hc
    have hr'L : r' < its.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hnone; simp at hnone
    rw [List.getElem?_eq_getElem hr'L, Option.some.injEq] at hnone
    rw [List.mem_iff_getElem]
    refine ⟨r' - r, by simp; omega, ?_⟩
    simp only [List.getElem_take, List.getElem_drop]
    have e : r + (r' - r) = r' := by omega
    simp only [e]
    exact hnone

theorem encItem_eq_encodeLiteral (o : Option (ℕ × Bool)) (l : ℕ × Bool) :
    encItem o = encodeLiteral l ↔ o = some l := by
  cases o with
  | none => simp [encItem, encodeLiteral_eq]
  | some l' =>
    simp only [encItem, Option.some.injEq]
    exact ⟨fun h => PEqualNP.Library.SearchHelpers.TwoSat.encodeLiteral_injective h,
      fun h => by rw [h]⟩

theorem segAt_iff {p : ℕ} (hp : p < its.length) (l : ℕ × Bool) :
    segAt (un p) (encodeLiteral l) (its.flatMap encItem) = true ↔ InSeg its p l := by
  have hloop : ((List.range (un p).length).flatMap fun r =>
      segHit (pairB (un r) (pairB (un p) (pairB (encodeLiteral l) (its.flatMap encItem))))) =
      (List.range p).flatMap fun r =>
        bflag (decide (headI (restAt (un r) (its.flatMap encItem)) = encodeLiteral l) &&
          decide (endsU (restAt (un r) (its.flatMap encItem)) =
            endsU (restAt (un p) (its.flatMap encItem)))) := by
    rw [un_length]
    simp only [segHit, unpairB_pairB]
  rw [segAt, hloop, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, isEmpty_flatMap_bflag,
    inSeg_iff_count]
  simp only [not_forall, exists_prop, Bool.not_eq_false]
  constructor
  · rintro ⟨r, hr, h⟩
    have hr' := List.mem_range.1 hr
    have hrL : r < its.length := by omega
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      headI_restAt its hrL, encItem_eq_encodeLiteral, restAt_items, restAt_items, endsU_items,
      endsU_items] at h
    exact ⟨r, hr', by rw [List.getElem?_eq_getElem hrL, h.1], un_inj h.2⟩
  · rintro ⟨r, hr, hl, hc⟩
    have hrL : r < its.length := by omega
    refine ⟨r, List.mem_range.2 hr, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      headI_restAt its hrL, encItem_eq_encodeLiteral, restAt_items, restAt_items, endsU_items,
      endsU_items, hc]
    rw [List.getElem?_eq_getElem hrL, Option.some.injEq] at hl
    exact ⟨hl, rfl⟩

end ClustNP

end M_ClustNP_RedItems
section M_ClustNP_RedCorrect

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open PEqualNP.Library.SearchHelpers.S2D (incB dig)
open RadiusClustering RadiusClustering.Clust

variable (its : List (Option (ℕ × Bool)))

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

end M_ClustNP_RedCorrect
section M_ClustNP_RedCPT

namespace ClustNP

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
  PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Library.SearchHelpers.S2D
  PEqualNP.Library.SearchHelpers.KSat.Hard

def itD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, _ => (.b, some true)
  | _, _ => (.b, none)

theorem itD_run : ∀ s : List Bool, fstRun itD (fun _ => none) PS.b s = itemsU s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: b :: r => by simp [fstRun, itD, itemsU, itD_run r]
  | true :: b :: r => by simp [fstRun, itD, itemsU, itD_run r]

theorem cpt_itemsU : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) itemsU :=
  fst_polyTime _ _ _ itD (fun _ => none) PS.b (fun s => (itD_run s).symm)

def d3D : Fin 3 → Bool → Fin 3 × Option Bool
  | q, _ => (q + 1, if q = 2 then some true else none)

theorem d3D_run (l : List Bool) : ∀ q : Fin 3,
    fstRun d3D (fun _ => none) q l = un ((q.val + l.length) / 3) := by
  induction l with
  | nil => intro q; fin_cases q <;> simp [fstRun, un]
  | cons a l ih =>
    intro q
    simp only [fstRun, d3D, ih, List.length_cons]
    fin_cases q
    · simp only [Fin.zero_eta, Fin.isValue]
      simp; congr 1; omega
    · simp; congr 1; omega
    · have h2 : (2 + (l.length + 1)) / 3 = (0 + l.length) / 3 + 1 := by omega
      simp [h2, un, List.replicate_succ]

theorem cpt_div3 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) div3 :=
  fst_polyTime _ _ _ d3D (fun _ => none) 0 (fun s => by simp [div3, d3D_run s 0])

def m3D : Fin 3 → Bool → Fin 3 × Option Bool
  | q, _ => (q + 1, none)

theorem m3D_run (k : ℕ) (l : List Bool) : ∀ q : Fin 3,
    fstRun m3D (fun q => if q.val = k then some true else none) q l =
      bflag (decide ((q.val + l.length) % 3 = k)) := by
  induction l with
  | nil =>
    intro q
    have h : q.val % 3 = q.val := Nat.mod_eq_of_lt q.isLt
    by_cases hk : q.val = k
    · subst hk; simp [fstRun, bflag, h]
    · simp [fstRun, bflag, h, hk]
  | cons a l ih =>
    intro q
    have key : ((q + 1 : Fin 3).val + l.length) % 3 = (q.val + (l.length + 1)) % 3 := by
      fin_cases q <;> simp <;> omega
    simp only [fstRun, m3D, ih, List.length_cons, Option.toList_none, List.nil_append, key]

theorem cpt_isR (k : ℕ) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun u => bflag (decide (u.length % 3 = k))) :=
  fst_polyTime _ _ _ m3D (fun q => if q.val = k then some true else none) 0
    (fun s => by simp [m3D_run k s 0])

theorem cpt_isR0 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun u => bflag (isR0 u)) := cpt_isR 0
theorem cpt_isR2 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) (fun u => bflag (isR2 u)) := cpt_isR 2

theorem flag_not (b : Bool) : sel (bflag b) [true] [] = bflag (!b) := by
  cases b <;> simp [sel, bflag]

theorem flag_or (a b : Bool) : sel (bflag a) (bflag b) [true] = bflag (a || b) := by
  cases a <;> cases b <;> simp [sel, bflag]

theorem flag_if (c : Prop) [Decidable c] (A B : Bool) :
    bflag (if c then A else B) = sel (bflag (decide c)) (bflag B) (bflag A) := by
  by_cases h : c <;> simp [sel, bflag, h]

theorem cons_flag (b : Bool) (l : List Bool) :
    b :: l = sel (bflag b) (false :: l) (true :: l) := by
  cases b <;> simp [sel, bflag]

theorem cpt_bAnd {a b : List Bool → Bool} (ha : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (a s))
    (hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (b s)) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (a s && b s) :=
  cptE (cpt_sel ha (cpt_const []) hb) (fun _ => flag_and _ _)

theorem cpt_bOr {a b : List Bool → Bool} (ha : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (a s))
    (hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (b s)) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (a s || b s) :=
  cptE (cpt_sel ha hb (cpt_const [true])) (fun _ => flag_or _ _)

theorem cpt_bNot {a : List Bool → Bool} (ha : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (a s)) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (!a s) :=
  cptE (cpt_sel ha (cpt_const [true]) (cpt_const [])) (fun _ => flag_not _)

theorem cpt_bIf {c : List Bool → Prop} [∀ s, Decidable (c s)] {A B : List Bool → Bool}
    (hc : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (decide (c s))) (hA : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (A s))
    (hB : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (B s)) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (if c s then A s else B s) :=
  cptE (cpt_sel hc hB hA) (fun _ => (flag_if _ _ _).symm)

theorem cpt_bEmpty {F : List Bool → List Bool} (hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) F) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (F s).isEmpty :=
  cptE (cpt_sel hF (cpt_const [true]) (cpt_const [])) (fun _ => flag_em _)

theorem cpt_bNonempty {F : List Bool → List Bool} (hF : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) F) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (!(F s).isEmpty) :=
  cptE (cpt_sel hF (cpt_const []) (cpt_const [true])) (fun _ => flag_ne _)

theorem cpt_consFlag (b : List Bool → Bool) {l : List Bool → List Bool}
    (hb : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (b s)) (hl : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) l) : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => b s :: l s :=
  cptE (cpt_sel hb (cpt_cons1 false hl) (cpt_cons1 true hl)) (fun _ => (cons_flag _ _).symm)

theorem cpt_vertsU : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) vertsU :=
  cptE (cpt_app2 (cpt_app2 cpt_itemsU cpt_itemsU) cpt_itemsU) (fun _ => rfl)

theorem cpt_restAt {u x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => restAt (u s) (x s) :=
  cpt_iterLen cpt_dropI dropI_length hu hx

theorem cpt_endAt {u x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (endAt (u s) (x s)) :=
  cpt_comp (g := fun r => bflag (isEnd r)) (cpt_restAt hu hx) cpt_isEndF

theorem cpt_varAt {u x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => varAt (u s) (x s) :=
  cpt_tail1 (cpt_tail1 (cpt_comp (cpt_restAt hu hx) cpt_headI))

theorem cpt_sameVar : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) sameVar := by
  have hR : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun z => (unpairB z).2 := cpt_unpairB2
  have hx := cpt_unpairB2_1 hR
  exact cpt_eqF (cpt_varAt cpt_unpairB1 hx) (cpt_varAt (cpt_unpairB1_1 hR) hx)

theorem cpt_repAt {u x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (repAt (u s) (x s)) := by
  have hl := cpt_flatMapRange cpt_sameVar hu (cpt_pairB2 hu hx)
  exact cpt_bAnd (cpt_bNot (cpt_endAt hu hx)) (cpt_bEmpty hl)

theorem cpt_segHit : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) segHit := by
  have hr : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun z => (unpairB z).1 := cpt_unpairB1
  have h1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun z => (unpairB z).2 := cpt_unpairB2
  have hu := cpt_unpairB1_1 h1
  have h2 := cpt_unpairB2_1 h1
  have hl := cpt_unpairB1_1 h2
  have hx := cpt_unpairB2_1 h2
  exact cpt_bAnd (cpt_eqF (cpt_comp (cpt_restAt hr hx) cpt_headI) hl)
    (cpt_eqF (cpt_comp (cpt_restAt hr hx) cpt_endsU) (cpt_comp (cpt_restAt hu hx) cpt_endsU))

theorem cpt_segAt {u l x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hl : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) l) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (segAt (u s) (l s) (x s)) :=
  cpt_bNot (cpt_bEmpty (cpt_flatMapRange cpt_segHit hu (cpt_pairB2 hu (cpt_pairB2 hl hx))))

theorem cpt_crossAt {u v x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hv : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) v) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (crossAt (u s) (v s) (x s)) := by
  have du := cpt_comp hu cpt_div3
  have dv := cpt_comp hv cpt_div3
  have lit := cpt_consFlag (fun _ => true) (cpt_const [true])
    (cpt_consFlag _ (cpt_comp (g := fun r => bflag (isR0 r)) hu cpt_isR0) (cpt_varAt du hx))
  exact cpt_bAnd (cpt_bAnd (cpt_bAnd (cpt_bAnd (cpt_bNot (cpt_comp (g := fun r => bflag (isR2 r)) hu cpt_isR2))
    (cpt_comp (g := fun r => bflag (isR2 r)) hv cpt_isR2)) (cpt_endAt dv hx)) (cpt_repAt du hx)) (cpt_segAt dv lit hx)

theorem cpt_adjAt {u v x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hv : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) v) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => bflag (adjAt (u s) (v s) (x s)) := by
  have du := cpt_comp hu cpt_div3
  have dv := cpt_comp hv cpt_div3
  have a := cpt_bOr (cpt_bAnd (cpt_bNot (cpt_comp (g := fun r => bflag (isR2 r)) hu cpt_isR2)) (cpt_bNot (cpt_comp (g := fun r => bflag (isR2 r)) hv cpt_isR2)))
    (cpt_bNot (cpt_endAt du hx))
  have b := cpt_bOr (cpt_crossAt hu hv hx) (cpt_crossAt hv hu hx)
  exact cpt_bIf (cpt_eqF du dv) a b

theorem cpt_entryAt {u v x : List Bool → List Bool} (hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) u) (hv : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) v) (hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) x) :
    (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun s => entryAt (u s) (v s) (x s) :=
  cpt_sel (cpt_adjAt hu hv hx) (cpt_const _) (cpt_const _)

theorem cpt_cell : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) cell := by
  have h1 : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun z => (unpairB z).2 := cpt_unpairB2
  have hi := cpt_unpairB1_1 h1
  have hx := cpt_unpairB2_1 h1
  exact cpt_entryAt hi (cpt_app2 hi (cpt_cons1 true cpt_unpairB1)) hx

theorem cpt_rowAt : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) rowAt := by
  have hu : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun z => (unpairB z).1 := cpt_unpairB1
  have hx : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) fun z => (unpairB z).2 := cpt_unpairB2
  have hc := cpt_iterLen cpt_tail (fun s => by simp) (cpt_cons1 true hu)
    (cpt_comp (g := vertsU) hx cpt_vertsU)
  exact cpt_app2 (cpt_flatMapRange cpt_cell hc cpt_id) (cpt_const _)

theorem cpt_rowsOf : (ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)) rowsOf :=
  cpt_flatMapRange cpt_rowAt cpt_vertsU cpt_id

theorem cpt_red : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) red := by
  have hi := cpt_iterGrow cpt_incB 1 incB_length cpt_itemsU (cpt_const [])
  exact cpt_sel cpt_wfF (cpt_const [])
    (cpt_app2 (cpt_app2 (cpt_app2 (cpt_comp hi cpt_dig) (cpt_const _)) (cpt_const _)) cpt_rowsOf)

end ClustNP

end M_ClustNP_RedCPT
section M_ClustNP_NPC

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open RadiusClustering RadiusClustering.Clust

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

theorem clustLang_npComplete : PEqualNP.Library.NPComplete clustLang :=
  PEqualNP.Library.L020 SAT clustLang PEqualNP.Library.L031 clustLang_mem_NP sat_reduces_clust

theorem clustLang_mem_P_iff : clustLang ∈ PEqualNP.Library.P ↔ PEqualNP.Library.P = PEqualNP.Library.NP :=
  PEqualNP.Library.L018 clustLang clustLang_npComplete

end ClustNP

end M_ClustNP_NPC
end PEqualNP.Outside.L_clust_npc

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
  have h := PEqualNP.Outside.L_clust_npc.ClustNP.clustLang_npComplete
  rwa [PEqualNP.Outside.L_clust_npc.RadiusClustering.Clust.clustLang_eq_inline] at h
