import RadiusClustering.Exact

/-!
# T4: minimum radius for exactly `k` clusters (corrected Th. 3.4, Prop. 3.5)
-/

namespace RadiusClustering

variable {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]

/-- `r` is the minimum radius of a partition into exactly `k` clusters (Def. 3.1): one exists at
radius `r`, none at any radius `τ < r`. -/
def IsMinRadius (d : X → X → α) (k : ℕ) (r : α) : Prop :=
  (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d r f) ∧
    ∀ τ < r, ¬ ∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f

omit [Fintype X] [Zero α] in
/-- Two thresholds with the same comparisons give the same threshold graph. -/
theorem thresholdGraph_congr (d : X → X → α) {τ τ' : α}
    (h : ∀ u v, d u v ≤ τ ↔ d u v ≤ τ') : thresholdGraph d τ = thresholdGraph d τ' := by
  ext u v
  simp only [thresholdGraph, SimpleGraph.fromRel_adj, h]

omit [Fintype X] in
-- `hd`, `ht` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- **T4a.** A set dominating `G_t` still dominates `G_t'` for `t ≤ t'`: `t ↦ γ(G_t)` is
antitone. -/
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

/-- **T4** (corrected Th. 3.4). Let `t` be a value of `d` such that `G_t` is dominated by `k`
vertices and no `G_{t'}` with `t'` a smaller value of `d` is. Then for `k ≤ |X|`, `t` is the
minimum radius of a partition into exactly `k` clusters. -/
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

-- `hmin` kept for fidelity to Th. 3.4 (`docs/cadrage.md` §2).
set_option linter.unusedVariables false in
/-- **T4c** (Th. 3.4, constructive form, as in Curgraph: `k = |S| = γ(G_t)`). Same `t`. The
partition derived from a minimum dominating set `S` of `G_t` has radius `≤ t` and exactly `k`
clusters, and `t` is the minimum radius for `k` clusters. -/
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
-- `hd`, `hτ` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- **Prop. 3.5.** For `X` non-empty, a single cluster of radius `≤ τ` exists iff some point is
at dissimilarity `≤ τ` from every point: `R*_1 = min_y max_x d(y, x)`. -/
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
