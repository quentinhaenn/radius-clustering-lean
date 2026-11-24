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

-- `hd`, `ht` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- **T4a.** A set dominating `G_t` still dominates `G_t'` for `t ≤ t'`: `t ↦ γ(G_t)` is
antitone. -/
theorem IsDominating.thresholdGraph_mono {d : X → X → α} (hd : IsDissimilarity d)
    {t t' : α} (ht : 0 ≤ t) (htt' : t ≤ t')
    {S : Finset X} (hS : IsDominating (thresholdGraph d t) S) :
    IsDominating (thresholdGraph d t') S := by
  sorry

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
  sorry

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
  sorry

-- `hd`, `hτ` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- **Prop. 3.5.** For `X` non-empty, a single cluster of radius `≤ τ` exists iff some point is
at dissimilarity `≤ τ` from every point: `R*_1 = min_y max_x d(y, x)`. -/
theorem exists_validClustering_one_iff [Nonempty X] (d : X → X → α) (hd : IsDissimilarity d)
    (τ : α) (hτ : 0 ≤ τ) :
    (∃ f : X → Fin 1, IsValidClustering d τ f) ↔ ∃ y, ∀ x, d y x ≤ τ := by
  sorry

end RadiusClustering
