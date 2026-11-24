import RadiusClustering.Basic

/-!
# SAT → dominating set (gadget)

CNF formulas as in pequalnp (`PEqualNP/Defs/Search.lean`): a literal `(i, b)` is true under `σ`
when `σ i = b`. Variables `i < N` get a triangle `{(i, true), (i, false), (i, none)}`; clause `j`
gets a vertex adjacent to its literals. `φ` is satisfiable iff the graph has a dominating set
of size `≤ N` (statement not yet reviewed by the author, `docs/pequalnp.md`).
-/

namespace RadiusClustering.PEqualNP

/-- Vertices: `inl (i, some b)` the literal `(i, b)`, `inl (i, none)` the third vertex of
triangle `i`, `inr j` clause `j`. -/
abbrev GadgetV (N m : ℕ) : Type := (Fin N × Option Bool) ⊕ Fin m

/-- Edges before symmetrisation: inside each triangle, and from a literal to the clauses
containing it. -/
def gadgetRel (φ : List (List (ℕ × Bool))) (N : ℕ) :
    GadgetV N φ.length → GadgetV N φ.length → Prop
  | .inl (i, _), .inl (i', _) => i = i'
  | .inl (i, some b), .inr j => ((i : ℕ), b) ∈ φ.get j
  | _, _ => False

/-- The gadget graph of `φ` with `N` variables. -/
def satGadget (φ : List (List (ℕ × Bool))) (N : ℕ) : SimpleGraph (GadgetV N φ.length) :=
  SimpleGraph.fromRel (gadgetRel φ N)

/-- **SAT → MDS.** If every variable of `φ` is `< N`, `φ` is satisfiable iff its gadget has a
dominating set of at most `N` vertices. -/
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

end RadiusClustering.PEqualNP
