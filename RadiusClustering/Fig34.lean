import RadiusClustering.Curgraph
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Fig. 3.4: the 4-point example, checked

Points `x1, x2, x3, x4` are `0, 1, 2, 3`. In the figure, `P*_i` is the `i`-th partition output by
Curgraph, not the number of clusters (`docs/cadrage.md` §2).
-/

namespace RadiusClustering

/-- Dissimilarity matrix of Fig. 3.4a. -/
def fig34 : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 1, 4],
    ![2, 0, 1, 4],
    ![1, 1, 0, 4],
    ![4, 4, 4, 0]]

theorem fig34_isDissimilarity : IsDissimilarity fig34 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem fig34_eq_of_le_zero : ∀ x y : Fin 4, fig34 x y ≤ 0 → x = y := by
  decide

/-- At radius `0` every cluster is a single point. -/
theorem fig34_injective_of_valid_zero {k : ℕ} {τ : ℕ} (hτ : τ < 1) {f : Fin 4 → Fin k}
    (hf : IsValidClustering fig34 τ f) : Function.Injective f := by
  intro a b hab
  obtain ⟨c, -, hc⟩ := hf a
  have ha := fig34_eq_of_le_zero c a (by have := hc a rfl; omega)
  have hb := fig34_eq_of_le_zero c b (by have := hc b hab.symm; omega)
  rw [← ha, ← hb]

/-- The three partitions output by Curgraph: `R*_1 = 4`, `R*_2 = 1`, `R*_4 = 0` (indexed by the
number of clusters). -/
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
