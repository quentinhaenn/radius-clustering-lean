import RadiusClustering.Curgraph
import Mathlib.Data.Fin.VecNotation

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
  sorry

/-- `R*_1 = 4`, `R*_2 = 1`, `R*_3 = 1`, `R*_4 = 0`. -/
theorem fig34_minRadius :
    IsMinRadius fig34 1 4 ∧ IsMinRadius fig34 2 1 ∧ IsMinRadius fig34 3 1 ∧
      IsMinRadius fig34 4 0 := by
  sorry

end RadiusClustering
