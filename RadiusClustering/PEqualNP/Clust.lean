import RadiusClustering.Fig34
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# The language CLUST, in pequalnp's encoding

Instances `(k, τ, M)` with `M` the strict upper triangle of an integer dissimilarity, encoded as
pequalnp encodes SAT (`PEqualNP/Defs/Search.lean`): a number is its binary digits (`Nat.bits`),
each as `[true, b]`, then `[false, true]`; a row ends with `[false, false]`.
`docs/cadrage.md` §5 records the choices.
-/

namespace RadiusClustering.PEqualNP

/-- Binary code of a natural number, as in pequalnp's `encodeLiteral`. -/
def encNat (a : ℕ) : List Bool :=
  (a.bits.flatMap fun b => [true, b]) ++ [false, true]

/-- A row: its numbers, then the end-of-row pair. -/
def encRow (row : List ℕ) : List Bool :=
  row.flatMap encNat ++ [false, false]

/-- An instance: `k`, `τ`, then the rows of `M`. -/
def encInst (k τ : ℕ) (M : List (List ℕ)) : List Bool :=
  encNat k ++ encNat τ ++ M.flatMap encRow

/-- Row `i` of `M` holds `d(i, j)` for `j > i`: it has `n - 1 - i` entries. -/
def IsTriangular (M : List (List ℕ)) : Prop :=
  ∀ i : Fin M.length, (M.get i).length = M.length - 1 - i.val

/-- The dissimilarity read off the upper triangle `M`. -/
def triDissim (M : List (List ℕ)) (i j : Fin M.length) : ℕ :=
  if i < j then (M.get i).getD (j.val - i.val - 1) 0
  else if j < i then (M.get j).getD (i.val - j.val - 1) 0
  else 0

/-- CLUST: the encodings of the instances with a partition into at most `k` clusters of radius
`≤ τ`. -/
def clustLang : Set (List Bool) :=
  {x | ∃ (M : List (List ℕ)) (k τ : ℕ), x = encInst k τ M ∧ IsTriangular M ∧
    ∃ f : Fin M.length → Fin k, IsValidClustering (triDissim M) τ f}

/-- The upper triangle of a dissimilarity on `Fin n`. -/
def toTri {n : ℕ} (d : Fin n → Fin n → ℕ) : List (List ℕ) :=
  List.ofFn fun i : Fin n => List.ofFn fun j : Fin (n - 1 - i.val) =>
    d i ⟨i.val + 1 + j.val, by omega⟩

/-- The candidate statement for pequalnp writes CLUST inline; it is this set. -/
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

/-- **Bridge (1).** The dissimilarity read off a triangle is a dissimilarity (Def. 1.2). -/
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

/-- Moving a clustering along a relabelling of the points. -/
theorem isValidClustering_comp_equiv {m n k : ℕ} (e : Fin m ≃ Fin n) {d : Fin n → Fin n → ℕ}
    {d' : Fin m → Fin m → ℕ} (hdd' : ∀ i j, d' i j = d (e i) (e j)) {τ : ℕ} (f : Fin n → Fin k)
    (hf : IsValidClustering d τ f) : IsValidClustering d' τ (f ∘ e) := by
  intro y
  obtain ⟨c, hc, hcz⟩ := hf (e y)
  refine ⟨e.symm c, by simp [hc], fun z hz => ?_⟩
  rw [hdd', Equiv.apply_symm_apply]
  exact hcz (e z) hz

/-- **Bridge (2).** CLUST holds exactly the encodings of `(k, τ, d)` with `d` a dissimilarity on
`n` points and a partition into at most `k` clusters of radius `≤ τ`. -/
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

end RadiusClustering.PEqualNP
