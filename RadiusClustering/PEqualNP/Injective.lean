import RadiusClustering.PEqualNP.Clust

/-!
# Unique reading of the CLUST encoding
-/

namespace RadiusClustering.PEqualNP

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

/-- **Unique reading.** An encoding determines `k`, `τ` and the rows. -/
theorem encInst_injective {k τ k' τ' : ℕ} {M M' : List (List ℕ)}
    (h : encInst k τ M = encInst k' τ' M') : k = k' ∧ τ = τ' ∧ M = M' := by
  unfold encInst at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨e1, h2⟩ := encNat_prefix h
  obtain ⟨e2, h3⟩ := encNat_prefix h2
  exact ⟨e1, e2, flatMap_encRow_inj _ _ h3⟩

end RadiusClustering.PEqualNP
