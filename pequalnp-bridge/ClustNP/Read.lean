import ClustNP.Defs

/-!
# The string functions of the verifier on encodings

What `leF`, `endsU`, `dropRow`, `rowLenU`, `rowsS`, `entryS` and `cntS` compute on encodings
of instances.
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.S2D (incB dig bits_succ)
open RadiusClustering.PEqualNP

theorem encNat_eq_vcode (a : ℕ) : encNat a = vcode a := rfl

theorem encNat_bit (b : Bool) (n : ℕ) (h : n = 0 → b = true) :
    encNat (Nat.bit b n) = true :: b :: encNat n := vcode_bit b n h

theorem encNat_zero : encNat 0 = [false, true] := rfl

theorem headI_encNat (a : ℕ) (r : List Bool) : headI (encNat a ++ r) = encNat a :=
  headI_vcode a r

theorem dropI_encNat (a : ℕ) (r : List Bool) : dropI (encNat a ++ r) = r := dropI_vcode a r

/-! ### Comparison -/

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

/-! ### Rows -/

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

/-- The entry `d(s, y)`, `s < y`, of a triangular instance. -/
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

/-! ### The number of centres -/

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
