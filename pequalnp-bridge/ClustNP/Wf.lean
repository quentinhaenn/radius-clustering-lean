import ClustNP.Read

/-!
# The acceptor `wfI` recognises the encodings of instances
-/

namespace ClustNP

open PEqualNP.Library.SearchHelpers.SatV
open RadiusClustering.PEqualNP

/-- From phase `p`, the rest `s` is accepted. -/
def Acc (p : Ph) (s : List Bool) : Prop := s.foldl wfD (p, none) = (Ph.R, none)

/-- Digit pairs. -/
local notation "Dg" ds => List.flatMap (fun d => [true, d]) ds

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

/-! ### Encodings are accepted -/

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

/-! ### Accepted strings are encodings -/

/-- A digit list with no trailing `false` is the binary code of a number. -/
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
    encNat a = (Dg ds) ++ [false, true] := by
  rw [encNat, h]

theorem num_parse (C D nxt : Ph) (hC : ∀ d, phD C true d = if d then C else D)
    (hD : ∀ d, phD D true d = if d then C else D) (hCE : phD C false true = nxt)
    (hCF : phD C false false = Ph.dead) (hDF : ∀ b, phD D false b = Ph.dead)
    (hCR : C ≠ Ph.R) (hDR : D ≠ Ph.R) :
    ∀ (n : ℕ) (s : List Bool), s.length ≤ n →
      (Acc C s → ∃ ds r, s = (Dg ds) ++ false :: true :: r ∧
        (ds = [] ∨ ds.getLast? = some true) ∧ Acc nxt r) ∧
      (Acc D s → ∃ ds r, s = (Dg ds) ++ false :: true :: r ∧ ds.getLast? = some true ∧
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
          Acc q (a :: b :: r) → ∃ ds r', a :: b :: r = (Dg ds) ++ false :: true :: r' ∧
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
    /- One pair read from `R` or `O`, landing in `O` after a whole number. -/
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
        obtain ⟨ds, r', rfl, hl, hacc⟩ : ∃ ds r', r = (Dg ds) ++ false :: true :: r' ∧
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
