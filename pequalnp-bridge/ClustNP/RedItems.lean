import ClustNP.RedDefs
import ClustNP.InNP
import PEqualNP.Library.SearchHelpers.TwoSatStr

/-!
# The string functions of the reduction on encodings of formulas

The encoding of `φ` is the concatenation of the codes of its items (`encodeCNF_eq_items`). On it,
`endAt`, `varAt`, `repAt`, `segAt` and `adjAt` compute the item gadget of `ItemGadget.lean`
(`adjAt_iff`).
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search
open RadiusClustering RadiusClustering.PEqualNP

/-- The code of an item. -/
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

/-- The variable code of an item. -/
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

/-! ### Representatives -/

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

/-! ### Clause segments -/

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
