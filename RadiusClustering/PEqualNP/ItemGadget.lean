import RadiusClustering.PEqualNP.SatToClust

/-!
# SAT → dominating set, indexed by the items of the encoding (intermediate lemma)

The gadget of `SatGadget.lean` has one triangle per variable below `N`, exponential in the length
of the encoding. Here a vertex block `{3p, 3p + 1, 3p + 2}` stands for item `p` of the encoding
(a literal, or the end of a clause), so the graph has `3 × (number of items)` vertices.
Rationale and layout: `docs/pequalnp.md`.
-/

namespace RadiusClustering.PEqualNP

/-- The items of `φ` in reading order: `some l` a literal, `none` the end of a clause. -/
def items (φ : List (List (ℕ × Bool))) : List (Option (ℕ × Bool)) :=
  φ.flatMap fun c => c.map some ++ [none]

/-- Item `p` is the literal `l` and no earlier item has the variable of `l`. -/
def IsRep (its : List (Option (ℕ × Bool))) (p : ℕ) (l : ℕ × Bool) : Prop :=
  its[p]? = some (some l) ∧ ∀ q < p, ∀ l', its[q]? = some (some l') → l'.1 ≠ l.1

/-- `l` is a literal of the clause closed by item `p`. -/
def InSeg (its : List (Option (ℕ × Bool))) (p : ℕ) (l : ℕ × Bool) : Prop :=
  ∃ r < p, its[r]? = some (some l) ∧ ∀ r', r < r' → r' < p → its[r']? ≠ some none

/-- Edges before symmetrisation. Vertex `i` is in block `i / 3` with role `i % 3`: `0` true,
`1` false, `2` the third vertex of a literal block or the clause vertex of an end block. -/
def itemRel (its : List (Option (ℕ × Bool))) (i j : ℕ) : Prop :=
  if i / 3 = j / 3 then (i % 3 < 2 ∧ j % 3 < 2) ∨ ∃ l, its[i / 3]? = some (some l)
  else i % 3 < 2 ∧ j % 3 = 2 ∧ its[j / 3]? = some none ∧
    ∃ l, IsRep its (i / 3) l ∧ InSeg its (j / 3) (l.1, decide (i % 3 = 0))

/-- The item gadget. -/
def itemGadget (its : List (Option (ℕ × Bool))) : SimpleGraph (Fin (3 * its.length)) :=
  SimpleGraph.fromRel fun i j => itemRel its i j

/-! ### Clauses as segments of items -/

private theorem getElem?_pre_lt {c : List (ℕ × Bool)} {rest : List (Option (ℕ × Bool))}
    {r : ℕ} (hr : r < c.length) : (c.map some ++ none :: rest)[r]? = some (some c[r]) := by
  rw [List.getElem?_append_left (by simpa using hr)]
  simp [hr]

private theorem getElem?_pre_eq {c : List (ℕ × Bool)} {rest : List (Option (ℕ × Bool))} :
    (c.map some ++ none :: rest)[c.length]? = some none := by
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem getElem?_pre_gt {c : List (ℕ × Bool)} {rest : List (Option (ℕ × Bool))}
    (p : ℕ) : (c.map some ++ none :: rest)[p + c.length + 1]? = rest[p]? := by
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map]
  rw [show p + c.length + 1 - c.length = p + 1 by omega]
  simp

private theorem inSeg_here (c : List (ℕ × Bool)) (rest : List (Option (ℕ × Bool)))
    (l : ℕ × Bool) : InSeg (c.map some ++ none :: rest) c.length l ↔ l ∈ c := by
  constructor
  · rintro ⟨r, hr, hl, -⟩
    rw [getElem?_pre_lt hr] at hl
    simp only [Option.some.injEq] at hl
    rw [← hl]
    exact List.getElem_mem hr
  · intro hl
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hl
    refine ⟨r, hr, getElem?_pre_lt hr, fun r' _ hr' => ?_⟩
    rw [getElem?_pre_lt hr']
    simp

private theorem inSeg_shift (c : List (ℕ × Bool)) (rest : List (Option (ℕ × Bool)))
    (p : ℕ) (l : ℕ × Bool) :
    InSeg (c.map some ++ none :: rest) (p + c.length + 1) l ↔ InSeg rest p l := by
  constructor
  · rintro ⟨r, hr, hl, hno⟩
    by_cases hrc : r ≤ c.length
    · exfalso
      rcases Nat.lt_or_eq_of_le hrc with h | h
      · exact hno c.length h (by omega) getElem?_pre_eq
      · subst h
        rw [getElem?_pre_eq] at hl
        simp at hl
    · obtain ⟨r, rfl⟩ : ∃ r', r = r' + c.length + 1 := ⟨r - c.length - 1, by omega⟩
      refine ⟨r, by omega, by rwa [getElem?_pre_gt] at hl, fun r' h1 h2 => ?_⟩
      have := hno (r' + c.length + 1) (by omega) (by omega)
      rwa [getElem?_pre_gt] at this
  · rintro ⟨r, hr, hl, hno⟩
    refine ⟨r + c.length + 1, by omega, by rwa [getElem?_pre_gt], fun r' h1 h2 => ?_⟩
    obtain ⟨r', rfl⟩ : ∃ r'', r' = r'' + c.length + 1 := ⟨r' - c.length - 1, by omega⟩
    rw [getElem?_pre_gt]
    exact hno r' (by omega) (by omega)

private theorem items_cons (c : List (ℕ × Bool)) (φ : List (List (ℕ × Bool))) :
    items (c :: φ) = c.map some ++ none :: items φ := by
  simp [items]

/-- Every clause of `φ` is the segment of some end item. -/
theorem exists_inSeg_of_mem (φ : List (List (ℕ × Bool))) :
    ∀ c ∈ φ, ∃ p, (items φ)[p]? = some none ∧ ∀ l, InSeg (items φ) p l ↔ l ∈ c := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    intro c' hc'
    rw [items_cons]
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨c'.length, getElem?_pre_eq, inSeg_here c' _⟩
    · obtain ⟨p, hp, hseg⟩ := ih c' hc'
      refine ⟨p + c.length + 1, by rwa [getElem?_pre_gt], fun l => ?_⟩
      rw [inSeg_shift]
      exact hseg l

/-- The segment of every end item is a clause of `φ`. -/
theorem exists_mem_of_inSeg (φ : List (List (ℕ × Bool))) :
    ∀ p, (items φ)[p]? = some none → ∃ c ∈ φ, ∀ l, InSeg (items φ) p l ↔ l ∈ c := by
  induction φ with
  | nil => simp [items]
  | cons c φ ih =>
    intro p hp
    rw [items_cons] at hp ⊢
    rcases lt_trichotomy p c.length with h | rfl | h
    · rw [getElem?_pre_lt h] at hp
      simp at hp
    · exact ⟨c, List.mem_cons_self .., inSeg_here c _⟩
    · obtain ⟨p, rfl⟩ : ∃ p', p = p' + c.length + 1 := ⟨p - c.length - 1, by omega⟩
      rw [getElem?_pre_gt] at hp
      obtain ⟨c', hc', hseg⟩ := ih p hp
      refine ⟨c', List.mem_cons_of_mem _ hc', fun l => ?_⟩
      rw [inSeg_shift]
      exact hseg l

/-! ### Representatives -/

theorem exists_isRep {its : List (Option (ℕ × Bool))} {q : ℕ} {l : ℕ × Bool}
    (hq : its[q]? = some (some l)) : ∃ r l', IsRep its r l' ∧ l'.1 = l.1 := by
  classical
  have hex : ∃ r, ∃ l' : ℕ × Bool, its[r]? = some (some l') ∧ l'.1 = l.1 := ⟨q, l, hq, rfl⟩
  obtain ⟨l', hl', hv⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, l', ⟨hl', fun q' hq' l'' hl'' he => ?_⟩, hv⟩
  exact Nat.find_min hex hq' ⟨l'', hl'', he.trans hv⟩

theorem IsRep.unique {its : List (Option (ℕ × Bool))} {r r' : ℕ} {l l' : ℕ × Bool}
    (h : IsRep its r l) (h' : IsRep its r' l') (hv : l.1 = l'.1) : r = r' := by
  rcases lt_trichotomy r r' with hlt | heq | hlt
  · exact absurd hv (h'.2 r hlt l h.1)
  · exact heq
  · exact absurd hv.symm (h.2 r' hlt l' h'.1)

/-! ### Blocks -/

private theorem getElem?_isSome {its : List (Option (ℕ × Bool))} {p : ℕ} (hp : p < its.length) :
    (∃ l, its[p]? = some (some l)) ∨ its[p]? = some none := by
  rw [List.getElem?_eq_getElem hp]
  rcases its[p] with _ | l
  · exact Or.inr rfl
  · exact Or.inl ⟨l, rfl⟩

private theorem adj_iff {its : List (Option (ℕ × Bool))} (u v : Fin (3 * its.length)) :
    (itemGadget its).Adj u v ↔ u ≠ v ∧ (itemRel its u v ∨ itemRel its v u) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The neighbours of the third vertex of a literal block, and of the false vertex of an end
block, lie in their block. -/
private theorem block_of_adj {its : List (Option (ℕ × Bool))} {s v : Fin (3 * its.length)}
    (hadj : (itemGadget its).Adj s v)
    (hv : (v.val % 3 = 2 ∧ ∃ l, its[v.val / 3]? = some (some l)) ∨
      (v.val % 3 = 1 ∧ its[v.val / 3]? = some none)) : s.val / 3 = v.val / 3 := by
  by_contra hne
  have hne' : v.val / 3 ≠ s.val / 3 := Ne.symm hne
  rw [adj_iff] at hadj
  rcases hadj.2 with h | h
  · simp only [itemRel, hne, ↓reduceIte] at h
    obtain ⟨-, h2, hnone, -⟩ := h
    rcases hv with ⟨-, l, hl⟩ | ⟨h1, -⟩
    · rw [hl] at hnone; simp at hnone
    · omega
  · simp only [itemRel, hne', ↓reduceIte] at h
    obtain ⟨h1, -, -, l, hrep, -⟩ := h
    rcases hv with ⟨h2, -⟩ | ⟨-, hnone⟩
    · omega
    · rw [hrep.1] at hnone; simp at hnone

/-! ### The equivalence -/

/-- **SAT → MDS on items.** `φ` is satisfiable iff its item gadget has a dominating set of at
most `(items φ).length` vertices. -/
theorem satisfiable_iff_exists_dominating_items (φ : List (List (ℕ × Bool))) :
    (∃ σ : ℕ → Bool, (φ.all fun c => c.any fun l => σ l.1 == l.2) = true) ↔
      ∃ S : Finset (Fin (3 * (items φ).length)), S.card ≤ (items φ).length ∧
        IsDominating (itemGadget (items φ)) S := by
  classical
  set its := items φ with hits
  set L := its.length
  /- Vertex `3p + t` of block `p`. -/
  let vx : ∀ p, p < L → ∀ t, t < 3 → Fin (3 * L) := fun p hp t ht => ⟨3 * p + t, by omega⟩
  have vx_div : ∀ p hp t ht, (vx p hp t ht).val / 3 = p := fun p _ t _ => by
    simp only [vx]; omega
  have vx_mod : ∀ p hp t ht, (vx p hp t ht).val % 3 = t := fun p _ t _ => by
    simp only [vx]; omega
  constructor
  · rintro ⟨σ, hσ⟩
    /- Block `p` contributes its true or false vertex (per `σ`) for a literal, its true vertex
    for an end. -/
    let role : ℕ → ℕ := fun p => match its[p]? with
      | some (some l) => if σ l.1 then 0 else 1
      | _ => 0
    have role_lt : ∀ p, role p < 3 := fun p => by
      simp only [role]; split <;> (try split) <;> omega
    let pick : Fin L → Fin (3 * L) := fun p => vx p p.2 (role p) (role_lt p)
    have pick_div : ∀ q : Fin L, (pick q).val / 3 = q.val := fun q => vx_div q q.2 _ (role_lt q)
    have pick_mod : ∀ q : Fin L, (pick q).val % 3 = role q := fun q => vx_mod q q.2 _ (role_lt q)
    refine ⟨Finset.univ.image pick, Finset.card_image_le.trans (by simp [L]), fun v => ?_⟩
    have hvL : v.val / 3 < L := by omega
    by_cases hin : v ∈ Finset.univ.image pick
    · exact Or.inl hin
    right
    have hpv : (pick ⟨v.val / 3, hvL⟩).val / 3 = v.val / 3 := pick_div _
    have hne : pick ⟨v.val / 3, hvL⟩ ≠ v := fun h => hin (h ▸ Finset.mem_image_of_mem _ (by simp))
    rcases getElem?_isSome hvL with ⟨l, hl⟩ | hnone
    · /- Literal block: the triangle. -/
      refine ⟨pick ⟨v.val / 3, hvL⟩, Finset.mem_image_of_mem _ (by simp), ?_⟩
      rw [adj_iff]
      refine ⟨hne, Or.inl ?_⟩
      simp only [itemRel, hpv, ↓reduceIte]
      exact Or.inr ⟨l, hl⟩
    · have hpick : (pick ⟨v.val / 3, hvL⟩).val % 3 = 0 := by
        rw [pick_mod]; simp [role, hnone]
      by_cases hv2 : v.val % 3 = 2
      · /- Clause vertex: a true literal of the clause, through its representative. -/
        obtain ⟨c, hc, hseg⟩ := exists_mem_of_inSeg φ _ hnone
        rw [← hits] at hseg
        have hcσ : (c.any fun l => σ l.1 == l.2) = true := List.all_eq_true.1 hσ c hc
        obtain ⟨l, hlc, hlσ⟩ := List.any_eq_true.1 hcσ
        have hlσ' : σ l.1 = l.2 := by simpa using hlσ
        obtain ⟨r0, hr0, hr0l, -⟩ := (hseg l).2 hlc
        obtain ⟨r, l', hrep, hvar⟩ := exists_isRep hr0l
        have hrL : r < L := by
          by_contra h
          have := hrep.1
          rw [List.getElem?_eq_none (by omega)] at this
          simp at this
        refine ⟨pick ⟨r, hrL⟩, Finset.mem_image_of_mem _ (by simp), ?_⟩
        have hpr : (pick ⟨r, hrL⟩).val / 3 = r := pick_div _
        have hpm : (pick ⟨r, hrL⟩).val % 3 = if σ l'.1 then 0 else 1 := by
          rw [pick_mod]; simp [role, hrep.1]
        have hrv : r ≠ v.val / 3 := by
          intro h
          have := hrep.1
          rw [h, hnone] at this
          simp at this
        rw [adj_iff]
        refine ⟨fun h => hrv (by rw [← hpr, h]), Or.inl ?_⟩
        simp only [itemRel, hpr, hrv, ↓reduceIte, hpm]
        refine ⟨by split <;> omega, hv2, hnone, l', hrep, ?_⟩
        have hpol : decide ((if σ l'.1 = true then 0 else 1) = 0) = l.2 := by
          rw [hvar, hlσ']; cases l.2 <;> simp
        rw [hpol, hvar]
        exact (hseg l).2 hlc
      · /- False vertex of an end block: the true vertex. -/
        refine ⟨pick ⟨v.val / 3, hvL⟩, Finset.mem_image_of_mem _ (by simp), ?_⟩
        rw [adj_iff]
        refine ⟨hne, Or.inl ?_⟩
        simp only [itemRel, hpv, ↓reduceIte]
        exact Or.inl ⟨by omega, by omega⟩
  · rintro ⟨S, hSL, hS⟩
    /- Every block meets `S`. -/
    have hblock : ∀ p, p < L → ∃ s ∈ S, s.val / 3 = p := by
      intro p hp
      rcases getElem?_isSome hp with ⟨l, hl⟩ | hnone
      · have hv := vx_div p hp 2 (by omega)
        rcases hS (vx p hp 2 (by omega)) with h | ⟨s, hs, hadj⟩
        · exact ⟨_, h, hv⟩
        · refine ⟨s, hs, ?_⟩
          rw [block_of_adj hadj (Or.inl ⟨vx_mod p hp 2 (by omega), l, by rw [hv]; exact hl⟩), hv]
      · have hv := vx_div p hp 1 (by omega)
        rcases hS (vx p hp 1 (by omega)) with h | ⟨s, hs, hadj⟩
        · exact ⟨_, h, hv⟩
        · refine ⟨s, hs, ?_⟩
          rw [block_of_adj hadj (Or.inr ⟨vx_mod p hp 1 (by omega), by rw [hv]; exact hnone⟩), hv]
    /- Hence exactly one vertex of `S` per block. -/
    have himg : S.image (fun s => s.val / 3) = Finset.range L := by
      apply Finset.eq_of_subset_of_card_le
      · intro p hp
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hp
        simp only [Finset.mem_range]; omega
      · apply Finset.card_le_card
        intro p hp
        obtain ⟨s, hs, rfl⟩ := hblock p (Finset.mem_range.1 hp)
        exact Finset.mem_image_of_mem _ hs
    have hinj : Set.InjOn (fun s : Fin (3 * L) => s.val / 3) S := by
      apply Finset.card_image_iff.1
      have := Finset.card_image_le (s := S) (f := fun s : Fin (3 * L) => s.val / 3)
      rw [himg, Finset.card_range] at this ⊢
      omega
    have huniq : ∀ s ∈ S, ∀ s' ∈ S, s.val / 3 = s'.val / 3 → s = s' :=
      fun s hs s' hs' h => hinj hs hs' h
    /- The assignment read on the true vertices of the representatives. -/
    refine ⟨fun v => decide (∃ r l, IsRep its r l ∧ l.1 = v ∧ ∃ s ∈ S, s.val = 3 * r), ?_⟩
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨p, hp, hseg⟩ := exists_inSeg_of_mem φ c hc
    rw [← hits] at hp hseg
    have hpL : p < L := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hp
      simp at hp
    have hw2 := vx_div p hpL 2 (by omega)
    have hw1 := vx_div p hpL 1 (by omega)
    rcases hS (vx p hpL 2 (by omega)) with hw | ⟨s, hs, hadj⟩
    · /- The clause vertex itself would leave the false vertex of its block undominated. -/
      exfalso
      rcases hS (vx p hpL 1 (by omega)) with hu | ⟨s, hs, hadj⟩
      · have := congrArg Fin.val (huniq _ hu _ hw (by rw [hw1, hw2]))
        simp [vx] at this
      · have hsb := block_of_adj hadj (Or.inr ⟨vx_mod p hpL 1 (by omega), by rw [hw1]; exact hp⟩)
        obtain rfl := huniq _ hs _ hw (by rw [hsb, hw1, hw2])
        rw [adj_iff] at hadj
        rcases hadj.2 with h | h <;>
          simp only [itemRel, hw1, hw2, vx_mod, ↓reduceIte, hp] at h <;> simp at h
    · have hsp : s.val / 3 ≠ p := by
        intro h
        rw [adj_iff] at hadj
        rcases hadj.2 with h' | h' <;>
          simp only [itemRel, h, hw2, vx_mod, ↓reduceIte, hp] at h' <;> simp at h'
      rw [adj_iff] at hadj
      rcases hadj.2 with h | h
      · simp only [itemRel, hw2, hsp, ↓reduceIte, vx_mod] at h
        obtain ⟨hs2, -, -, l, hrep, hin⟩ := h
        rw [List.any_eq_true]
        refine ⟨_, (hseg _).1 hin, ?_⟩
        simp only [beq_iff_eq, decide_eq_decide]
        constructor
        · rintro ⟨r, l', hrep', hv, s', hs', hs'r⟩
          obtain rfl := hrep'.unique hrep hv
          obtain rfl := huniq _ hs' _ hs (by omega)
          omega
        · intro h0
          exact ⟨s.val / 3, l, hrep, rfl, s, hs, by omega⟩
      · simp only [itemRel, hw2, Ne.symm hsp, ↓reduceIte, vx_mod] at h
        omega

end RadiusClustering.PEqualNP

namespace RadiusClustering.PEqualNP

open Classical in
/-- The instance built from `φ`: `k` the number of items, `τ = 1`, `d` the graph dissimilarity of
the item gadget. -/
noncomputable def itemInst (φ : List (List (ℕ × Bool))) : List Bool :=
  encInst (items φ).length 1 (toTri (graphDissim (itemGadget (items φ))))

/-- **SAT → CLUST on items.** `φ` is satisfiable iff `itemInst φ` is in CLUST. -/
theorem satisfiable_iff_itemInst_mem (φ : List (List (ℕ × Bool))) :
    (∃ σ : ℕ → Bool, (φ.all fun c => c.any fun l => σ l.1 == l.2) = true) ↔
      itemInst φ ∈ clustLang := by
  classical
  have hdis := isDissimilarity_graphDissim (itemGadget (items φ))
  rw [satisfiable_iff_exists_dominating_items,
    exists_dominating_iff_exists_validClustering_graphDissim, itemInst]
  constructor
  · rintro ⟨f, hf⟩
    exact (mem_clustLang_iff _).2 ⟨_, _, 1, _, hdis, rfl, f, hf⟩
  · rintro ⟨M, k, τ, h, -, f, hf⟩
    obtain ⟨rfl, rfl, rfl⟩ := encInst_injective h
    let e : Fin (toTri (graphDissim (itemGadget (items φ)))).length ≃
        Fin (3 * (items φ).length) := finCongr (length_toTri _)
    refine ⟨f ∘ e.symm, isValidClustering_comp_equiv e.symm (d := triDissim _) ?_ f hf⟩
    intro u v
    rw [triDissim_toTri hdis]
    simp [e]

end RadiusClustering.PEqualNP
