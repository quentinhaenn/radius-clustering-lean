import ClustNP.RedDefs
import ClustNP.CPT

/-!
# `red` is polynomial-time computable

Same method as `CPT.lean`: every subexpression is a polynomial-time function of one packed
string, booleans are flags combined with `sel`, loops are `cpt_flatMapRange`.
-/

namespace ClustNP

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
  PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Library.SearchHelpers.S2D
  PEqualNP.Library.SearchHelpers.KSat.Hard

local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Transducers -/

def itD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, _ => (.b, some true)
  | _, _ => (.b, none)

theorem itD_run : ∀ s : List Bool, fstRun itD (fun _ => none) PS.b s = itemsU s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: b :: r => by simp [fstRun, itD, itemsU, itD_run r]
  | true :: b :: r => by simp [fstRun, itD, itemsU, itD_run r]

theorem cpt_itemsU : CPTs itemsU :=
  fst_polyTime _ _ _ itD (fun _ => none) PS.b (fun s => (itD_run s).symm)

def d3D : Fin 3 → Bool → Fin 3 × Option Bool
  | q, _ => (q + 1, if q = 2 then some true else none)

theorem d3D_run (l : List Bool) : ∀ q : Fin 3,
    fstRun d3D (fun _ => none) q l = un ((q.val + l.length) / 3) := by
  induction l with
  | nil => intro q; fin_cases q <;> simp [fstRun, un]
  | cons a l ih =>
    intro q
    simp only [fstRun, d3D, ih, List.length_cons]
    fin_cases q
    · simp only [Fin.zero_eta, Fin.isValue]
      simp; congr 1; omega
    · simp; congr 1; omega
    · have h2 : (2 + (l.length + 1)) / 3 = (0 + l.length) / 3 + 1 := by omega
      simp [h2, un, List.replicate_succ]

theorem cpt_div3 : CPTs div3 :=
  fst_polyTime _ _ _ d3D (fun _ => none) 0 (fun s => by simp [div3, d3D_run s 0])

def m3D : Fin 3 → Bool → Fin 3 × Option Bool
  | q, _ => (q + 1, none)

theorem m3D_run (k : ℕ) (l : List Bool) : ∀ q : Fin 3,
    fstRun m3D (fun q => if q.val = k then some true else none) q l =
      bflag (decide ((q.val + l.length) % 3 = k)) := by
  induction l with
  | nil =>
    intro q
    have h : q.val % 3 = q.val := Nat.mod_eq_of_lt q.isLt
    by_cases hk : q.val = k
    · subst hk; simp [fstRun, bflag, h]
    · simp [fstRun, bflag, h, hk]
  | cons a l ih =>
    intro q
    have key : ((q + 1 : Fin 3).val + l.length) % 3 = (q.val + (l.length + 1)) % 3 := by
      fin_cases q <;> simp <;> omega
    simp only [fstRun, m3D, ih, List.length_cons, Option.toList_none, List.nil_append, key]

theorem cpt_isR (k : ℕ) : CPTs (fun u => bflag (decide (u.length % 3 = k))) :=
  fst_polyTime _ _ _ m3D (fun q => if q.val = k then some true else none) 0
    (fun s => by simp [m3D_run k s 0])

theorem cpt_isR0 : CPTs (fun u => bflag (isR0 u)) := cpt_isR 0
theorem cpt_isR2 : CPTs (fun u => bflag (isR2 u)) := cpt_isR 2

/-! ### Flags -/

theorem flag_not (b : Bool) : sel (bflag b) [true] [] = bflag (!b) := by
  cases b <;> simp [sel, bflag]

theorem flag_or (a b : Bool) : sel (bflag a) (bflag b) [true] = bflag (a || b) := by
  cases a <;> cases b <;> simp [sel, bflag]

theorem flag_if (c : Prop) [Decidable c] (A B : Bool) :
    bflag (if c then A else B) = sel (bflag (decide c)) (bflag B) (bflag A) := by
  by_cases h : c <;> simp [sel, bflag, h]

theorem cons_flag (b : Bool) (l : List Bool) :
    b :: l = sel (bflag b) (false :: l) (true :: l) := by
  cases b <;> simp [sel, bflag]

theorem cpt_bAnd {a b : List Bool → Bool} (ha : CPTs fun s => bflag (a s))
    (hb : CPTs fun s => bflag (b s)) : CPTs fun s => bflag (a s && b s) :=
  cptE (cpt_sel ha (cpt_const []) hb) (fun _ => flag_and _ _)

theorem cpt_bOr {a b : List Bool → Bool} (ha : CPTs fun s => bflag (a s))
    (hb : CPTs fun s => bflag (b s)) : CPTs fun s => bflag (a s || b s) :=
  cptE (cpt_sel ha hb (cpt_const [true])) (fun _ => flag_or _ _)

theorem cpt_bNot {a : List Bool → Bool} (ha : CPTs fun s => bflag (a s)) :
    CPTs fun s => bflag (!a s) :=
  cptE (cpt_sel ha (cpt_const [true]) (cpt_const [])) (fun _ => flag_not _)

theorem cpt_bIf {c : List Bool → Prop} [∀ s, Decidable (c s)] {A B : List Bool → Bool}
    (hc : CPTs fun s => bflag (decide (c s))) (hA : CPTs fun s => bflag (A s))
    (hB : CPTs fun s => bflag (B s)) : CPTs fun s => bflag (if c s then A s else B s) :=
  cptE (cpt_sel hc hB hA) (fun _ => (flag_if _ _ _).symm)

theorem cpt_bEmpty {F : List Bool → List Bool} (hF : CPTs F) :
    CPTs fun s => bflag (F s).isEmpty :=
  cptE (cpt_sel hF (cpt_const [true]) (cpt_const [])) (fun _ => flag_em _)

theorem cpt_bNonempty {F : List Bool → List Bool} (hF : CPTs F) :
    CPTs fun s => bflag (!(F s).isEmpty) :=
  cptE (cpt_sel hF (cpt_const []) (cpt_const [true])) (fun _ => flag_ne _)

theorem cpt_consFlag (b : List Bool → Bool) {l : List Bool → List Bool}
    (hb : CPTs fun s => bflag (b s)) (hl : CPTs l) : CPTs fun s => b s :: l s :=
  cptE (cpt_sel hb (cpt_cons1 false hl) (cpt_cons1 true hl)) (fun _ => (cons_flag _ _).symm)

/-! ### Items -/

theorem cpt_vertsU : CPTs vertsU :=
  cptE (cpt_app2 (cpt_app2 cpt_itemsU cpt_itemsU) cpt_itemsU) (fun _ => rfl)

theorem cpt_restAt {u x : List Bool → List Bool} (hu : CPTs u) (hx : CPTs x) :
    CPTs fun s => restAt (u s) (x s) :=
  cpt_iterLen cpt_dropI dropI_length hu hx

theorem cpt_endAt {u x : List Bool → List Bool} (hu : CPTs u) (hx : CPTs x) :
    CPTs fun s => bflag (endAt (u s) (x s)) :=
  cpt_comp (g := fun r => bflag (isEnd r)) (cpt_restAt hu hx) cpt_isEndF

theorem cpt_varAt {u x : List Bool → List Bool} (hu : CPTs u) (hx : CPTs x) :
    CPTs fun s => varAt (u s) (x s) :=
  cpt_tail1 (cpt_tail1 (cpt_comp (cpt_restAt hu hx) cpt_headI))

theorem cpt_sameVar : CPTs sameVar := by
  have hR : CPTs fun z => (unpairB z).2 := cpt_unpairB2
  have hx := cpt_unpairB2_1 hR
  exact cpt_eqF (cpt_varAt cpt_unpairB1 hx) (cpt_varAt (cpt_unpairB1_1 hR) hx)

theorem cpt_repAt {u x : List Bool → List Bool} (hu : CPTs u) (hx : CPTs x) :
    CPTs fun s => bflag (repAt (u s) (x s)) := by
  have hl := cpt_flatMapRange cpt_sameVar hu (cpt_pairB2 hu hx)
  exact cpt_bAnd (cpt_bNot (cpt_endAt hu hx)) (cpt_bEmpty hl)

theorem cpt_segHit : CPTs segHit := by
  have hr : CPTs fun z => (unpairB z).1 := cpt_unpairB1
  have h1 : CPTs fun z => (unpairB z).2 := cpt_unpairB2
  have hu := cpt_unpairB1_1 h1
  have h2 := cpt_unpairB2_1 h1
  have hl := cpt_unpairB1_1 h2
  have hx := cpt_unpairB2_1 h2
  exact cpt_bAnd (cpt_eqF (cpt_comp (cpt_restAt hr hx) cpt_headI) hl)
    (cpt_eqF (cpt_comp (cpt_restAt hr hx) cpt_endsU) (cpt_comp (cpt_restAt hu hx) cpt_endsU))

theorem cpt_segAt {u l x : List Bool → List Bool} (hu : CPTs u) (hl : CPTs l) (hx : CPTs x) :
    CPTs fun s => bflag (segAt (u s) (l s) (x s)) :=
  cpt_bNot (cpt_bEmpty (cpt_flatMapRange cpt_segHit hu (cpt_pairB2 hu (cpt_pairB2 hl hx))))

/-! ### Adjacency -/

theorem cpt_crossAt {u v x : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) (hx : CPTs x) :
    CPTs fun s => bflag (crossAt (u s) (v s) (x s)) := by
  have du := cpt_comp hu cpt_div3
  have dv := cpt_comp hv cpt_div3
  have lit := cpt_consFlag (fun _ => true) (cpt_const [true])
    (cpt_consFlag _ (cpt_comp (g := fun r => bflag (isR0 r)) hu cpt_isR0) (cpt_varAt du hx))
  exact cpt_bAnd (cpt_bAnd (cpt_bAnd (cpt_bAnd (cpt_bNot (cpt_comp (g := fun r => bflag (isR2 r)) hu cpt_isR2))
    (cpt_comp (g := fun r => bflag (isR2 r)) hv cpt_isR2)) (cpt_endAt dv hx)) (cpt_repAt du hx)) (cpt_segAt dv lit hx)

theorem cpt_adjAt {u v x : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) (hx : CPTs x) :
    CPTs fun s => bflag (adjAt (u s) (v s) (x s)) := by
  have du := cpt_comp hu cpt_div3
  have dv := cpt_comp hv cpt_div3
  have a := cpt_bOr (cpt_bAnd (cpt_bNot (cpt_comp (g := fun r => bflag (isR2 r)) hu cpt_isR2)) (cpt_bNot (cpt_comp (g := fun r => bflag (isR2 r)) hv cpt_isR2)))
    (cpt_bNot (cpt_endAt du hx))
  have b := cpt_bOr (cpt_crossAt hu hv hx) (cpt_crossAt hv hu hx)
  exact cpt_bIf (cpt_eqF du dv) a b

theorem cpt_entryAt {u v x : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) (hx : CPTs x) :
    CPTs fun s => entryAt (u s) (v s) (x s) :=
  cpt_sel (cpt_adjAt hu hv hx) (cpt_const _) (cpt_const _)

theorem cpt_cell : CPTs cell := by
  have h1 : CPTs fun z => (unpairB z).2 := cpt_unpairB2
  have hi := cpt_unpairB1_1 h1
  have hx := cpt_unpairB2_1 h1
  exact cpt_entryAt hi (cpt_app2 hi (cpt_cons1 true cpt_unpairB1)) hx

/-! ### Rows and the reduction -/

theorem cpt_rowAt : CPTs rowAt := by
  have hu : CPTs fun z => (unpairB z).1 := cpt_unpairB1
  have hx : CPTs fun z => (unpairB z).2 := cpt_unpairB2
  have hc := cpt_iterLen cpt_tail (fun s => by simp) (cpt_cons1 true hu)
    (cpt_comp (g := vertsU) hx cpt_vertsU)
  exact cpt_app2 (cpt_flatMapRange cpt_cell hc cpt_id) (cpt_const _)

theorem cpt_rowsOf : CPTs rowsOf :=
  cpt_flatMapRange cpt_rowAt cpt_vertsU cpt_id

theorem cpt_red : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
    (fun x : List Bool => x) red := by
  have hi := cpt_iterGrow cpt_incB 1 incB_length cpt_itemsU (cpt_const [])
  exact cpt_sel cpt_wfF (cpt_const [])
    (cpt_app2 (cpt_app2 (cpt_app2 (cpt_comp hi cpt_dig) (cpt_const _)) (cpt_const _)) cpt_rowsOf)

end ClustNP
