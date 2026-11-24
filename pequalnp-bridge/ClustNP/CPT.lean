import ClustNP.Defs
import PEqualNP.Library.SearchHelpers.KSatHard

/-!
# `CV` is polynomial-time computable

Pequalnp's method (`SatVerifierCPT.lean`): the pair is packed with `cpt_pairB`, every
subexpression is a polynomial-time function of the packed string, booleans are flag strings
combined with `sel`. Scanners are finite-state transducers.
-/

namespace ClustNP

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.TwoSat
  PEqualNP.Library.SearchHelpers.Tab.StepW PEqualNP.Library.SearchHelpers.S2D
  PEqualNP.Library.SearchHelpers.KSat.Hard

local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Transducers -/

/-- States of the scanners: boundary, one symbol held, copying (or finished). -/
inductive PS : Type
  | b | h (a : Bool) | c
  deriving DecidableEq, Fintype

def f1D : PS → Bool → PS × Option Bool
  | .b, a => (.c, if a then some true else none)
  | q, _ => (q, none)

theorem f1D_c (l : List Bool) : fstRun f1D (fun _ => none) PS.c l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, f1D, ih]

theorem f1D_run (s : List Bool) : fstRun f1D (fun _ => none) PS.b s = f1 s := by
  cases s with
  | nil => rfl
  | cons a l => cases a <;> simp [f1, fstRun, f1D, f1D_c]

theorem cpt_f1 : CPTs f1 :=
  fst_polyTime _ _ _ f1D (fun _ => none) PS.b (fun s => (f1D_run s).symm)

def trD : Unit → Bool → Unit × Option Bool
  | _, a => ((), if a then some true else none)

theorem trD_run (w : List Bool) : fstRun trD (fun _ => none) () w = trues w := by
  induction w with
  | nil => rfl
  | cons a l ih => cases a <;> simp [fstRun, trD, trues] at ih ⊢ <;> exact ih

theorem cpt_trues : CPTs trues :=
  fst_polyTime _ _ _ trD (fun _ => none) () (fun s => (trD_run s).symm)

def euD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, false => (.b, some true)
  | _, _ => (.b, none)

theorem euD_run : ∀ s : List Bool, fstRun euD (fun _ => none) PS.b s = endsU s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: false :: r => by simp [fstRun, euD, endsU, euD_run r]
  | false :: true :: r => by simp [fstRun, euD, endsU, euD_run r]
  | true :: b :: r => by cases b <;> simp [fstRun, euD, endsU, euD_run r]

theorem cpt_endsU : CPTs endsU :=
  fst_polyTime _ _ _ euD (fun _ => none) PS.b (fun s => (euD_run s).symm)

def drD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, false => (.c, none)
  | .h _, _ => (.b, none)
  | .c, a => (.c, some a)

theorem drD_c (l : List Bool) : fstRun drD (fun _ => none) PS.c l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, drD, ih]

theorem drD_run : ∀ s : List Bool, fstRun drD (fun _ => none) PS.b s = dropRow s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: false :: r => by simp [fstRun, drD, dropRow, drD_c]
  | false :: true :: r => by simp [fstRun, drD, dropRow, drD_run r]
  | true :: b :: r => by cases b <;> simp [fstRun, drD, dropRow, drD_run r]

theorem cpt_dropRow : CPTs dropRow :=
  fst_polyTime _ _ _ drD (fun _ => none) PS.b (fun s => (drD_run s).symm)

def rlD : PS → Bool → PS × Option Bool
  | .b, a => (.h a, none)
  | .h false, false => (.c, none)
  | .h false, true => (.b, some true)
  | .h true, _ => (.b, none)
  | .c, _ => (.c, none)

theorem rlD_c (l : List Bool) : fstRun rlD (fun _ => none) PS.c l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, rlD, ih]

theorem rlD_run : ∀ s : List Bool, fstRun rlD (fun _ => none) PS.b s = rowLenU s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | false :: false :: r => by simp [fstRun, rlD, rowLenU, rlD_c]
  | false :: true :: r => by simp [fstRun, rlD, rowLenU, rlD_run r]
  | true :: b :: r => by cases b <;> simp [fstRun, rlD, rowLenU, rlD_run r]

theorem cpt_rowLenU : CPTs rowLenU :=
  fst_polyTime _ _ _ rlD (fun _ => none) PS.b (fun s => (rlD_run s).symm)

def wfFin : Ph × Option Bool → Option Bool
  | q => if q = (.R, none) then some true else none

theorem wfI_run (l : List Bool) : ∀ q : Ph × Option Bool,
    fstRun (fun q a => (wfD q a, (none : Option Bool))) wfFin q l =
      bflag (decide (l.foldl wfD q = (.R, none))) := by
  induction l with
  | nil => intro q; by_cases h : q = (.R, none) <;> simp [fstRun, wfFin, bflag, h]
  | cons a l ih => intro q; simp only [fstRun, Option.toList_none, List.nil_append, List.foldl_cons]; exact ih _

theorem cpt_wfI : CPTs (fun x => bflag (wfI x)) :=
  fst_polyTime _ _ _ (fun q a => (wfD q a, (none : Option Bool))) wfFin (.kC, none)
    (fun s => (wfI_run s _).symm)

/-! ### Small functions -/

theorem cpt_rowsS : CPTs rowsS := by
  have := cpt_comp cpt_dropI cpt_dropI
  exact this

theorem dropRow_length (s : List Bool) : (dropRow s).length ≤ s.length := by
  induction s using dropRow.induct <;> simp [dropRow] <;> omega

theorem tail_iter (n : ℕ) (l : List Bool) : List.tail^[n] l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, List.drop_tail]

theorem f1_length (s : List Bool) : (f1 s).length ≤ 1 := by
  unfold f1; split_ifs <;> simp

theorem leStep_length (s : List Bool) : (leStep s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := f1_length (unpairB (unpairB s).2).1.tail
  have h4 : (unpairB s).1.tail.tail.length ≤ (unpairB s).1.length := by simp; omega
  have h5 : (unpairB (unpairB s).2).1.tail.tail.length ≤ (unpairB (unpairB s).2).1.length := by
    simp; omega
  unfold leStep
  simp only [sel]
  split_ifs <;> simp only [pairB_length, List.length_nil, List.length_singleton] <;> omega

theorem cpt_leStep : CPTs leStep := by
  have hA : CPTs (fun s => (unpairB s).1) := cpt_unpairB1
  have hR : CPTs (fun s => (unpairB s).2) := cpt_unpairB2
  have hB : CPTs (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hR
  have hF : CPTs (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hR
  have hhA := cpt_hd1 hA
  have hhB := cpt_hd1 hB
  have c0 := cpt_const ([] : List Bool)
  have e1 := cpt_pairB2 c0 (cpt_pairB2 c0 hF)
  have e2 := cpt_pairB2 c0 (cpt_pairB2 c0 (cpt_const [true]))
  have e3 := cpt_pairB2 c0 (cpt_pairB2 c0 c0)
  have fA : CPTs (fun s => f1 (unpairB s).1.tail) := cpt_comp (cpt_tail1 hA) cpt_f1
  have fB : CPTs (fun s => f1 (unpairB (unpairB s).2).1.tail) := cpt_comp (cpt_tail1 hB) cpt_f1
  have q := cpt_sel (cpt_eqF fA fB) fB hF
  have e4 := cpt_pairB2 (cpt_tail1 (cpt_tail1 hA))
    (cpt_pairB2 (cpt_tail1 (cpt_tail1 hB)) q)
  exact cptE (cpt_sel hhA (cpt_sel hhB e1 e2) (cpt_sel hhB e3 e4)) (fun _ => rfl)

theorem cpt_leF {a b : List Bool → List Bool} (ha : CPTs a) (hb : CPTs b) :
    CPTs (fun s => leF (a s) (b s)) := by
  have hit := cpt_iterGrow cpt_leStep 3 leStep_length (cpt_app2 ha hb)
    (cpt_pairB2 ha (cpt_pairB2 hb (cpt_const [true])))
  exact cptE (cpt_unpairB2_1 (cpt_unpairB2_1 hit)) (fun _ => rfl)

theorem cpt_entryS {a b x : List Bool → List Bool} (ha : CPTs a) (hb : CPTs b) (hx : CPTs x) :
    CPTs (fun s => entryS (a s) (b s) (x s)) := by
  have h1 : CPTs (fun s => dropRow^[(a s).length] (rowsS (x s))) :=
    cpt_iterLen cpt_dropRow dropRow_length ha (cpt_comp hx cpt_rowsS)
  have h2 : CPTs (fun s => List.tail^[(true :: a s).length] (b s)) :=
    cpt_iterLen cpt_tail (fun s => by simp) (cpt_cons1 true ha) hb
  have h3 := cpt_iterLen cpt_dropI dropI_length h2 h1
  exact cptE (cpt_comp h3 cpt_headI) (fun _ => rfl)

/-! ### Flags -/

theorem flag_em (F : List Bool) : sel F [true] [] = bflag F.isEmpty := by
  cases F <;> simp [sel, bflag]

theorem sel_ent (us uy e1 e2 : List Bool) :
    sel (List.tail^[us.length] uy) e1 e2 = if us.length < uy.length then e2 else e1 := by
  rw [tail_iter]
  unfold sel
  by_cases h : us.length < uy.length
  · have : uy.drop us.length ≠ [] := by simpa [List.drop_eq_nil_iff] using h
    simp [this, h]
  · have : uy.drop us.length = [] := by simpa [List.drop_eq_nil_iff] using h
    simp [this, h]

theorem covers_flag (us uy x w : List Bool) :
    bflag (covers us uy x w) =
      sel (f1 (List.tail^[us.length] w)) []
        (sel (bflag (decide (us = uy)))
          (sel (leF (sel (List.tail^[us.length] uy) (entryS uy us x) (entryS us uy x))
            (headI (dropI x))) [] [true]) [true]) := by
  rw [sel_ent]
  unfold covers
  generalize (if us.length < uy.length then entryS us uy x else entryS uy us x) = E
  generalize f1 (List.tail^[us.length] w) = P
  generalize leF E (headI (dropI x)) = L
  cases P <;> cases L <;> by_cases h : us = uy <;> simp [sel, bflag, h]

theorem cpt_covers {us uy x w : List Bool → List Bool} (hu : CPTs us) (hy : CPTs uy)
    (hx : CPTs x) (hw : CPTs w) : CPTs (fun s => bflag (covers (us s) (uy s) (x s) (w s))) := by
  have P : CPTs (fun s => f1 (List.tail^[(us s).length] (w s))) :=
    cpt_comp (cpt_iterLen cpt_tail (fun s => by simp) hu hw) cpt_f1
  have lt : CPTs (fun s => List.tail^[(us s).length] (uy s)) :=
    cpt_iterLen cpt_tail (fun s => by simp) hu hy
  have ent := cpt_sel lt (cpt_entryS hy hu hx) (cpt_entryS hu hy hx)
  have lim : CPTs (fun s => headI (dropI (x s))) := cpt_comp (cpt_comp hx cpt_dropI) cpt_headI
  have L := cpt_leF ent lim
  exact cptE (cpt_sel P (cpt_const []) (cpt_sel (cpt_eqF hu hy)
    (cpt_sel L (cpt_const []) (cpt_const [true])) (cpt_const [true])))
    (fun s => (covers_flag _ _ _ _).symm)

theorem cpt_covRow : CPTs covRow := by
  have h2 : CPTs (fun z => (unpairB z).2) := cpt_unpairB2
  have h3 := cpt_unpairB2_1 h2
  exact cpt_covers cpt_unpairB1 (cpt_unpairB1_1 h2) (cpt_unpairB1_1 h3) (cpt_unpairB2_1 h3)

theorem cpt_uncov : CPTs uncov := by
  have hc : CPTs (fun z => endsU (unpairB (unpairB z).2).1) :=
    cpt_comp (cpt_unpairB1_1 cpt_unpairB2) cpt_endsU
  have hl := cpt_flatMapRange cpt_covRow hc cpt_id
  exact cptE (cpt_sel hl (cpt_const [true]) (cpt_const [])) (fun z => flag_em _)

theorem cpt_uncovS : CPTs (fun s => (List.range (endsU (unpairB s).1).length).flatMap
    fun y => uncov (pairB (un y) s)) :=
  cpt_flatMapRange cpt_uncov (cpt_comp cpt_unpairB1 cpt_endsU) cpt_id

theorem cpt_triRow : CPTs triRow := by
  have hu : CPTs (fun z => (unpairB z).1) := cpt_unpairB1
  have hx : CPTs (fun z => (unpairB z).2) := cpt_unpairB2
  have hd : CPTs (fun z => dropRow^[(unpairB z).1.length] (rowsS (unpairB z).2)) :=
    cpt_iterLen cpt_dropRow dropRow_length hu (cpt_comp hx cpt_rowsS)
  have hl := cpt_app2 (cpt_comp hd cpt_rowLenU) (cpt_cons1 true hu)
  have he := cpt_comp hx cpt_endsU
  exact cptE (cpt_sel (cpt_eqF hl he) (cpt_const [true]) (cpt_const [])) (fun z => by
    unfold triRow; cases decide (rowLenU (dropRow^[(unpairB z).1.length] (rowsS (unpairB z).2)) ++
      true :: (unpairB z).1 = endsU (unpairB z).2) <;> simp [sel, bflag])

theorem cpt_triBad : CPTs triBad :=
  cpt_flatMapRange cpt_triRow cpt_endsU cpt_id

theorem cpt_cntS {w : List Bool → List Bool} (hw : CPTs w) : CPTs (fun s => cntS (w s)) := by
  have hi := cpt_iterGrow cpt_incB 1 incB_length (cpt_comp hw cpt_trues) (cpt_const [])
  exact cptE (cpt_app2 (cpt_comp hi cpt_dig) (cpt_const [false, true])) (fun _ => rfl)

theorem flag_CV (a : Bool) (T L U : List Bool) :
    (!(sel (bflag a) [] (sel T (sel L [] (sel U [true] [])) [])).isEmpty) =
      (a && T.isEmpty && !L.isEmpty && U.isEmpty) := by
  cases a <;> cases T <;> cases L <;> cases U <;> simp [sel, bflag]

theorem cpt_CVS : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
    (fun s : List Bool => !(sel (bflag (wfI (unpairB s).1)) []
      (sel (triBad (unpairB s).1) (sel (leF (cntS (unpairB s).2) (headI (unpairB s).1)) []
        (sel ((List.range (endsU (unpairB s).1).length).flatMap
          fun y => uncov (pairB (un y) s)) [true] [])) [])).isEmpty) := by
  have hx : CPTs (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : CPTs (fun s => (unpairB s).2) := cpt_unpairB2
  have F1 : CPTs (fun s => bflag (wfI (unpairB s).1)) := cpt_comp (g := fun x => bflag (wfI x)) hx cpt_wfI
  have T : CPTs (fun s => triBad (unpairB s).1) := cpt_comp hx cpt_triBad
  have hh : CPTs (fun s => headI (unpairB s).1) := cpt_comp hx cpt_headI
  have L := cpt_leF (cpt_cntS hw) hh
  have G := cpt_sel F1 (cpt_const [])
    (cpt_sel T (cpt_sel L (cpt_const []) (cpt_sel cpt_uncovS (cpt_const [true]) (cpt_const [])))
      (cpt_const []))
  exact cpt_comp (g := fun l : List Bool => !l.isEmpty) G cpt_neS

/-- `CV` is polynomial-time computable. -/
theorem cpt_CV : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool CV :=
  cptG (cpt_comp cpt_pairB cpt_CVS) (fun p => by
    obtain ⟨x, w⟩ := p
    simp only [unpairB_pairB]
    rw [flag_CV]
    rfl)

end ClustNP
