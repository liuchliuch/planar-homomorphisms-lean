import PlanarHom.ListDropMachines
import PlanarHom.ListContextMachines
import PlanarHom.ListFilterMachines
import PlanarHom.ListIndexMachines
import PlanarHom.FixedFieldArithmeticMachines

/-! NEW reconstruction. Actual encoded polynomial-time operations used by the
runtime Pfaffian program. Every arithmetic leaf is an existing fixed-field TM2
program and every scan/map is an existing list TM2 compiler. -/

namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines

/-- Binary-index total lookup, including indices larger than the materialized list. -/
def lookup {A : Type} (d : A) (xs : List A) (i : ℕ) : A := xs[i]?.getD d

theorem fp_at {A : Type} (e : BitEncoding A) (d : A) :
    FP (e.list.prod BitEncoding.nat) e (fun p => lookup d p.1 p.2) := by
  have hx := fp_fst e.list BitEncoding.nat
  have hi := fp_snd e.list BitEncoding.nat
  exact (((hi.pair hx).comp (ListDropMachines.fp_drop e d)).comp
    (ListDecompositionMachines.fp_headD e d)).congr (fun p => by
      simp only [lookup, Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop])

def filterContext {C A : Type} (p : C × A → Bool) (c : C) (xs : List A) : List A :=
  ((xs.map (fun a => (c,a))).filter p).map Prod.snd

theorem filterContext_eq {C A : Type} (p : C × A → Bool) (c : C) (xs : List A) :
    filterContext p c xs = xs.filter (fun a => p (c,a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    unfold filterContext at *
    cases h : p (c,a) <;> simp [h, ih]

theorem fp_filterContext {C A : Type} (ec : BitEncoding C) (ea : BitEncoding A)
    (p : C × A → Bool) (hp : FP (ec.prod ea) BitEncoding.bool p) :
    FP (ec.prod ea.list) ea.list (fun q => filterContext p q.1 q.2) := by
  have hm := ListContextMachines.fp_mapWithContext ec ea (ec.prod ea)
    id (fp_id (ec.prod ea))
  exact (hm.comp (ListFilterMachines.fp_filter (ec.prod ea) p hp)).comp
    (ListMapMachines.fp_map (ec.prod ea) ea Prod.snd (fp_snd ec ea))

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Grid (K : Type) := List (List K)
noncomputable def gridEncoding : BitEncoding (Grid K) := (numberFieldEncoding basis).list.list

/-- Out-of-range rows and entries are zero, giving a total function on raw lists. -/
def entry (g : Grid K) (i j : ℕ) : K  := lookup 0 (lookup [] g i) j

theorem fp_entry : FP ((gridEncoding basis).prod (BitEncoding.nat.prod BitEncoding.nat))
    (numberFieldEncoding basis) (fun p => entry p.1 p.2.1 p.2.2) := by
  let e := numberFieldEncoding basis
  have hg := fp_fst e.list.list (BitEncoding.nat.prod BitEncoding.nat)
  have ht := fp_snd e.list.list (BitEncoding.nat.prod BitEncoding.nat)
  have hi := ht.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj := ht.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hr := (hg.pair hi).comp (fp_at e.list [])
  exact (hr.pair hj).comp (fp_at e 0)

/-- One exact Schur entry using six field-arithmetic operations. -/
def updateEntry (g : Grid K) (i j u v : ℕ) : K :=
  entry g u v - entry g i u * entry g j v / entry g i j +
    entry g j u * entry g i v / entry g i j

abbrev UpdateContext (K : Type) := Grid K × (ℕ × ℕ)
noncomputable def updateEncoding : BitEncoding (UpdateContext K) :=
  (gridEncoding basis).prod (BitEncoding.nat.prod BitEncoding.nat)

theorem fp_updateEntry :
    FP ((updateEncoding basis).prod (BitEncoding.nat.prod BitEncoding.nat))
      (numberFieldEncoding basis)
      (fun p => updateEntry p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  let e := numberFieldEncoding basis
  let en := BitEncoding.nat.prod BitEncoding.nat
  let ec := updateEncoding basis
  have hc := fp_fst ec en
  have huv := fp_snd ec en
  have hg := hc.comp (fp_fst e.list.list en)
  have hij := hc.comp (fp_snd e.list.list en)
  have hi := hij.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj := hij.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hu := huv.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hv := huv.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have huv' := (hg.pair (hu.pair hv)).comp (fp_entry basis)
  have hiu := (hg.pair (hi.pair hu)).comp (fp_entry basis)
  have hjv := (hg.pair (hj.pair hv)).comp (fp_entry basis)
  have hju := (hg.pair (hj.pair hu)).comp (fp_entry basis)
  have hiv := (hg.pair (hi.pair hv)).comp (fp_entry basis)
  have hp := (hg.pair (hi.pair hj)).comp (fp_entry basis)
  have hx := ((hiu.pair hjv).comp (FixedFieldArithmetic.fp_multiplication basis)).pair hp
  have hy := ((hju.pair hiv).comp (FixedFieldArithmetic.fp_multiplication basis)).pair hp
  have hx' := hx.comp (FixedFieldArithmetic.fp_division basis)
  have hy' := hy.comp (FixedFieldArithmetic.fp_division basis)
  exact (((huv'.pair hx').comp (FixedFieldArithmetic.fp_subtraction basis)).pair hy').comp
    (FixedFieldArithmetic.fp_addition basis)

/-- Materialize every entry; rows keep their original length even on ragged input. -/
def updateRow (c : UpdateContext K) (p : List K × ℕ) : List K :=
  p.1.zipIdx.map (fun q => updateEntry c.1 c.2.1 c.2.2 p.2 q.2)

theorem fp_updateRow :
    FP ((updateEncoding basis).prod ((numberFieldEncoding basis).list.prod BitEncoding.nat))
      (numberFieldEncoding basis).list (fun p => updateRow p.1 p.2) := by
  let e := numberFieldEncoding basis
  let ec := updateEncoding basis
  let er := e.list.prod BitEncoding.nat
  let ei := e.prod BitEncoding.nat
  have hc := fp_fst ec er
  have hr := fp_snd ec er
  have hu := hr.comp (fp_snd e.list BitEncoding.nat)
  have hs := (hr.comp (fp_fst e.list BitEncoding.nat)).comp (ListIndexMachines.fp_zipIdx e)
  have hct := fp_fst (ec.prod BitEncoding.nat) ei
  have hit := fp_snd (ec.prod BitEncoding.nat) ei
  have hcc := hct.comp (fp_fst ec BitEncoding.nat)
  have huu := hct.comp (fp_snd ec BitEncoding.nat)
  have hv := hit.comp (fp_snd e BitEncoding.nat)
  have hb := (hcc.pair (huu.pair hv)).comp (fp_updateEntry basis)
  exact ((hc.pair hu).pair hs).comp
    (ListContextMachines.fp_mapWithContext (ec.prod BitEncoding.nat) ei e _ hb)

def updateGrid (g : Grid K) (i j : ℕ) : Grid K :=
  g.zipIdx.map (fun p => updateRow (g,(i,j)) p)

theorem fp_updateGrid :
    FP (updateEncoding basis) (gridEncoding basis)
      (fun p => updateGrid p.1 p.2.1 p.2.2) := by
  let e := numberFieldEncoding basis
  have hg := fp_fst e.list.list (BitEncoding.nat.prod BitEncoding.nat)
  have hz := hg.comp (ListIndexMachines.fp_zipIdx e.list)
  exact ((fp_id (updateEncoding basis)).pair hz).comp
    (ListContextMachines.fp_mapWithContext (updateEncoding basis)
      (e.list.prod BitEncoding.nat) e.list _ (fp_updateRow basis))

@[simp] theorem updateRow_length (c : UpdateContext K) (p : List K × ℕ) :
    (updateRow c p).length = p.1.length := by simp [updateRow]

@[simp] theorem updateGrid_length (g : Grid K) (i j : ℕ) :
    (updateGrid g i j).length = g.length := by simp [updateGrid]

end PlanarHom.PfaffianList
