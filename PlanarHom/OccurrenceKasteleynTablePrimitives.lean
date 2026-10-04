import PlanarHom.OccurrenceKasteleynPeelingSemantics
import PlanarHom.OccurrenceOrientationLogMachines
import PlanarHom.GraphComponentMachines

/-! NEW reconstruction: concrete polynomial-time codecs, boundary lookups,
parity folds and candidate scans for the finite materialized face table. -/
namespace PlanarHom.MultiGraph.Kasteleyn
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 def dartCode : BitEncoding (Dart ℕ) := BitEncoding.nat.prod BitEncoding.bool
 def faceCode : BitEncoding RawFace := BitEncoding.nat.prod dartCode.list
 def tableCode : BitEncoding (List RawFace) := faceCode.list
 def pivotCode : BitEncoding (ℕ × ℕ) := BitEncoding.nat.prod BitEncoding.nat

 theorem fp_bodd : FP BitEncoding.nat BitEncoding.bool Nat.bodd := by
  have hd := ((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat 2)).comp
    BinaryArithmetic.fp_division
  have he := (hd.comp (fp_snd BitEncoding.nat BitEncoding.nat)).comp RationalCircuits.fp_nat_isZero
  exact (he.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun n => by
    simp only [Function.comp_apply,id_eq,Nat.mod_two_of_bodd]
    cases n.bodd <;> rfl)

 theorem fp_faceTarget : FP dartCode.list BitEncoding.bool faceTarget := by
  exact ((ListCodecMachines.fp_length dartCode).comp fp_bodd).comp
    (fp_bool_unary BitEncoding.bool Bool.not)

 theorem incidenceParity_eq_count (e : ℕ) (ds : List (Dart ℕ)) :
    incidenceParity e ds = ((ds.map Prod.fst).count e).bodd := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    by_cases h : a.1=e <;> simp [incidenceParity,ih,h,Nat.bodd_succ]

 theorem fp_incidenceParity : FP (BitEncoding.nat.prod dartCode.list) BitEncoding.bool
    (fun p => incidenceParity p.1 p.2) := by
  have he := fp_fst BitEncoding.nat dartCode.list
  have hs := (fp_snd BitEncoding.nat dartCode.list).comp
    (ListMapMachines.fp_map dartCode BitEncoding.nat Prod.fst (fp_fst BitEncoding.nat BitEncoding.bool))
  exact (((hs.pair he).comp PfaffianList.fp_occurrenceCount).comp fp_bodd).congr
    (fun p => (incidenceParity_eq_count p.1 p.2).symm)

 def parity (xs : List Bool) : Bool := xs.foldl Bool.xor false

 theorem fp_parity : FP BitEncoding.bool.list BitEncoding.bool parity := by
  have hf := ListFoldMachines.fp_foldl BitEncoding.bool BitEncoding.bool Bool.xor
    (fp_bool_gate (fun p => p.1 ^^ p.2)) 1 (fun b xs i hi => by simp [BitEncoding.bool])
  exact ((fp_const BitEncoding.bool.list BitEncoding.bool false).pair (fp_id BitEncoding.bool.list)).comp hf

 theorem fold_xor {A : Type} (f : A → Bool) (xs : List A) (b : Bool) :
    (xs.map f).foldl Bool.xor b = (b ^^ (xs.map f).foldl Bool.xor false) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih (b ^^ f a),ih (false ^^ f a)]
    simp [Bool.xor_assoc]

 theorem boundaryParity_eq_parity (log : List ℕ) (ds : List (Dart ℕ)) :
    boundaryParity (logOrientation log) ds =
      parity (ds.map (fun a => logOrientation log a.1 ^^ a.2)) := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [boundaryParity,List.map_cons,parity,List.foldl_cons]
    rw [fold_xor]
    simpa [parity] using congrArg (fun b => (logOrientation log a.1 ^^ a.2) ^^ b) ih

 theorem fp_boundaryParity : FP (logCode.prod dartCode.list) BitEncoding.bool
    (fun p => boundaryParity (logOrientation p.1) p.2) := by
  have hl := fp_fst logCode dartCode
  have ha := fp_snd logCode dartCode
  have he := ha.comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hb := ha.comp (fp_snd BitEncoding.nat BitEncoding.bool)
  have ho := (hl.pair he).comp fp_logOrientation
  have hx := (ho.pair hb).comp (fp_bool_gate (fun p => p.1 ^^ p.2))
  exact ((ListContextMachines.fp_mapWithContext logCode dartCode BitEncoding.bool _ hx).comp fp_parity).congr
    (fun p => (boundaryParity_eq_parity p.1 p.2).symm)

 def selectedRows (p : List RawFace × ℕ) : List RawFace :=
    p.1.filter (fun row => decide (row.1 = p.2))

 theorem tableBoundary_eq_selectedRows (p : List RawFace × ℕ) :
    tableBoundary p.1 p.2 = ((selectedRows p).headD (0,[])).2 := by
  rcases p with ⟨table,f⟩
  induction table with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨label,ds⟩
    by_cases h : f=label
    · simp [tableBoundary,selectedRows,List.lookup_cons,h,Bool.beq_eq_decide_eq]
    · simp [tableBoundary,selectedRows,List.lookup_cons,h,Ne.symm h,Bool.beq_eq_decide_eq] at ih ⊢
      exact ih

 theorem fp_tableBoundary : FP (tableCode.prod BitEncoding.nat) dartCode.list
    (fun p => tableBoundary p.1 p.2) := by
  have hf := fp_fst BitEncoding.nat faceCode
  have hr := (fp_snd BitEncoding.nat faceCode).comp (fp_fst BitEncoding.nat dartCode.list)
  have heq := (hr.pair hf).comp PfaffianList.fp_nat_eq
  have ht := fp_fst tableCode BitEncoding.nat
  have hi := fp_snd tableCode BitEncoding.nat
  have hsel := (hi.pair ht).comp (PfaffianList.fp_filterContext BitEncoding.nat faceCode _ heq)
  have hhead := hsel.comp (ListDecompositionMachines.fp_headD faceCode (0,[]))
  exact (hhead.comp (fp_snd BitEncoding.nat dartCode.list)).congr (fun p => by
    rw [tableBoundary_eq_selectedRows]
    simp [Function.comp_apply,PfaffianList.filterContext_eq,selectedRows])

end PlanarHom.MultiGraph.Kasteleyn
