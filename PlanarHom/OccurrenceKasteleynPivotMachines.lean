import PlanarHom.OccurrenceKasteleynTablePrimitives

/-! NEW reconstruction. Actual finite candidate generation, exclusive-pivot
checks and deterministic first-candidate selection under the literal codecs. -/
namespace PlanarHom.MultiGraph.Kasteleyn
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 theorem fp_allBool : FP BitEncoding.bool.list BitEncoding.bool (fun xs => xs.all id) := by
  have ha := ListPredicateMachines.fp_any BitEncoding.bool Bool.not
    (fp_bool_unary BitEncoding.bool Bool.not)
  exact (ha.comp (fp_bool_unary BitEncoding.bool Bool.not)).congr (fun xs => by
    induction xs with
    | nil => rfl
    | cons b xs ih => cases b <;> simp_all)

 theorem fp_pivotCandidates : FP (tableCode.prod BitEncoding.nat.list) pivotCode.list
    (fun p => pivotCandidates (tableBoundary p.1) p.2) := by
  have hf := fp_fst BitEncoding.nat dartCode
  have he := (fp_snd BitEncoding.nat dartCode).comp (fp_fst BitEncoding.nat BitEncoding.bool)
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.nat dartCode pivotCode _ (hf.pair he)
  have hid := fp_snd tableCode BitEncoding.nat
  have hb := fp_tableBoundary
  have hrow := (hid.pair hb).comp hm
  have hall := ListContextMachines.fp_mapWithContext tableCode BitEncoding.nat pivotCode.list _ hrow
  exact (hall.comp (ListFlattenMachines.fp_flatten pivotCode)).congr (fun p => by
    simp only [Function.comp_apply,pivotCandidates]
    rfl)

 def scanCode : BitEncoding (List RawFace × List ℕ) := tableCode.prod BitEncoding.nat.list

 theorem fp_pivotTest : FP (scanCode.prod pivotCode) BitEncoding.bool
    (fun p => pivotTest (tableBoundary p.1.1) p.1.2 p.2) := by
  let ec := tableCode.prod pivotCode
  have hc := fp_fst ec BitEncoding.nat
  have hg := fp_snd ec BitEncoding.nat
  have ht := hc.comp (fp_fst tableCode pivotCode)
  have hp := hc.comp (fp_snd tableCode pivotCode)
  have hf := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have he := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hrow := (ht.pair hg).comp fp_tableBoundary
  have hinc := (he.pair hrow).comp fp_incidenceParity
  have hnot := hinc.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have heq := (hg.pair hf).comp PfaffianList.fp_nat_eq
  have htest := (heq.pair hnot).comp (fp_bool_gate (fun p => p.1 || p.2))
  have hscan := fp_fst scanCode pivotCode
  have hpiv := fp_snd scanCode pivotCode
  have htable := hscan.comp (fp_fst tableCode BitEncoding.nat.list)
  have hfaces := hscan.comp (fp_snd tableCode BitEncoding.nat.list)
  have hface := hpiv.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hedge := hpiv.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hboundary := (htable.pair hface).comp fp_tableBoundary
  have hparity := (hedge.pair hboundary).comp fp_incidenceParity
  have hmap := ((htable.pair hpiv).pair hfaces).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat BitEncoding.bool _ htest)
  have hall := hmap.comp fp_allBool
  exact ((hparity.pair hall).comp (fp_bool_gate (fun p => p.1 && p.2))).congr
    (fun p => by simp [pivotTest,List.all_map])

 def goodPivots (table : List RawFace) (fs : List ℕ) : List (ℕ × ℕ) :=
   (pivotCandidates (tableBoundary table) fs).filter (pivotTest (tableBoundary table) fs)

 theorem fp_goodPivots : FP scanCode pivotCode.list (fun p => goodPivots p.1 p.2) := by
  exact (((fp_id scanCode).pair fp_pivotCandidates).comp
    (PfaffianList.fp_filterContext scanCode pivotCode _ fp_pivotTest)).congr
      (fun p => by simp only [Function.comp_apply,id_eq,PfaffianList.filterContext_eq,goodPivots])

 theorem head_filter_eq_find {A : Type} (xs : List A) (p : A → Bool) :
    (xs.filter p).head? = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h,ih]

 theorem goodPivots_head (table : List RawFace) (fs : List ℕ) :
    (goodPivots table fs).head? = pickPivot (tableBoundary table) fs :=
  head_filter_eq_find _ _

 theorem fp_eraseFace : FP (BitEncoding.nat.list.prod BitEncoding.nat) BitEncoding.nat.list
    (fun p : List ℕ × ℕ => p.1.erase p.2) := by
  have hx := fp_fst BitEncoding.nat.list BitEncoding.nat
  have hf := fp_snd BitEncoding.nat.list BitEncoding.nat
  have hi := (hf.pair hx).comp GraphComponentMachines.fp_index
  exact ((hx.pair hi).comp (PfaffianList.fp_eraseIndex BitEncoding.nat)).congr
    (fun p => by simp only [Function.comp_apply]; rw [PfaffianList.eraseIndex_eq, ← List.erase_eq_eraseIdx_of_idxOf]; rfl)

end PlanarHom.MultiGraph.Kasteleyn
