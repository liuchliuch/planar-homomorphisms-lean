import PlanarHom.OccurrenceKasteleynPivotMachines
import PlanarHom.OccurrenceKasteleynOrientationIteration

/-! NEW reconstruction. Concrete FP forward-peeling and reverse-repair steps
of the exact table orientation program, without promises on raw input. -/
namespace PlanarHom.MultiGraph.Kasteleyn
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 def orientationStateCode : BitEncoding OrientationState :=
   tableCode.prod (BitEncoding.nat.list.prod pivotCode.list)

 theorem peelStep_eq (s : OrientationState) :
    peelStep s = if goodPivots s.1 s.2.1 = [] then (s.1,([],s.2.2)) else
      let p := (goodPivots s.1 s.2.1).headD (0,0)
      (s.1,(s.2.1.erase p.1,p::s.2.2)) := by
  have h := goodPivots_head s.1 s.2.1
  cases he : goodPivots s.1 s.2.1 with
  | nil => simp only [he,List.head?_nil] at h; simp [peelStep,← h]
  | cons p ps => simp only [he,List.head?_cons] at h; simp [peelStep,← h]

 theorem fp_peelStep : FP orientationStateCode orientationStateCode peelStep := by
  let et := BitEncoding.nat.list.prod pivotCode.list
  have ht := fp_fst tableCode et
  have hs := fp_snd tableCode et
  have hf := hs.comp (fp_fst BitEncoding.nat.list pivotCode.list)
  have hp := hs.comp (fp_snd BitEncoding.nat.list pivotCode.list)
  have hgood := (ht.pair hf).comp fp_goodPivots
  have hchoice := hgood.comp (ListDecompositionMachines.fp_headD pivotCode (0,0))
  have hface := hchoice.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have herase := (hf.pair hface).comp fp_eraseFace
  have hpush := (hchoice.pair hp).comp (ListMutationMachines.fp_cons pivotCode)
  have hnext := ht.pair (herase.pair hpush)
  have hstop := ht.pair ((fp_const orientationStateCode BitEncoding.nat.list []).pair hp)
  have hz := (hgood.comp (ListCodecMachines.fp_length pivotCode)).comp RationalCircuits.fp_nat_isZero
  have hz' : FP orientationStateCode BitEncoding.bool (fun s => decide (goodPivots s.1 s.2.1 = [])) :=
    hz.congr (fun _ => by simp)
  exact (hz'.ite hstop hnext).congr (fun s => (peelStep_eq s).symm)

 theorem fp_initialOrientationState : FP tableCode orientationStateCode initialOrientationState := by
  have hf := ListMapMachines.fp_map faceCode BitEncoding.nat Prod.fst
    (fp_fst BitEncoding.nat dartCode.list)
  exact (fp_id tableCode).pair (hf.pair (fp_const tableCode pivotCode.list []))

 theorem fp_repairLog : FP ((tableCode.prod logCode).prod pivotCode) logCode
    (fun p => repairLog p.1.1 p.1.2 p.2) := by
  let ec := tableCode.prod logCode
  have hc := fp_fst ec pivotCode
  have hp := fp_snd ec pivotCode
  have ht := hc.comp (fp_fst tableCode logCode)
  have hl := hc.comp (fp_snd tableCode logCode)
  have hf := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have he := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hrow := (ht.pair hf).comp fp_tableBoundary
  have hpar := (hl.pair hrow).comp fp_boundaryParity
  have htarget := hrow.comp fp_faceTarget
  have heq := (hpar.pair htarget).comp (fp_bool_gate (fun p => p.1 == p.2))
  have heq' : FP (ec.prod pivotCode) BitEncoding.bool
      (fun p => decide (boundaryParity (logOrientation p.1.2) (tableBoundary p.1.1 p.2.1) =
        faceTarget (tableBoundary p.1.1 p.2.1))) := heq.congr (fun _ => by simp [Bool.beq_eq_decide_eq])
  have hpush := (he.pair hl).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  exact heq'.ite hl hpush

 def repairState (s : List RawFace × List ℕ) (p : RawPivot) : List RawFace × List ℕ :=
   (s.1,repairLog s.1 s.2 p)

 theorem fp_repairState : FP ((tableCode.prod logCode).prod pivotCode) (tableCode.prod logCode)
    (fun p => repairState p.1 p.2) := by
  have ht := (fp_fst (tableCode.prod logCode) pivotCode).comp (fp_fst tableCode logCode)
  exact ht.pair fp_repairLog

end PlanarHom.MultiGraph.Kasteleyn
