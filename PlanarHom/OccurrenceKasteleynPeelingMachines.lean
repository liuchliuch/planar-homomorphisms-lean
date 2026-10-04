import PlanarHom.OccurrenceKasteleynOrientationRuntimeBounds
import PlanarHom.RestrictedIterationMachine

/-! NEW reconstruction. The exact materialized table-to-orientation-log function
is encoded FP, including malformed inputs. The real finite scan, bounded forward
loop, stack and reverse repair fold are all compiled; no orientation solver,
peeling order or geometric extraction is assumed as a computational primitive. -/
noncomputable section
namespace PlanarHom.MultiGraph.Kasteleyn
open Complexity PairProjectionMachines MachineComposition Polynomial

 def preparedOrientationCode : BitEncoding (List RawFace) :=
  (BitEncoding.unaryNat.prod orientationStateCode).retract
    (fun table => (table.length,initialOrientationState table))
    (fun p => p.2.1) (fun _ => rfl)

 theorem fp_prepareOrientation : FP tableCode preparedOrientationCode id := by
  exact ((ListUnaryLengthMachine.fp_length faceCode).pair fp_initialOrientationState).transportOutput
    (fun _ => rfl)

 theorem fp_peelState : FP tableCode orientationStateCode peelState := by
  obtain ⟨body⟩ := fp_peelStep
  have hbound (table : List RawFace) (i : ℕ) (hi : i ≤ table.length) :
      (orientationStateCode.encode (peelStep^[i] (initialOrientationState table))).length ≤
        orientationLoopPolynomial.eval (preparedOrientationCode.encode table).length := by
    apply (orientation_loop_size table i hi).trans
    apply natPolynomial_monotone
    simp only [preparedOrientationCode,BitEncoding.retract,BitEncoding.prod_length,
      orientationStateCode,initialOrientationState]
    omega
  have hlo : FP preparedOrientationCode orientationStateCode peelState :=
    ⟨BoundedIterationMachine.computerOn preparedOrientationCode orientationStateCode peelStep
      List.length initialOrientationState (fun _ => rfl) body orientationLoopPolynomial hbound⟩
  exact fp_prepareOrientation.comp hlo

 theorem fp_repairFold : FP ((tableCode.prod logCode).prod pivotCode.list) logCode
    (fun p => p.2.foldl (repairLog p.1.1) p.1.2) := by
  have hf := ListFoldMachines.fp_foldl pivotCode (tableCode.prod logCode) repairState
    fp_repairState (C 20*(X+1)^2) (fun s ps i hi => repair_fold_size s ps i)
  exact (hf.comp (fp_snd tableCode logCode)).congr (fun p => by
    rcases p with ⟨⟨table,log⟩,ps⟩
    simp only [Function.comp_apply,repairState_foldl])

 theorem fp_computeOrientationIterative : FP tableCode logCode computeOrientationIterative := by
  have hs := fp_peelState.comp (fp_snd tableCode (BitEncoding.nat.list.prod pivotCode.list))
  have hstack := hs.comp (fp_snd BitEncoding.nat.list pivotCode.list)
  have hinit := (fp_id tableCode).pair (fp_const tableCode logCode [])
  exact (hinit.pair hstack).comp fp_repairFold

/-- Unconditional actual machine theorem for the original finite-table solver. -/
 theorem fp_computeOrientation : FP tableCode logCode computeOrientation :=
  fp_computeOrientationIterative.congr computeOrientationIterative_eq_computeOrientation

/-- The runtime and the already proved geometric-dual correctness coexist for
the very same program. No face-system promise enters the FP component. -/
 theorem certified_computeOrientation : FP tableCode logCode computeOrientation ∧
    ∀ (D : DualIncidence ℕ ℕ) (boundary : Boundaries ℕ ℕ), D.Compatible boundary →
      ∀ (root : ℕ) (fs : List ℕ), (∀ f ∈ fs, Relation.ReflTransGen D.Adj root f) →
      fs.Nodup → root ∉ fs → ∀ f ∈ fs,
      FaceOdd (logOrientation (computeOrientation (faceTable boundary fs))) (boundary f) :=
  ⟨fp_computeOrientation,fun D boundary hc root fs hconn hn hr =>
    computeOrientation_faceOdd D boundary hc root fs hconn hn hr⟩

end PlanarHom.MultiGraph.Kasteleyn
