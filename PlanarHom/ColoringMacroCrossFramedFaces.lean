import PlanarHom.FinitePermutationCycleCertificate
import PlanarHom.ColoringMacroCrossFramedFaceCheckNextbound
import PlanarHom.ColoringMacroCrossFramedFaceCheckPrevbound
import PlanarHom.ColoringMacroCrossFramedFaceCheckLabelbound
import PlanarHom.ColoringMacroCrossFramedFaceCheckRootbound
import PlanarHom.ColoringMacroCrossFramedFaceCheckGapbound
import PlanarHom.ColoringMacroCrossFramedFaceCheckPrevNextValue
import PlanarHom.ColoringMacroCrossFramedFaceCheckNextPrevValue
import PlanarHom.ColoringMacroCrossFramedFaceCheckRootLabelValue
import PlanarHom.ColoringMacroCrossFramedFaceCheckStepLabelValue
import PlanarHom.ColoringMacroCrossFramedFaceCheckZeroRootValue
import PlanarHom.ColoringMacroCrossFramedFaceCheckStepRankValue

/-! Exact coordinate-derived macro face certificate. Source SHA256 065cd8487b1ea70849f99498352f97bb5c8fa6510b6215ec46f252b38a04b6e7. -/
namespace PlanarHom.ColoringMacroFaces.CrossFramed
open FinitePermutationCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def next (i : Fin 6336) : Fin 6336 := ⟨nextValue i.val,nextBound i⟩
def prev (i : Fin 6336) : Fin 6336 := ⟨prevValue i.val,prevBound i⟩
def label (i : Fin 6336) : Fin 1896 := ⟨labelValue i.val,labelBound i⟩
def root (i : Fin 1896) : Fin 6336 := ⟨rootValue i.val,rootBound i⟩
def gap (i : Fin 16) : Fin 6336 := ⟨gapValue i.val,gapBound i⟩
theorem prev_next : ∀ i : Fin 6336,prev (next i)=i := fun i => Fin.ext (prev_next_value i)
theorem next_prev : ∀ i : Fin 6336,next (prev i)=i := fun i => Fin.ext (next_prev_value i)
def permutation : Equiv.Perm (Fin 6336) := ⟨next,prev,prev_next,next_prev⟩
def rank (i : Fin 6336) := rankValue i.val
theorem root_label : ∀ i : Fin 1896,label (root i)=i := fun i => Fin.ext (root_label_value i)
theorem step_label : ∀ i : Fin 6336,label (permutation i)=label i := fun i => Fin.ext (step_label_value i)
theorem zero_root : ∀ i : Fin 6336,rank i=0 → i=root (label i) := fun i h => Fin.ext (zero_root_value i h)
theorem step_rank : ∀ i : Fin 6336,0<rank i → rank (permutation i)+1=rank i := step_rank_value
def certificate : LabelCertificate permutation (Fin 1896) := ⟨label,root,rank,root_label,step_label,zero_root,step_rank⟩
theorem cycle_count : count permutation=1896 := by simpa using certificate.count
theorem euler : 1274+count permutation=3168+2 := by rw [cycle_count]
theorem gap_outer : ∀ i : Fin 16,label (gap i)=1895 := by decide +kernel
theorem gap_rank_strictMono : StrictMono (fun i : Fin 16 => rank (gap i)) := by decide +kernel
theorem gap_zero_root : gap 0=root 1895 := by decide +kernel
theorem outer_predecessor : ∀ i : Fin 15, permutation (gap i.succ)=gap i.castSucc := by decide +kernel
theorem outer_closing : permutation (gap 0)=gap (Fin.last 15) := by decide +kernel
theorem all_gaps_sameCycle (i j : Fin 16) : permutation.SameCycle (gap i) (gap j) :=
  (certificate.sameCycle_iff _ _).mpr ((gap_outer i).trans (gap_outer j).symm)
end PlanarHom.ColoringMacroFaces.CrossFramed
