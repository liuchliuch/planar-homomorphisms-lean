import PlanarHom.FinitePermutationCycleCertificate
import PlanarHom.ColoringMacroTestFramedFaceCheckNextbound
import PlanarHom.ColoringMacroTestFramedFaceCheckPrevbound
import PlanarHom.ColoringMacroTestFramedFaceCheckLabelbound
import PlanarHom.ColoringMacroTestFramedFaceCheckRootbound
import PlanarHom.ColoringMacroTestFramedFaceCheckGapbound
import PlanarHom.ColoringMacroTestFramedFaceCheckPrevNextValue
import PlanarHom.ColoringMacroTestFramedFaceCheckNextPrevValue
import PlanarHom.ColoringMacroTestFramedFaceCheckRootLabelValue
import PlanarHom.ColoringMacroTestFramedFaceCheckStepLabelValue
import PlanarHom.ColoringMacroTestFramedFaceCheckZeroRootValue
import PlanarHom.ColoringMacroTestFramedFaceCheckStepRankValue

/-! Exact coordinate-derived macro face certificate. Source SHA256 30f6c194674ffe96c11fdf8a27528d11c7be6db93d1bfab9b9220b3ceae58ca6. -/
namespace PlanarHom.ColoringMacroFaces.TestFramed
open FinitePermutationCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def next (i : Fin 570) : Fin 570 := ⟨nextValue i.val,nextBound i⟩
def prev (i : Fin 570) : Fin 570 := ⟨prevValue i.val,prevBound i⟩
def label (i : Fin 570) : Fin 169 := ⟨labelValue i.val,labelBound i⟩
def root (i : Fin 169) : Fin 570 := ⟨rootValue i.val,rootBound i⟩
def gap (i : Fin 13) : Fin 570 := ⟨gapValue i.val,gapBound i⟩
theorem prev_next : ∀ i : Fin 570,prev (next i)=i := fun i => Fin.ext (prev_next_value i)
theorem next_prev : ∀ i : Fin 570,next (prev i)=i := fun i => Fin.ext (next_prev_value i)
def permutation : Equiv.Perm (Fin 570) := ⟨next,prev,prev_next,next_prev⟩
def rank (i : Fin 570) := rankValue i.val
theorem root_label : ∀ i : Fin 169,label (root i)=i := fun i => Fin.ext (root_label_value i)
theorem step_label : ∀ i : Fin 570,label (permutation i)=label i := fun i => Fin.ext (step_label_value i)
theorem zero_root : ∀ i : Fin 570,rank i=0 → i=root (label i) := fun i h => Fin.ext (zero_root_value i h)
theorem step_rank : ∀ i : Fin 570,0<rank i → rank (permutation i)+1=rank i := step_rank_value
def certificate : LabelCertificate permutation (Fin 169) := ⟨label,root,rank,root_label,step_label,zero_root,step_rank⟩
theorem cycle_count : count permutation=169 := by simpa using certificate.count
theorem euler : 118+count permutation=285+2 := by rw [cycle_count]
theorem gap_outer : ∀ i : Fin 13,label (gap i)=168 := by decide +kernel
theorem gap_rank_strictMono : StrictMono (fun i : Fin 13 => rank (gap i)) := by decide +kernel
theorem gap_zero_root : gap 0=root 168 := by decide +kernel
theorem outer_predecessor : ∀ i : Fin 12, permutation (gap i.succ)=gap i.castSucc := by decide +kernel
theorem outer_closing : permutation (gap 0)=gap (Fin.last 12) := by decide +kernel
theorem all_gaps_sameCycle (i j : Fin 13) : permutation.SameCycle (gap i) (gap j) :=
  (certificate.sameCycle_iff _ _).mpr ((gap_outer i).trans (gap_outer j).symm)
end PlanarHom.ColoringMacroFaces.TestFramed
