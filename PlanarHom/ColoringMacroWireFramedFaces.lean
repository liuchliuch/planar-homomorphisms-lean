import PlanarHom.FinitePermutationCycleCertificate
import PlanarHom.ColoringMacroWireFramedFaceCheckNextbound
import PlanarHom.ColoringMacroWireFramedFaceCheckPrevbound
import PlanarHom.ColoringMacroWireFramedFaceCheckLabelbound
import PlanarHom.ColoringMacroWireFramedFaceCheckRootbound
import PlanarHom.ColoringMacroWireFramedFaceCheckGapbound
import PlanarHom.ColoringMacroWireFramedFaceCheckPrevNextValue
import PlanarHom.ColoringMacroWireFramedFaceCheckNextPrevValue
import PlanarHom.ColoringMacroWireFramedFaceCheckRootLabelValue
import PlanarHom.ColoringMacroWireFramedFaceCheckStepLabelValue
import PlanarHom.ColoringMacroWireFramedFaceCheckZeroRootValue
import PlanarHom.ColoringMacroWireFramedFaceCheckStepRankValue

/-! Exact coordinate-derived macro face certificate. Source SHA256 9f8f450a0c2072e6c18868372340fe80a1e449eb68dd42943cf1c7e9f11ee953. -/
namespace PlanarHom.ColoringMacroFaces.WireFramed
open FinitePermutationCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def next (i : Fin 2646) : Fin 2646 := ⟨nextValue i.val,nextBound i⟩
def prev (i : Fin 2646) : Fin 2646 := ⟨prevValue i.val,prevBound i⟩
def label (i : Fin 2646) : Fin 791 := ⟨labelValue i.val,labelBound i⟩
def root (i : Fin 791) : Fin 2646 := ⟨rootValue i.val,rootBound i⟩
def gap (i : Fin 10) : Fin 2646 := ⟨gapValue i.val,gapBound i⟩
theorem prev_next : ∀ i : Fin 2646,prev (next i)=i := fun i => Fin.ext (prev_next_value i)
theorem next_prev : ∀ i : Fin 2646,next (prev i)=i := fun i => Fin.ext (next_prev_value i)
def permutation : Equiv.Perm (Fin 2646) := ⟨next,prev,prev_next,next_prev⟩
def rank (i : Fin 2646) := rankValue i.val
theorem root_label : ∀ i : Fin 791,label (root i)=i := fun i => Fin.ext (root_label_value i)
theorem step_label : ∀ i : Fin 2646,label (permutation i)=label i := fun i => Fin.ext (step_label_value i)
theorem zero_root : ∀ i : Fin 2646,rank i=0 → i=root (label i) := fun i h => Fin.ext (zero_root_value i h)
theorem step_rank : ∀ i : Fin 2646,0<rank i → rank (permutation i)+1=rank i := step_rank_value
def certificate : LabelCertificate permutation (Fin 791) := ⟨label,root,rank,root_label,step_label,zero_root,step_rank⟩
theorem cycle_count : count permutation=791 := by simpa using certificate.count
theorem euler : 534+count permutation=1323+2 := by rw [cycle_count]
theorem gap_outer : ∀ i : Fin 10,label (gap i)=790 := by decide +kernel
theorem gap_rank_strictMono : StrictMono (fun i : Fin 10 => rank (gap i)) := by decide +kernel
theorem gap_zero_root : gap 0=root 790 := by decide +kernel
theorem outer_predecessor : ∀ i : Fin 9, permutation (gap i.succ)=gap i.castSucc := by decide +kernel
theorem outer_closing : permutation (gap 0)=gap (Fin.last 9) := by decide +kernel
theorem all_gaps_sameCycle (i j : Fin 10) : permutation.SameCycle (gap i) (gap j) :=
  (certificate.sameCycle_iff _ _).mpr ((gap_outer i).trans (gap_outer j).symm)
end PlanarHom.ColoringMacroFaces.WireFramed
