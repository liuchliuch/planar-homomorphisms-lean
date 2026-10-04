import PlanarHom.FinitePermutationCycleCertificate
import PlanarHom.ColoringMacroFanFramedFaceCheckNextbound
import PlanarHom.ColoringMacroFanFramedFaceCheckPrevbound
import PlanarHom.ColoringMacroFanFramedFaceCheckLabelbound
import PlanarHom.ColoringMacroFanFramedFaceCheckRootbound
import PlanarHom.ColoringMacroFanFramedFaceCheckGapbound
import PlanarHom.ColoringMacroFanFramedFaceCheckPrevNextValue
import PlanarHom.ColoringMacroFanFramedFaceCheckNextPrevValue
import PlanarHom.ColoringMacroFanFramedFaceCheckRootLabelValue
import PlanarHom.ColoringMacroFanFramedFaceCheckStepLabelValue
import PlanarHom.ColoringMacroFanFramedFaceCheckZeroRootValue
import PlanarHom.ColoringMacroFanFramedFaceCheckStepRankValue

/-! Exact coordinate-derived macro face certificate. Source SHA256 88127d52343501533be1800170103e1e71290e15ca4540e9b8f364fb3278bf7f. -/
namespace PlanarHom.ColoringMacroFaces.FanFramed
open FinitePermutationCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def next (i : Fin 5264) : Fin 5264 := ⟨nextValue i.val,nextBound i⟩
def prev (i : Fin 5264) : Fin 5264 := ⟨prevValue i.val,prevBound i⟩
def label (i : Fin 5264) : Fin 1576 := ⟨labelValue i.val,labelBound i⟩
def root (i : Fin 1576) : Fin 5264 := ⟨rootValue i.val,rootBound i⟩
def gap (i : Fin 13) : Fin 5264 := ⟨gapValue i.val,gapBound i⟩
theorem prev_next : ∀ i : Fin 5264,prev (next i)=i := fun i => Fin.ext (prev_next_value i)
theorem next_prev : ∀ i : Fin 5264,next (prev i)=i := fun i => Fin.ext (next_prev_value i)
def permutation : Equiv.Perm (Fin 5264) := ⟨next,prev,prev_next,next_prev⟩
def rank (i : Fin 5264) := rankValue i.val
theorem root_label : ∀ i : Fin 1576,label (root i)=i := fun i => Fin.ext (root_label_value i)
theorem step_label : ∀ i : Fin 5264,label (permutation i)=label i := fun i => Fin.ext (step_label_value i)
theorem zero_root : ∀ i : Fin 5264,rank i=0 → i=root (label i) := fun i h => Fin.ext (zero_root_value i h)
theorem step_rank : ∀ i : Fin 5264,0<rank i → rank (permutation i)+1=rank i := step_rank_value
def certificate : LabelCertificate permutation (Fin 1576) := ⟨label,root,rank,root_label,step_label,zero_root,step_rank⟩
theorem cycle_count : count permutation=1576 := by simpa using certificate.count
theorem euler : 1058+count permutation=2632+2 := by rw [cycle_count]
theorem gap_outer : ∀ i : Fin 13,label (gap i)=1575 := by decide +kernel
theorem gap_rank_strictMono : StrictMono (fun i : Fin 13 => rank (gap i)) := by decide +kernel
theorem gap_zero_root : gap 0=root 1575 := by decide +kernel
theorem outer_predecessor : ∀ i : Fin 12, permutation (gap i.succ)=gap i.castSucc := by decide +kernel
theorem outer_closing : permutation (gap 0)=gap (Fin.last 12) := by decide +kernel
theorem all_gaps_sameCycle (i j : Fin 13) : permutation.SameCycle (gap i) (gap j) :=
  (certificate.sameCycle_iff _ _).mpr ((gap_outer i).trans (gap_outer j).symm)
end PlanarHom.ColoringMacroFaces.FanFramed
