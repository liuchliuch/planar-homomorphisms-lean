import PlanarHom.ColoringFramedBoundaryClassification
import PlanarHom.ColoringFramedPrivateRows
import PlanarHom.ColoringFramedFinalMarkers
import PlanarHom.FaceSpliceRowReflectionAny

/-! The actual canonical augmented canvas rotation has exactly the face
permutation produced by the finite closing-arrow splice program. -/
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem finalPairs_mem_iff_input (f : NumericFormula) (hf : NumericValid f) (p : Dart f×Dart f) :
    p∈finalPairs f hf ↔ ∃x : InputIndex f,p=(oldMarker f hf x.1 x.2,newMarker f x.1 x.2) := by
  rw [finalPairs_mem]
  constructor
  · rintro ⟨i,hi⟩
    rw [cellPairs_eq_finRange] at hi
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hi
    exact ⟨⟨i,j⟩,hj.symm⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    refine ⟨i,?_⟩
    rw [cellPairs_eq_finRange]
    exact List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩

 theorem fullRows_face_eq_finalFace (f : NumericFormula) (hf : NumericValid f) :
    (fullRows f).facePerm=finalFace f hf := by
  rw [finalFace_eq_applyPairSplices]
  apply face_eq_splices_of_rows_any (fullRows f) (baseFace f) (finalPairs f hf)
    (finalPairs_markers_nodup f hf)
  · intro p hp
    obtain ⟨x,rfl⟩ := (finalPairs_mem_iff_input f hf p).mp hp
    exact (oldMarker_reverse_host f hf x).trans (newMarker_reverse_host f x).symm
  · intro p hp q hq he
    obtain ⟨x,rfl⟩ := (finalPairs_mem_iff_input f hf p).mp hp
    obtain ⟨y,rfl⟩ := (finalPairs_mem_iff_input f hf q).mp hq
    rw [oldMarker_reverse_host,oldMarker_reverse_host] at he
    have hxy := inputTriple_injective f hf (Sum.inl.inj (Sum.inl.inj he))
    subst y
    rfl
  · intro v hn a ha
    rcases v with (b | ⟨i,w⟩) | ⟨i,k⟩
    · have hb : ∀x : InputIndex f,inputTriple f x≠b := by
        intro x hx
        apply hn
        refine ⟨(oldMarker f hf x.1 x.2,newMarker f x.1 x.2),
          (finalPairs_mem_iff_input f hf _).mpr ⟨x,rfl⟩,?_⟩
        rw [oldMarker_reverse_host,hx]
      rw [fullRows_boundary_unconsumed f hf b hb] at ha ⊢
      exact (producerBlock_base f hf b a ha).symm
    · rw [fullRows_private] at ha ⊢
      exact (blockWord_baseRotation f (some i) (FramedMacro.oldVertex _ w.val) a ha).symm
    · rw [fullRows_corner] at ha ⊢
      exact (blockWord_baseRotation f (some i) (FramedMacro.vertexParts _ (.inr k)) a ha).symm
  · intro p hp
    obtain ⟨x,rfl⟩ := (finalPairs_mem_iff_input f hf p).mp hp
    obtain ⟨xs,hxs⟩ := consumerBlock_ending f x
    obtain ⟨ys,hys⟩ := producerBlock_ending f hf (inputTriple f x)
    change producerBlock f hf (inputTriple f x)=ys++[reversePerm (Edge f) (oldMarker f hf x.1 x.2)] at hys
    refine ⟨xs,ys,?_,?_,?_⟩
    · rw [oldMarker_reverse_host f hf x,fullRows_boundary_consumer f hf x,hxs,hys]
    · intro a ha
      have hb := consumerBlock_base f x a (by rwa [hxs])
      rwa [hxs] at hb
    · intro a ha
      have hb := producerBlock_base f hf (inputTriple f x) a (by rwa [hys])
      rwa [hys] at hb

end PlanarHom.ColoringEmitter.FramedCanvas
