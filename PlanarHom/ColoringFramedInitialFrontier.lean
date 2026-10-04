import PlanarHom.ColoringFramedFrontierWords
import PlanarHom.ColoringFramedMarkerInjection
import PlanarHom.FiniteRotateCycleWord

/-! NEW exact initial cyclic frontier of the source seed. Physical channels
[2,1,0] enumerate seed vertices 3*r,3*r+1,3*r+2 in increasing order. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 def seedMarker (f:NumericFormula) (v:Fin (3*f.1)) : Dart f :=
  seedDart f ((finRotate (3*f.1)).symm v,true)

 theorem seedMarker_injective (f:NumericFormula) : Function.Injective (seedMarker f) := by
  intro a b h
  exact (finRotate (3*f.1)).symm.injective (congrArg Prod.fst (seedDart_injective f h))

 theorem seedMarker_step (f:NumericFormula) (v:Fin (3*f.1)) :
    baseFace f (seedMarker f v)=seedMarker f (finRotate (3*f.1) v) := by
  change seedDart f (finRotate (3*f.1) ((finRotate (3*f.1)).symm v),true)=
    seedDart f ((finRotate (3*f.1)).symm (finRotate (3*f.1) v),true)
  rw [Equiv.apply_symm_apply,Equiv.symm_apply_apply]

 theorem producerMarker_initial (f:NumericFormula) (hf:NumericValid f) (i:Fin f.1) (b:Fin 3) :
    producerMarker f hf (initialBoundary f i,b)=seedMarker f (initialVertex f i b) := by
  unfold producerMarker
  rw [←Canvas.signalEquiv_initial f hf i,Equiv.symm_apply_apply]
  rfl

 theorem initial_frontier_word (f:NumericFormula) (hf:NumericValid f) (fallback:Boundary f) :
    frontierWord f hf fallback (railFrontier 0 0 (List.range f.1))=List.ofFn (seedMarker f) := by
  have he:frontierWord f hf fallback (railFrontier 0 0 (List.range f.1))=
      (List.range f.1).flatMap (fun k=>tripleWord f hf (signalForName f hf fallback k)):=by
    have hh:=congrArg (fun xs:List ℕ=>xs.flatMap (fun k=>tripleWord f hf (signalForName f hf fallback k)))
      (railFrontier_map_names 0 0 (List.range f.1))
    simpa only [List.flatMap_map,frontierWord,Function.comp_def] using hh
  rw [he,←List.map_coe_finRange f.1,List.flatMap_map,List.ofFn_mul']
  rw [List.ofFn_eq_map,←List.flatMap_def]
  congr 1
  funext i
  have hs:signalForName f hf fallback i.val=initialBoundary f i:=by
    rw [←boundaryName_initial f hf i,signalForName_eq]
  simp only [Function.comp_def,hs,tripleWord,producerMarker_initial]
  simp [List.ofFn_succ,initialVertex]

 theorem initial_frontier_cyclic (f:NumericFormula) (hf:NumericValid f) (fallback:Boundary f) (hn:0<f.1) :
    CyclicSublist (baseFace f) (frontierWord f hf fallback (railFrontier 0 0 (List.range f.1))) := by
  rw [initial_frontier_word,List.ofFn_eq_map]
  apply CyclicSublist.map_embedding (finRotate (3*f.1)) (baseFace f) (seedMarker f)
    (seedMarker_injective f) (seedMarker_step f)
  have hN:0<3*f.1:=by omega
  refine ⟨⟨0,hN⟩,?_⟩
  rw [finRotate_cycleWord]

end PlanarHom.ColoringEmitter.FramedCanvas
