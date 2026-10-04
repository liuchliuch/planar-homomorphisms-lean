import PlanarHom.ColoringFramedGlobalMarkers
import PlanarHom.ColoringFinalFacePairSupport

/-! NEW unconditional nonrepetition of every actual final face-splice marker.
The proof retains literal cell/input order and the original nested program. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree FinitePermutationCycles

 theorem cellPairs_eq_finRange (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f) :
    cellPairs f hf i=(List.finRange (sharedPred f i+1)).map (fun j=>(oldMarker f hf i j,newMarker f i j)) := by
  rw [cellPairs,←List.map_coe_finRange (sharedPred f i+1),List.map_map]
  apply List.map_congr_left
  intro j hj
  exact Prod.ext (extendBoundaryPath_at (sharedPred f i) (oldMarker f hf i) j)
    (extendBoundaryPath_at (sharedPred f i) (newMarker f i) j)

 def localInputMarker (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f)
    (p:Fin (sharedPred f i+1)×Bool) : Dart f := inputMarker f hf (⟨i,p.1⟩,p.2)

 theorem cellMarkers_eq_product (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f) :
    pairMarkers (cellPairs f hf i)=
      ((List.finRange (sharedPred f i+1)).product [false,true]).map (localInputMarker f hf i) := by
  rw [cellPairs_eq_finRange]
  simp only [pairMarkers,List.flatMap_map,List.product,List.map_flatMap,List.map_map,List.map_cons,List.map_nil]
  rfl

 theorem localInputMarker_injective (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f) :
    Function.Injective (localInputMarker f hf i) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ h
  have he:((⟨i,a⟩:InputIndex f),c)=((⟨i,b⟩:InputIndex f),d):=inputMarker_injective f hf h
  have hab:a=b:=by
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using congrArg Prod.fst he
  exact Prod.ext hab (congrArg (fun p:InputIndex f×Bool=>p.2) he)

 theorem cellMarkers_nodup (f:NumericFormula) (hf:NumericValid f) (i:Canvas.Index f) :
    (pairMarkers (cellPairs f hf i)).Nodup := by
  rw [cellMarkers_eq_product]
  exact ((List.nodup_finRange _).product (by decide : ([false,true]:List Bool).Nodup)).map
    (localInputMarker_injective f hf i)

 theorem cellMarkers_disjoint (f:NumericFormula) (hf:NumericValid f) (i j:Canvas.Index f) (hij:i≠j) :
    List.Disjoint (pairMarkers (cellPairs f hf i)) (pairMarkers (cellPairs f hf j)) := by
  rw [cellMarkers_eq_product,cellMarkers_eq_product]
  apply List.disjoint_left.mpr
  intro a ha hb
  obtain ⟨p,_,hp⟩:=List.mem_map.mp ha
  obtain ⟨q,_,hq⟩:=List.mem_map.mp hb
  have he:((⟨i,p.1⟩:InputIndex f),p.2)=((⟨j,q.1⟩:InputIndex f),q.2):=
    inputMarker_injective f hf (hp.trans hq.symm)
  exact hij (congrArg (fun p:InputIndex f×Bool=>p.1.1) he)

 theorem prefixPairs_markers_nodup (f:NumericFormula) (hf:NumericValid f) (n:ℕ) :
    (pairMarkers (prefixPairs f hf n)).Nodup :=
  prefixMarkers_nodup f hf (cellMarkers_nodup f hf) (cellMarkers_disjoint f hf) n

 theorem finalPairs_markers_nodup (f:NumericFormula) (hf:NumericValid f) :
    (pairMarkers (finalPairs f hf)).Nodup :=
  finalMarkers_nodup f hf (cellMarkers_nodup f hf) (cellMarkers_disjoint f hf)

end PlanarHom.ColoringEmitter.FramedCanvas
