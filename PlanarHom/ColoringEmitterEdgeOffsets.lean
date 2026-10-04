import PlanarHom.ColoringEmitterEdgeEquivalence
import PlanarHom.ListBlockIndexing

/-! NEW literal occurrence offsets used by the numeric rotation serializer. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem cellEdgeBlocks_flat_length (cs:List Cell) (s:State) :
    (cellEdgeBlocks cs s).flatten.length=(cs.map (fun c=>(Macro.edges c.shape.kind).length)).sum := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [cellEdgeBlocks,ih,emitEdges,Cell.instruction]

namespace Canvas

 theorem before_edges_length (f:NumericFormula) (i:Index f) :
    (before f i).edges.length=((canvas f).take i.val |>.map (fun c=>(Macro.edges c.shape.kind).length)).sum := by
  rw [before,fold_cell_edges]
  simpa only [initial,List.nil_append] using cellEdgeBlocks_flat_length ((canvas f).take i.val) (initial f.1)

 theorem edgeEquiv_val (f:NumericFormula) (i:Index f) (e:LocalPatch.Edge (canvasCell f i).shape) :
    (edgeEquiv f ⟨i,e⟩).val=(before f i).edges.length+e.val := by
  let blocks := fun j:Index f => (List.finRange (Macro.edges (canvasCell f j).shape.kind).length).map (fun a=>(⟨j,a⟩:Edge f))
  let ii:Fin (List.finRange (canvas f).length).length:=Fin.cast (List.length_finRange).symm i
  let ee:Fin (blocks ((List.finRange (canvas f).length).get ii)).length:=⟨e.val,by simpa [blocks,ii] using e.isLt⟩
  have hh:=ListBlockIndexing.get_flatMap_at (List.finRange (canvas f).length) blocks ii ee
  have hval:(blocks ((List.finRange (canvas f).length).get ii)).get ee=⟨i,e⟩:=by
    simp only [blocks,List.get_eq_getElem,List.getElem_map,List.getElem_finRange,ii,Fin.coe_cast,ee]
    apply Sigma.ext (by simp)
    apply (Fin.heq_ext_iff (by simp)).mpr
    rfl
  rw [hval] at hh
  have hprefix:(((List.finRange (canvas f).length).take ii.val).flatMap blocks).length=(before f i).edges.length:=by
    rw [←ListBlockIndexing.prefix_length]
    simp only [blocks,List.length_map,List.length_finRange]
    rw [before_edges_length]
    simpa [ii,List.length_flatMap] using
      (ListBlockIndexing.prefix_length (canvas f) (fun c=>Macro.edges c.shape.kind) i)
  rw [hprefix] at hh
  change (typedEdges f)[(before f i).edges.length+e.val]?=some ⟨i,e⟩ at hh
  have hlt:(before f i).edges.length+e.val<(typedEdges f).length:=List.getElem?_eq_some_iff.mp hh |>.1
  have hget:(typedEdges f)[(before f i).edges.length+e.val]=⟨i,e⟩:=by
    rw [List.getElem?_eq_getElem hlt] at hh
    exact Option.some.inj hh
  change (typedEdges f).idxOf ⟨i,e⟩=_
  rw [←hget,List.idxOf_getElem (typedEdges_nodup f)]

end Canvas
end PlanarHom.ColoringEmitter
