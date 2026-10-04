import PlanarHom.ColoringEmitterPrefixAllocation
import Mathlib.Data.List.NodupEquivFin

/-! NEW exact flattened occurrence enumeration for the actual stateful emitter.
Equal endpoint pairs remain different occurrences; cell/local edge order is
preserved, and no source-validity hypothesis is needed. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open PositiveBlockProgram ParsimoniousNorOneInThree

 def cellEdgeBlocks : List Cell→State→List (List EdgeCode)
  | [],_=>[]
  | c::cs,s=>emitEdges s c.instruction::cellEdgeBlocks cs (step s c.instruction)

 theorem cellEdgeBlocks_length (cs:List Cell) (s:State) : (cellEdgeBlocks cs s).length=cs.length := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [cellEdgeBlocks,List.length_cons,ih]

 theorem fold_cell_edges (cs:List Cell) (s:State) :
    ((cs.map Cell.instruction).foldl step s).edges=s.edges++(cellEdgeBlocks cs s).flatten := by
  induction cs generalizing s with
  | nil => simp [cellEdgeBlocks]
  | cons c cs ih => simp only [List.map_cons,List.foldl_cons,ih,step,cellEdgeBlocks,List.flatten_cons,List.append_assoc]

 theorem cellEdgeBlocks_get (cs:List Cell) (s:State) (i:Fin cs.length) :
    (cellEdgeBlocks cs s).get (Fin.cast (cellEdgeBlocks_length cs s).symm i)=
      emitEdges (((cs.take i.val).map Cell.instruction).foldl step s) (cs.get i).instruction := by
  induction cs generalizing s with
  | nil => exact i.elim0
  | cons c cs ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [cellEdgeBlocks,List.get_eq_getElem,Fin.coe_cast,Fin.val_succ,List.getElem_cons_succ,
        List.take_succ_cons,List.map_cons,List.foldl_cons] using ih (step s c.instruction) i

namespace Canvas

 def typedEdges (f:NumericFormula) : List (Edge f) :=
  (List.finRange (canvas f).length).sigma (fun i=>List.finRange (Macro.edges (canvasCell f i).shape.kind).length)

 theorem typedEdges_nodup (f:NumericFormula) : (typedEdges f).Nodup :=
  (List.nodup_finRange _).sigma (fun _=>List.nodup_finRange _)
 theorem typedEdges_mem (f:NumericFormula) (e:Edge f) : e∈typedEdges f := by
  rcases e with ⟨i,e⟩
  simp [typedEdges,List.mem_sigma]

 def emittedEdge (f:NumericFormula) (e:Edge f) : EdgeCode :=
  (localVertex (canvasCell f e.1).instruction (before f e.1).dictionary (before f e.1).vertices
      (LocalPatch.edgePair (canvasCell f e.1).shape e.2).1,
   localVertex (canvasCell f e.1).instruction (before f e.1).dictionary (before f e.1).vertices
      (LocalPatch.edgePair (canvasCell f e.1).shape e.2).2,0)

 theorem blocks_eq (f:NumericFormula) : cellEdgeBlocks (canvas f) (initial f.1)=
    (List.finRange (canvas f).length).map (fun i=>emitEdges (before f i) (canvasCell f i).instruction) := by
  apply List.ext_getElem (by simp [cellEdgeBlocks_length])
  intro j hj hk
  have hj':j<(canvas f).length:=by simpa only [cellEdgeBlocks_length] using hj
  have hh:=cellEdgeBlocks_get (canvas f) (initial f.1) ⟨j,hj'⟩
  simpa only [List.get_eq_getElem,Fin.coe_cast,List.getElem_map,List.getElem_finRange,before] using hh

 theorem emittedCell_map (f:NumericFormula) (i:Index f) :
    emitEdges (before f i) (canvasCell f i).instruction=
      (List.finRange (Macro.edges (canvasCell f i).shape.kind).length).map (fun e=>emittedEdge f ⟨i,e⟩) := by
  unfold emitEdges
  rw [←List.finRange_map_get (Macro.edges (canvasCell f i).instruction.1),List.map_map]
  rfl

 theorem state_edges_eq_map (f:NumericFormula) : (state f).edges=(typedEdges f).map (emittedEdge f) := by
  rw [state_eq_cells,fold_cell_edges]
  change (cellEdgeBlocks (canvas f) (initial f.1)).flatten=_
  rw [blocks_eq]
  simp only [typedEdges,List.sigma,List.map_flatMap,List.map_map,Function.comp_def,←List.flatMap_def]
  congr 1
  funext i
  exact emittedCell_map f i

 def edgeEquiv (f:NumericFormula) : Edge f ≃ Fin (state f).edges.length :=
  ((typedEdges_nodup f).getEquivOfForallMemList (typedEdges f) (typedEdges_mem f)).symm.trans
    (finCongr (by rw [state_edges_eq_map,List.length_map]))

 theorem state_edge_get (f:NumericFormula) (i:Index f) (e:LocalPatch.Edge (canvasCell f i).shape) :
    (state f).edges.get (edgeEquiv f ⟨i,e⟩)=
      (localVertex (canvasCell f i).instruction (before f i).dictionary (before f i).vertices (LocalPatch.edgePair (canvasCell f i).shape e).1,
       localVertex (canvasCell f i).instruction (before f i).dictionary (before f i).vertices (LocalPatch.edgePair (canvasCell f i).shape e).2,0) := by
  have hi:(typedEdges f).idxOf ⟨i,e⟩<(typedEdges f).length:=List.idxOf_lt_length_iff.mpr (typedEdges_mem f ⟨i,e⟩)
  have hget:(state f).edges[(edgeEquiv f ⟨i,e⟩).val]?=some (emittedEdge f ⟨i,e⟩):=by
    change (state f).edges[(typedEdges f).idxOf ⟨i,e⟩]?=_
    rw [state_edges_eq_map]
    simp [List.getElem?_map,hi,List.getElem_idxOf]
  rw [List.getElem?_eq_getElem (edgeEquiv f ⟨i,e⟩).isLt] at hget
  exact Option.some.inj hget

end Canvas
end PlanarHom.ColoringEmitter
