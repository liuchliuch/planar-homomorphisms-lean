import PlanarHom.FisherReferenceSignProducts

/-! NEW actual reference matching in the numeric cubic output: precisely the
original external occurrences, with no search or nonzero-weight premise. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph Fisher FisherNumericEnumeration
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)
local instance (priority := high) referenceEdgeBEq : BEq (Fin g.edges.length⊕(Fin g.vertices×Fin 3)) := instBEqOfDecidableEq

 def referenceEdge (e : Fin g.edges.length) : Fin (code g).edges.length :=
  (incidenceEquiv g hg hc).edge (Sum.inl e)
 def referenceMatching : Finset (Fin (code g).edges.length) := Finset.univ.image (referenceEdge g hg hc)
 theorem referenceEdge_injective : Function.Injective (referenceEdge g hg hc) :=
  (incidenceEquiv g hg hc).edge.injective.comp Sum.inl_injective

 theorem referenceMatching_perfect : ((code g).toMultiGraph (valid g hg hc)).PerfectMatching (referenceMatching g hg hc) := by
  have hh:=((incidenceEquiv g hg hc).perfectMatching_map_iff Fisher.referenceMatching).mpr
    (Fisher.referenceMatching_perfect (ports g hg hc))
  convert hh using 1
  ext e
  simp [referenceMatching,referenceEdge,Fisher.referenceMatching,Fisher.decoratedEdges,Fisher.internalEdges,Equiv.apply_eq_iff_eq_symm_apply]

 theorem referenceEdge_val (e : Fin g.edges.length) : (referenceEdge g hg hc e).val=e.val := by
  rw [referenceEdge,incidenceEquiv_edge_val]
  have hm:Sum.inl e∈(List.finRange g.edges.length).map (Sum.inl : Fin g.edges.length→Fin g.edges.length⊕(Fin g.vertices×Fin 3)):=
    List.mem_map.mpr ⟨e,List.mem_finRange _,rfl⟩
  rw [edgeList,List.idxOf_append,if_pos hm]
  have hh:=idxOf_map_injective (Sum.inl : Fin g.edges.length→Fin g.edges.length⊕(Fin g.vertices×Fin 3))
    Sum.inl_injective (List.finRange g.edges.length) e
  calc
    _ = (List.finRange g.edges.length).idxOf e := by
      simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using hh
    _ = e.val := List.idxOf_finRange e

 theorem incidenceEquiv_vertex_val (v : Fin g.vertices×Fin 3) :
    ((incidenceEquiv g hg hc).vertex v).val=3*v.1.val+v.2.val := by
  change ((codeIncidenceEquiv (enumeratedCode_eq g hg hc) _ _).vertex
    ((enumeratedIncidenceEquiv _ _ _ _ _ _ _).vertex v)).val=_
  rw [codeIncidenceEquiv_vertex_val]
  have hh:=vertexList_index g v
  simpa [enumeratedIncidenceEquiv,List.Nodup.getEquivOfForallMemList,List.idxOf,Lean.Grind.beq_eq_decide_eq] using hh

 theorem referenceEdge_src (e : Fin g.edges.length) :
    (((code g).toMultiGraph (valid g hg hc)).src (referenceEdge g hg hc e)).val=portNumber g (e.val,false) := by
  have hh:=(incidenceEquiv g hg hc).src_eq (Sum.inl e)
  have hv:=congrArg Fin.val hh
  rw [incidenceEquiv_vertex_val] at hv
  exact hv.trans (portNumber_inverse g hg hc (e,false)).symm

 theorem referenceEdge_dst (e : Fin g.edges.length) :
    (((code g).toMultiGraph (valid g hg hc)).dst (referenceEdge g hg hc e)).val=portNumber g (e.val,true) := by
  have hh:=(incidenceEquiv g hg hc).dst_eq (Sum.inl e)
  have hv:=congrArg Fin.val hh
  rw [incidenceEquiv_vertex_val] at hv
  exact hv.trans (portNumber_inverse g hg hc (e,true)).symm

end PlanarHom.FisherCubicCode
