import PlanarHom.FisherExpansionPortIndices

/-! NEW occurrence-preserving incidence equivalence between the numeric
expansion program and the original abstract Fisher path/endloop graph. -/
noncomputable section
open Classical
namespace PlanarHom.FisherExpansionCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (o : (g.toMultiGraph hg).IncidenceOrdering)
variable {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o)

 def edgeEntry (e : ExpansionEdge o) : ℕ×(ℕ×ℕ) :=
  ((vertexList g hg o).idxOf ((expansionGraph o).src e),
   (vertexList g hg o).idxOf ((expansionGraph o).dst e),0)

include hr

 theorem edgeEntry_external (e : Fin g.edges.length) :
    edgeEntry g hg o (Sum.inl e)=(portNumber g rows (e.val,false),portNumber g rows (e.val,true),0) := by
  simp only [edgeEntry,expansionGraph,Sum.elim_inl]
  rw [←portNumber_eq g hg o hr (e,false),←portNumber_eq g hg o hr (e,true)]
  rfl

 theorem edgeEntry_internal (v : Fin g.vertices) (e : Fin (o.degree v+1)⊕Bool) :
    edgeEntry g hg o (Sum.inr ⟨v,e⟩)=
      (vertexNumber g rows v.val ((localExpansion (o.degree v)).src e).val,
       vertexNumber g rows v.val ((localExpansion (o.degree v)).dst e).val,0) := by
  simp only [edgeEntry,expansionGraph,Sum.elim_inr]
  rw [vertexNumber_eq g hg o hr ⟨v,_⟩,vertexNumber_eq g hg o hr ⟨v,_⟩]

 theorem externalEdgeList_map :
    ((List.finRange g.edges.length).map Sum.inl).map (edgeEntry g hg o)=externalEdges g rows := by
  rw [List.map_map]
  unfold externalEdges
  rw [←List.map_coe_finRange g.edges.length,List.map_map]
  apply List.map_congr_left
  intro e he
  exact edgeEntry_external g hg o hr e

 theorem localEdgeList_map (v : Fin g.vertices) :
    (localEdgeList g hg o v).map (fun e=>edgeEntry g hg o (Sum.inr ⟨v,e⟩))=localEdges g rows v.val := by
  simp only [localEdgeList,List.map_append,List.map_map,List.map_cons,List.map_nil,
    edgeEntry_internal g hg o hr,localExpansion,Sum.elim_inl,Sum.elim_inr,Fin.coe_castSucc,Fin.val_succ,
    pathLoopVertex,Bool.false_eq_true,if_false,if_true,Fin.val_zero,Fin.val_last]
  unfold localEdges
  rw [←hr.degree_eq g hg v]
  dsimp only
  rw [←List.map_coe_finRange (o.degree v+1),List.map_map]
  rfl

 theorem internalEdgeList_map :
    (internalEdgeList g hg o).map (fun e=>edgeEntry g hg o (Sum.inr e))=internalEdges g rows := by
  simp only [internalEdgeList,sigmaList,List.map_flatMap,List.map_map,Function.comp_def]
  unfold internalEdges
  rw [←List.map_coe_finRange g.vertices,List.flatMap_map]
  congr 1
  funext v
  exact localEdgeList_map g hg o hr v

 theorem enumeratedCode_eq :
    enumeratedCode (expansionGraph o) (vertexList g hg o) (edgeList g hg o)=code g rows := by
  have hv:=congrArg List.length (vertexList_erase g hg o hr)
  simp only [List.length_map] at hv
  have he:(edgeList g hg o).map (edgeEntry g hg o)=externalEdges g rows++internalEdges g rows := by
    rw [edgeList,List.map_append,externalEdgeList_map g hg o hr,List.map_map]
    rw [show (edgeEntry g hg o ∘ Sum.inr)=(fun e=>edgeEntry g hg o (Sum.inr e)) from rfl,
      internalEdgeList_map g hg o hr]
  unfold edgeEntry at he
  unfold enumeratedCode code
  simp only [List.idxOf,Lean.Grind.beq_eq_decide_eq] at he ⊢
  rw [hv,he]

 theorem valid : (code g rows).Valid 1 0 := by
  rw [←enumeratedCode_eq g hg o hr]
  exact enumerated_valid _ _ _ (vertexList_mem g hg o)

 def incidenceEquiv : IncidenceEquiv (expansionGraph o) ((code g rows).toMultiGraph (valid g hg o hr)) := by
  have hh:=enumeratedIncidenceEquiv (expansionGraph o) (vertexList g hg o) (edgeList g hg o)
    (vertexList_nodup g hg o) (edgeList_nodup g hg o) (vertexList_mem g hg o) (edgeList_mem g hg o)
  exact hh.trans (codeIncidenceEquiv (enumeratedCode_eq g hg o hr) _ _)

omit hr
include hg

 theorem computed_valid : (computed g).Valid 1 0 :=
  valid g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg)

 def computedIncidenceEquiv : IncidenceEquiv (expansionGraph (FisherContourOrder.ordering g hg))
    ((computed g).toMultiGraph (computed_valid g hg)) :=
  incidenceEquiv g hg (FisherContourOrder.ordering g hg) (FisherContourOrder.computed_realizes g hg)

end PlanarHom.FisherExpansionCode
