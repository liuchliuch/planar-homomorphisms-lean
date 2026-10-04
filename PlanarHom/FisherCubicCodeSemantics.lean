import PlanarHom.FisherCubicPortIndices

/-! NEW exact occurrence/vertex bijections for the numeric triangle stage. -/
noncomputable section
open Classical
namespace PlanarHom.FisherCubicCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (hc : ∀v,(g.toMultiGraph hg).selectedDegree Finset.univ v=3)

 def vertexList : List (Fin g.vertices×Fin 3) := (List.finRange g.vertices) ×ˢ (List.finRange 3)
 theorem vertexList_nodup : (vertexList g).Nodup := (List.nodup_finRange _).product (List.nodup_finRange _)
 theorem vertexList_mem (v : Fin g.vertices×Fin 3) : v∈vertexList g := by rcases v with ⟨v,i⟩; simp [vertexList,List.mem_product]
 theorem vertexList_length : (vertexList g).length=3*g.vertices := by simp [vertexList,List.length_product,Nat.mul_comm]
 theorem vertexList_index (v : Fin g.vertices×Fin 3) : (vertexList g).idxOf v=3*v.1.val+v.2.val := by
  rcases v with ⟨v,i⟩
  calc
    _ = (List.finRange g.vertices).idxOf v*(List.finRange 3).length+(List.finRange 3).idxOf i := by
      simpa only [vertexList,List.idxOf,Lean.Grind.beq_eq_decide_eq] using
        idxOf_product (List.finRange g.vertices) (List.finRange 3) v i (List.mem_finRange _) (List.mem_finRange _)
    _ = _ := by simp [Nat.mul_comm]

 def edgeList : List (Fin g.edges.length⊕(Fin g.vertices×Fin 3)) :=
  (List.finRange g.edges.length).map Sum.inl ++ (vertexList g).map Sum.inr
 theorem edgeList_nodup : (edgeList g).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective,(vertexList_nodup g).map Sum.inr_injective,?_⟩
  intro a ha b hb he
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hb
  cases he
 theorem edgeList_mem (e : Fin g.edges.length⊕(Fin g.vertices×Fin 3)) : e∈edgeList g := by
  cases e <;> simp [edgeList,vertexList_mem]

 def edgeEntry (e : Fin g.edges.length⊕(Fin g.vertices×Fin 3)) : ℕ×(ℕ×ℕ) :=
  ((vertexList g).idxOf ((cubicDecoration (ports g hg hc)).src e),
   (vertexList g).idxOf ((cubicDecoration (ports g hg hc)).dst e),0)

 theorem edgeEntry_external (e : Fin g.edges.length) :
    edgeEntry g hg hc (Sum.inl e)=(portNumber g (e.val,false),portNumber g (e.val,true),0) := by
  simp only [edgeEntry,cubicDecoration,Sum.elim_inl,vertexList_index]
  rw [←portNumber_inverse g hg hc (e,false),←portNumber_inverse g hg hc (e,true)]
  rfl

 theorem triangleSrc_eq (i : Fin 3) : (triangle.src i).val=triangleSrc i.val := by fin_cases i <;> rfl
 theorem triangleDst_eq (i : Fin 3) : (triangle.dst i).val=triangleDst i.val := by fin_cases i <;> rfl

 theorem edgeEntry_internal (v : Fin g.vertices×Fin 3) :
    edgeEntry g hg hc (Sum.inr v)=(3*v.1.val+triangleSrc v.2.val,3*v.1.val+triangleDst v.2.val,0) := by
  simp only [edgeEntry,cubicDecoration,Sum.elim_inr,vertexList_index,triangleSrc_eq,triangleDst_eq]

 theorem externalEdgeList_map :
    ((List.finRange g.edges.length).map Sum.inl).map (edgeEntry g hg hc)=externalEdges g := by
  rw [List.map_map]
  unfold externalEdges
  rw [←List.map_coe_finRange g.edges.length,List.map_map]
  apply List.map_congr_left
  intro e he
  exact edgeEntry_external g hg hc e

 theorem internalEdgeList_map :
    ((vertexList g).map Sum.inr).map (edgeEntry g hg hc)=internalEdges g := by
  simp only [vertexList,List.map_map,SProd.sprod,List.product,List.map_flatMap]
  unfold internalEdges
  rw [←List.map_coe_finRange g.vertices,List.flatMap_map]
  congr 1
  funext v
  rw [←List.map_coe_finRange 3,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact edgeEntry_internal g hg hc (v,i)

 theorem enumeratedCode_eq :
    enumeratedCode (cubicDecoration (ports g hg hc)) (vertexList g) (edgeList g)=code g := by
  have he:(edgeList g).map (edgeEntry g hg hc)=externalEdges g++internalEdges g := by
    rw [edgeList,List.map_append,externalEdgeList_map,internalEdgeList_map]
  unfold edgeEntry at he
  unfold enumeratedCode code
  simp only [List.idxOf,Lean.Grind.beq_eq_decide_eq] at he ⊢
  rw [vertexList_length,he]

 include hg hc in
 theorem valid : (code g).Valid 1 0 := by
  rw [←enumeratedCode_eq g hg hc]
  exact enumerated_valid _ _ _ (vertexList_mem g)

 def incidenceEquiv : IncidenceEquiv (cubicDecoration (ports g hg hc)) ((code g).toMultiGraph (valid g hg hc)) :=
  (enumeratedIncidenceEquiv _ (vertexList g) (edgeList g)
    (vertexList_nodup g) (edgeList_nodup g) (vertexList_mem g) (edgeList_mem g)).trans
      (codeIncidenceEquiv (enumeratedCode_eq g hg hc) _ _)

end PlanarHom.FisherCubicCode
