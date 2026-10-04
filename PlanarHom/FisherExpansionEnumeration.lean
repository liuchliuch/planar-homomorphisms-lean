import PlanarHom.FisherContourOrdering

/-! NEW literal finite enumerations of expansion vertices and occurrences,
matched to their actual serialized numeric addresses. -/
noncomputable section
open Classical
namespace PlanarHom.FisherExpansionCode
open Complexity MultiGraph Fisher FisherNumericEnumeration PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (o : (g.toMultiGraph hg).IncidenceOrdering)

 def vertexList : List (ExpansionVertex o) := finSigma g.vertices (fun v=>o.degree v+2)
 def eraseVertex (v : ExpansionVertex o) : ℕ×ℕ := (v.1.val,v.2.val)

 theorem eraseVertex_injective : Function.Injective (eraseVertex g hg o) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ he
  have hv:v=w:=Fin.ext (congrArg Prod.fst he)
  subst w
  have hi:i=j:=Fin.ext (congrArg Prod.snd he)
  subst j
  rfl

 theorem vertexList_nodup : (vertexList g hg o).Nodup := finSigma_nodup _ _
 theorem vertexList_mem (v : ExpansionVertex o) : v∈vertexList g hg o := finSigma_mem _ _ _

 theorem vertexList_erase {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o) :
    (vertexList g hg o).map (eraseVertex g hg o)=vertexSlots g rows := by
  simp only [vertexList,finSigma,sigmaList,List.map_flatMap,List.map_map,Function.comp_def,eraseVertex,vertexSlots]
  rw [←List.map_coe_finRange g.vertices,List.flatMap_map]
  congr 1
  funext v
  rw [←hr.degree_eq g hg v,←List.map_coe_finRange (o.degree v+2),List.map_map]
  rfl

 theorem vertexNumber_eq {rows : Rows} (hr : FisherContourOrder.Realizes g hg rows o)
    (v : ExpansionVertex o) : vertexNumber g rows v.1.val v.2.val=(vertexList g hg o).idxOf v := by
  change (vertexSlots g rows).idxOf (eraseVertex g hg o v)=_
  rw [←vertexList_erase g hg o hr]
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using
    idxOf_map_injective _ (eraseVertex_injective g hg o) (vertexList g hg o) v

 def localEdgeList (v : Fin g.vertices) : List (Fin (o.degree v+1)⊕Bool) :=
  (List.finRange (o.degree v+1)).map Sum.inl ++ [Sum.inr false,Sum.inr true]

 theorem localEdgeList_nodup (v : Fin g.vertices) : (localEdgeList g hg o v).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective,by simp,?_⟩
  intro a ha b hb hab
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl <;> cases hab

 theorem localEdgeList_mem (v : Fin g.vertices) (e : Fin (o.degree v+1)⊕Bool) :
    e∈localEdgeList g hg o v := by
  cases e with
  | inl i => simp [localEdgeList]
  | inr b => cases b <;> simp [localEdgeList]

 def internalEdgeList : List (ExpansionInternalEdge o) :=
  sigmaList (List.finRange g.vertices) (localEdgeList g hg o)
 def edgeList : List (ExpansionEdge o) :=
  (List.finRange g.edges.length).map Sum.inl ++ (internalEdgeList g hg o).map Sum.inr

 theorem internalEdgeList_nodup : (internalEdgeList g hg o).Nodup :=
  sigmaList_nodup _ _ (List.nodup_finRange _) (fun v _=>localEdgeList_nodup g hg o v)
 theorem internalEdgeList_mem (e : ExpansionInternalEdge o) : e∈internalEdgeList g hg o := by
  rw [internalEdgeList,sigmaList_mem]
  exact ⟨List.mem_finRange _,localEdgeList_mem g hg o _ _⟩

 theorem edgeList_nodup : (edgeList g hg o).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective,(internalEdgeList_nodup g hg o).map Sum.inr_injective,?_⟩
  intro a ha b hb hab
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hb
  cases hab
 theorem edgeList_mem (e : ExpansionEdge o) : e∈edgeList g hg o := by
  cases e with
  | inl e => simp [edgeList]
  | inr e => simp [edgeList,internalEdgeList_mem]

end PlanarHom.FisherExpansionCode
