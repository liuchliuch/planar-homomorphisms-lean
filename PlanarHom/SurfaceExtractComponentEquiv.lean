import PlanarHom.SurfaceComponentHomologyDimension
import PlanarHom.GraphComponentPlanarity
import PlanarHom.GraphComponentSemantics

/-! NEW exact occurrence and vertex correspondence between the literal
component extraction and the actual DFS component. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceComponentCode
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PlanarityLRDirect
open PlanarityLRRawConstraints GraphComponentCode
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)

theorem reach_of_component {a b : Fin g.vertices}
    (h:(g.toMultiGraph hg).componentSetoid Finset.univ a b) : Reach g.edges a.val b.val := by
  induction h with
  | rel a b h =>
    obtain ⟨e,_,rfl,rfl⟩:=h
    exact edge_reach g.edges (g.edges.get e) (List.get_mem _ _)
  | refl => exact .refl
  | symm _ _ _ ih => exact reach_symm _ ih
  | trans _ _ _ _ _ ih ij => exact ih.trans ij

include hg

theorem root_eq_of_reach {u v : ℕ} (h:Reach g.edges u v) :
    componentRoot g u=componentRoot g v := by
  induction h with
  | refl => rfl
  | tail h ha ih =>
    obtain ⟨_,e,he,heq|heq⟩:=ha
    all_goals
      obtain ⟨i,rfl⟩:=List.mem_iff_get.mp he
      have he:=endpoints_componentRoot g hg i.isLt
      simp only [edge,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt,Option.getD_some] at he
    · exact ih.trans (heq.1 ▸ heq.2 ▸ he)
    · exact ih.trans (heq.1 ▸ heq.2 ▸ he.symm)

def partRoot (xs : List ℕ) (hx:xs∈parts g) : Root g :=
  vertexRoot g ⟨xs.head (parts_nonempty g xs hx),
    part_vertex_lt g xs hx _ (List.head_mem (parts_nonempty g xs hx))⟩

theorem mem_part_iff_root (xs : List ℕ) (hx:xs∈parts g) (v:Fin g.vertices) :
    v.val∈xs ↔ componentRoot g v.val=(partRoot g xs hx).val.val := by
  constructor
  · intro hv
    exact (root_eq_of_reach g hg (parts_sound g xs hx _
      (List.head_mem (parts_nonempty g xs hx)) _ hv)).symm
  · intro hv
    have hh:vertexRoot g ⟨xs.head (parts_nonempty g xs hx),
        part_vertex_lt g xs hx _ (List.head_mem (parts_nonempty g xs hx))⟩=vertexRoot g v :=
      (root_eq_iff g _ _).mpr hv.symm
    exact part_reach_closed g hg xs hx (List.head_mem (parts_nonempty g xs hx))
      (reach_of_component g hg ((component_iff_vertexRoot g hg _ _).mpr hh))

def extractVertexEquiv (xs : List ℕ) (hx:xs∈parts g) :
    Fin xs.length≃ComponentVertex g (partRoot g xs hx).val.val where
  toFun v:=⟨extractVertexEmbedding g xs (part_nodup g xs hx) (part_vertex_lt g xs hx) v,
    (mem_part_iff_root g hg xs hx _).mp (List.get_mem _ _)⟩
  invFun v:=⟨xs.idxOf v.val.val,List.idxOf_lt_length_iff.mpr
    ((mem_part_iff_root g hg xs hx v.val).mpr v.property)⟩
  left_inv v:=Fin.ext (List.get_idxOf (part_nodup g xs hx) v)
  right_inv v:=Subtype.ext (Fin.ext (List.getElem_idxOf _))

theorem edgeInside_iff_component (xs : List ℕ) (hx:xs∈parts g) (e:Fin g.edges.length) :
    edgeInside xs (g.edges.get e)=true ↔
      componentRoot g (source g e.val)=(partRoot g xs hx).val.val := by
  have hs:=mem_part_iff_root g hg xs hx ((g.toMultiGraph hg).src e)
  have hd:=mem_part_iff_root g hg xs hx ((g.toMultiGraph hg).dst e)
  have he:=original_host_componentRoot g hg (e,true)
  have he':=original_host_componentRoot g hg (e,false)
  change componentRoot g ((g.toMultiGraph hg).src e).val=_ at he
  change componentRoot g ((g.toMultiGraph hg).dst e).val=_ at he'
  simp only [edgeInside,decide_eq_true_eq]
  change ((g.toMultiGraph hg).src e).val∈xs ∧ ((g.toMultiGraph hg).dst e).val∈xs ↔ _
  rw [hs,hd,he,he',and_self]

def extractEdgeEquiv (xs : List ℕ) (hx:xs∈parts g) :
    Fin (GraphComponentCode.extract g xs).edges.length≃ComponentEdge g (partRoot g xs hx).val.val :=
  ((finCongr (extract_edges_length g xs)).trans (FilteredOccurrence.equiv g.edges (edgeInside xs))).trans
    (Equiv.subtypeEquivRight (edgeInside_iff_component g hg xs hx))

def extractIncidenceEquiv (xs : List ℕ) (hx:xs∈parts g) :
    IncidenceEquiv ((GraphComponentCode.extract g xs).toMultiGraph (extract_valid g hg xs))
      (componentGraph g hg (partRoot g xs hx).val.val) where
  vertex:=extractVertexEquiv g hg xs hx
  edge:=extractEdgeEquiv g hg xs hx
  src_eq e:=Subtype.ext ((extractIncidenceEmbedding g hg xs (part_nodup g xs hx)
    (part_vertex_lt g xs hx)).src_eq e)
  dst_eq e:=Subtype.ext ((extractIncidenceEmbedding g hg xs (part_nodup g xs hx)
    (part_vertex_lt g xs hx)).dst_eq e)

end PlanarHom.SurfaceComponentCode
