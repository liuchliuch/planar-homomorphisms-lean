import PlanarHom.PlanarityLRGlobalEuler
import PlanarHom.OccurrenceIsolatedComponents

/-! Exact bijection between raw isolated vertices and empty computed DFS
components. Every isolated vertex is retained, including an entirely empty graph. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityDepthFirstSearch

 abbrev EmptyRoot (g : MixedCode) := {r : Root g // IsEmpty (ComponentEdge g r.val.val)}

 theorem isolated_vertexRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices)
    (hv : (g.toMultiGraph hg).selectedDegree Finset.univ v=0) : (vertexRoot g v).val=v := by
  apply (g.toMultiGraph hg).eq_of_connected_degree_zero v hv
  apply (component_iff_vertexRoot g hg _ _).mpr
  exact (vertexRoot_eq_root g (vertexRoot g v)).symm

 theorem isolated_emptyRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices)
    (hv : (g.toMultiGraph hg).selectedDegree Finset.univ v=0) : IsEmpty (ComponentEdge g (vertexRoot g v).val.val) := by
  refine ⟨fun e => ?_⟩
  have he : vertexRoot g ((g.toMultiGraph hg).src e.val)=vertexRoot g v := by
    apply (root_eq_iff g _ _).mpr
    exact (original_host_componentRoot g hg (e.val,true)).trans e.property
  have hc := (component_iff_vertexRoot g hg v ((g.toMultiGraph hg).src e.val)).mpr he.symm
  have hh := (g.toMultiGraph hg).eq_of_connected_degree_zero v hv hc
  exact ((g.toMultiGraph hg).degree_zero_iff_no_endpoints v |>.mp hv e.val).1 hh

 theorem emptyRoot_isolated (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : Root g)
    (hr : IsEmpty (ComponentEdge g r.val.val)) :
    (g.toMultiGraph hg).selectedDegree Finset.univ r.val=0 := by
  apply ((g.toMultiGraph hg).degree_zero_iff_no_endpoints r.val).mpr
  intro e
  have hroot := componentRoot_eq_self g r.val.isLt r.property
  constructor
  · intro h
    have he := original_host_componentRoot g hg (e,true)
    change componentRoot g ((g.toMultiGraph hg).src e).val=componentRoot g (PlanarityLRRawConstraints.source g e.val) at he
    rw [h,hroot] at he
    exact hr.false ⟨e,he.symm⟩
  · intro h
    have he := original_host_componentRoot g hg (e,false)
    change componentRoot g ((g.toMultiGraph hg).dst e).val=componentRoot g (PlanarityLRRawConstraints.source g e.val) at he
    rw [h,hroot] at he
    exact hr.false ⟨e,he.symm⟩

 def isolatedRootEquiv (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    {v : Fin g.vertices // (g.toMultiGraph hg).selectedDegree Finset.univ v=0} ≃ EmptyRoot g where
  toFun v := ⟨vertexRoot g v.val,isolated_emptyRoot g hg v.val v.property⟩
  invFun r := ⟨r.val.val,emptyRoot_isolated g hg r.val r.property⟩
  left_inv v := Subtype.ext (isolated_vertexRoot g hg v.val v.property)
  right_inv r := Subtype.ext (vertexRoot_eq_root g r.val)

 theorem isolated_card_eq_sum_roots (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    Fintype.card {v : Fin g.vertices // (g.toMultiGraph hg).selectedDegree Finset.univ v=0}=
      ∑r : Root g,if IsEmpty (ComponentEdge g r.val.val) then 1 else 0 := by
  rw [Fintype.card_congr (isolatedRootEquiv g hg),Fintype.card_subtype,Finset.card_filter]
end PlanarHom.PlanarityLRRealization
