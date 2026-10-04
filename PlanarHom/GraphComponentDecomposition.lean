import PlanarHom.GraphComponentConnectivity
import PlanarHom.GraphComponentPlanarity

/-! The proved connected-input preprocessing interface. -/
namespace PlanarHom.GraphComponentCode
open Complexity

theorem parts_nodup (g : MixedCode) : (parts g).Nodup := by
  apply List.Pairwise.imp_of_mem _ (parts_pairwise_disjoint g)
  intro xs ys hx hy hd heq
  subst ys
  have hne := parts_nonempty g xs hx
  obtain ⟨v,hv⟩ := List.exists_mem_of_ne_nil xs hne
  exact (List.disjoint_left.mp hd) hv hv

/-- The component machine keeps every vertex exactly once. -/
theorem components_vertex_sum (g : MixedCode) :
    ((components g).map MixedCode.vertices).sum = g.vertices := by
  have h := (parts_flatten_perm g).length_eq
  simpa [components,extract,List.length_flatten,List.map_map,Function.comp_def] using h

/-- The number of nonempty connected oracle inputs is at most the explicitly
encoded original vertex count, including an all-isolated input. -/
theorem components_length_le (g : MixedCode) : (components g).length ≤ g.vertices := by
  have h := List.sum_le_sum (l:=components g) (f:=fun _ : MixedCode => 1)
    (g:=MixedCode.vertices) (fun c hc => components_nonempty g c hc)
  simpa [components_vertex_sum,List.map_const',List.sum_replicate] using h

@[simp] theorem components_of_vertices_zero (g : MixedCode) (hg : g.vertices=0) : components g = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  have h := components_length_le g
  omega

theorem components_planarValid {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.PlanarValid binaryTypes unaryTypes) (c : MixedCode) (hc : c∈components g) :
    c.PlanarValid binaryTypes unaryTypes := by
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hc
  exact extract_planarValid g hg xs (part_nodup g xs hx) (part_vertex_lt g xs hx)

/-- Ready for a connected-query reduction: actual local codes, with endpoint and
label validity, ordinary planarity, genuine support connectedness and nonemptiness. -/
theorem components_promises {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.PlanarValid binaryTypes unaryTypes) :
    ∀c∈components g, c.PlanarValid binaryTypes unaryTypes ∧
      (support c).Connected ∧ 0<c.vertices := by
  intro c hc
  exact ⟨components_planarValid g hg c hc,components_connected g hg.1 c hc,
    components_nonempty g c hc⟩

end PlanarHom.GraphComponentCode
