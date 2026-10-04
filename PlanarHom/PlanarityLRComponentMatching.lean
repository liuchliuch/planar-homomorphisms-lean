import PlanarHom.PlanarityLRComponentGraph
import PlanarHom.OccurrenceMatchingCycleConfinement
import Mathlib.GroupTheory.Perm.Fin

/-! NEW restriction of actual occurrence perfect matchings and simple cycles
to the computed DFS component, preserving every original occurrence label. -/
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints

 def componentMatching (g : MixedCode) (r : ℕ) (M : Finset (Fin g.edges.length)) : Finset (ComponentEdge g r) :=
  M.subtype (fun e : Fin g.edges.length=>componentRoot g (source g e.val)=r)

@[simp] theorem mem_componentMatching (g : MixedCode) (r : ℕ) (M : Finset (Fin g.edges.length))
    (e : ComponentEdge g r) : e∈componentMatching g r M ↔ e.val∈M := by
  simp [componentMatching]

 theorem component_endpointCount (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) (e : ComponentEdge g r) (v : ComponentVertex g r) :
    (componentGraph g hg r).endpointCount e v=(g.toMultiGraph hg).endpointCount e.val v.val := by
  simp only [endpointCount,componentGraph,Subtype.ext_iff]
  split_ifs <;> rfl

 theorem edge_component_of_endpoint_pos (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) (e : Fin g.edges.length) (v : ComponentVertex g r)
    (hpos : 0<(g.toMultiGraph hg).endpointCount e v.val) : componentRoot g (source g e.val)=r := by
  have hs := original_host_componentRoot g hg (e,true)
  have ht := original_host_componentRoot g hg (e,false)
  change componentRoot g ((g.toMultiGraph hg).src e).val=_ at hs
  change componentRoot g ((g.toMultiGraph hg).dst e).val=_ at ht
  by_cases he : (g.toMultiGraph hg).src e=v.val
  · exact hs.symm.trans ((congrArg (fun v : Fin g.vertices=>componentRoot g v.val) he).trans v.property)
  · have hd : (g.toMultiGraph hg).dst e=v.val := by
      by_contra hn
      simp [endpointCount,he,hn] at hpos
    exact ht.symm.trans ((congrArg (fun v : Fin g.vertices=>componentRoot g v.val) hd).trans v.property)

 theorem componentMatching_degree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) (M : Finset (Fin g.edges.length)) (v : ComponentVertex g r) :
    (componentGraph g hg r).selectedDegree (componentMatching g r M) v=
      (g.toMultiGraph hg).selectedDegree M v.val := by
  simp only [selectedDegree_eq_sum_endpointCount,component_endpointCount]
  change (∑e∈M.subtype (fun e : Fin g.edges.length=>componentRoot g (source g e.val)=r),
    (g.toMultiGraph hg).endpointCount e.val v.val)=_
  rw [Finset.sum_subtype_eq_sum_filter (s:=M)
    (p:=fun e : Fin g.edges.length=>componentRoot g (source g e.val)=r)
    (fun e : Fin g.edges.length=>(g.toMultiGraph hg).endpointCount e v.val)]
  apply Finset.sum_filter_of_ne
  intro e _ he
  exact edge_component_of_endpoint_pos g hg r e v (Nat.pos_of_ne_zero he)

 theorem componentMatching_perfect (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) (M : Finset (Fin g.edges.length)) (hM : (g.toMultiGraph hg).PerfectMatching M) :
    (componentGraph g hg r).PerfectMatching (componentMatching g r M) := by
  intro v
  rw [componentMatching_degree]
  exact hM v.val

 theorem componentDartLift_head (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (r : ℕ)
    (a : Dart (ComponentEdge g r)) :
    ((componentGraph g hg r).dartPair a).2.val=((g.toMultiGraph hg).dartPair (componentDartLift g r a)).2 := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

namespace DirectedSimpleCycle
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (c : MultiGraph.DirectedSimpleCycle (g.toMultiGraph hg))

 def componentIndex : Fin g.vertices :=
  ⟨componentRoot g (c.vertex ⟨0,by have := c.length_ge_two; omega⟩).val,
    (componentRoot_spec g (c.vertex ⟨0,by have := c.length_ge_two; omega⟩).isLt).1⟩

 theorem componentIndex_height : PlanarityDepthFirstSearch.height g (componentIndex g hg c).val=0 :=
  (componentRoot_spec g (c.vertex ⟨0,by have := c.length_ge_two; omega⟩).isLt).2.2

 theorem vertex_component (i : Fin c.length) :
    componentRoot g (c.vertex i).val=(componentIndex g hg c).val := by
  have hstep : ∀j,componentRoot g (c.vertex (finRotate c.length j)).val=componentRoot g (c.vertex j).val := by
    intro j
    have hs := original_host_componentRoot g hg (c.dart j)
    have ht := original_host_componentRoot g hg (reversePerm _ (c.dart j))
    change componentRoot g ((g.toMultiGraph hg).dartPair ((c.dart j).1,!(c.dart j).2)).1.val=_ at ht
    rw [dartPair_reverse_fst,c.head_eq,cycleNext_eq_finRotate] at ht
    rw [c.tail_eq] at hs
    exact ht.trans hs.symm
  let i₀ : Fin c.length := ⟨0,by have := c.length_ge_two; omega⟩
  have hn : ∀i : Fin c.length,finRotate c.length i≠i := by
    intro i
    rw [←cycleNext_eq_finRotate c.length c.length_ge_two i]
    exact cycleNext_ne c.length c.length_ge_two i
  obtain ⟨n,hni⟩ := ((isCycle_finRotate_of_le c.length_ge_two).sameCycle (hn i₀) (hn i)).exists_nat_pow_eq
  have hi : ∀n,componentRoot g (c.vertex ((finRotate c.length)^[n] i₀)).val=componentRoot g (c.vertex i₀).val := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',hstep,ih]
  simpa only [Equiv.Perm.iterate_eq_pow,hni] using hi n

 theorem edge_component (i : Fin c.length) :
    componentRoot g (source g (c.dart i).1.val)=(componentIndex g hg c).val := by
  have h := original_host_componentRoot g hg (c.dart i)
  rw [c.tail_eq] at h
  exact h.symm.trans (vertex_component g hg c i)

 def inComponent : MultiGraph.DirectedSimpleCycle (componentGraph g hg (componentIndex g hg c).val) where
  length := c.length
  length_ge_two := c.length_ge_two
  vertex i := ⟨c.vertex i,vertex_component g hg c i⟩
  vertex_injective := by intro i j h; exact c.vertex_injective (congrArg Subtype.val h)
  dart i := (⟨(c.dart i).1,edge_component g hg c i⟩,(c.dart i).2)
  edge_injective := by intro i j h; exact c.edge_injective (congrArg Subtype.val h)
  tail_eq i := by
    apply Subtype.ext
    rw [componentDartLift_host]
    exact c.tail_eq i
  head_eq i := by
    apply Subtype.ext
    rw [componentDartLift_head]
    exact c.head_eq i

end DirectedSimpleCycle
end PlanarHom.PlanarityLRRealization
