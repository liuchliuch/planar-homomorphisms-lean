import PlanarHom.PlanarityDepthFirstSearchSources
import PlanarHom.PlanarityDepthFirstSearchCodecs
import PlanarHom.CodecSizeBounds

/-! NEW reconstruction. Every numeric DFS field is copied from an actual input
word or a bounded occurrence/vertex index. These are binary-word bounds, not a
unit-cost assumption on arbitrarily large endpoint labels. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

def inputLength (g : MixedCode) : ℕ := (MixedCode.encoding.encode g).length

def SmallNat (g : MixedCode) (v : ℕ) : Prop := (BitEncoding.nat.encode v).length ≤ inputLength g

 theorem vertices_le_input (g : MixedCode) : g.vertices≤ inputLength g := MixedCode.vertices_le_length g
 theorem edges_le_input (g : MixedCode) : g.edges.length≤ inputLength g := MixedCode.edges_le_length g

 theorem small_of_le_vertices (g : MixedCode) {v : ℕ} (hv : v≤g.vertices) : SmallNat g v :=
  (encodeNat_length_le v).trans (hv.trans (vertices_le_input g))
 theorem small_of_le_edges (g : MixedCode) {v : ℕ} (hv : v≤g.edges.length) : SmallNat g v :=
  (encodeNat_length_le v).trans (hv.trans (edges_le_input g))

 theorem edge_word_le_input (g : MixedCode) {e : Edge} (he : e∈g.edges) :
    (edgeCode.encode e).length≤ inputLength g := by
  have hh := MaterializedFieldHeights.element_length_le_list edgeCode g.edges he
  apply hh.trans
  simp only [inputLength,MixedCode.encoding,BitEncoding.retract,BitEncoding.prod_length,
    edgeCode]
  omega

 theorem neighbour_small (g : MixedCode) (v : ℕ) {a : Arc} (ha : a∈neighbours g v) :
    SmallNat g a.1 ∧ SmallNat g a.2 := by
  obtain ⟨e,he,hadj⟩ := neighbours_adjacent g v ha
  have hh := edge_word_le_input g he
  have heq : (edgeCode.encode e).length = 2*(BitEncoding.nat.encode e.1).length+
      (2*(BitEncoding.nat.encode e.2.1).length+(BitEncoding.nat.encode e.2.2).length+1)+1 := by
    simp [edgeCode,BitEncoding.prod_length]
  refine ⟨?_,small_of_le_edges g (neighbours_index_lt g v ha).le⟩
  unfold SmallNat
  rcases hadj with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h2] at heq; omega
  · rw [h1] at heq; omega

structure SmallFields (g : MixedCode) (s : State) : Prop where
  work : ∀t∈s.work,SmallNat g t.vertex ∧ SmallNat g t.edge
  discovered : ∀r∈s.discovered,SmallNat g r.vertex ∧ SmallNat g r.treeEdge
  finished : ∀v∈s.finished,SmallNat g v

 theorem smallFields_initial (g : MixedCode) : SmallFields g (initial g) := by
  constructor
  · intro t ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    exact ⟨small_of_le_vertices g (List.mem_range.mp hv).le,small_of_le_edges g le_rfl⟩
  · simp [initial]
  · simp [initial]

 theorem smallFields_step (g : MixedCode) (s : State) (h : SmallFields g s) : SmallFields g (step g s) := by
  cases hw : s.work with
  | nil => simpa [step,hw] using h
  | cons t rest =>
    have htop := h.work t (by rw [hw]; exact List.mem_cons_self)
    have hrest : ∀t'∈rest,SmallNat g t'.vertex ∧ SmallNat g t'.edge :=
      fun t' ht'=>h.work t' (by rw [hw]; exact List.mem_cons_of_mem _ ht')
    cases ht : t.enter with
    | false =>
      simp only [step,hw,ht,Bool.false_eq_true,↓reduceIte]
      refine ⟨hrest,h.discovered,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact htop.1
      · exact h.finished v hv
    | true =>
      by_cases hn : t.vertex<g.vertices ∧ t.vertex∉seen s
      · simp only [step,hw,ht,hn,↓reduceIte]
        constructor
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
            exact neighbour_small g t.vertex hb
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨htop.1,small_of_le_edges g (Nat.zero_le _)⟩
            · exact hrest a ha
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact htop
          · exact h.discovered r hr
        · exact h.finished
      · simpa only [step,hw,ht,hn,↓reduceIte] using
          (show SmallFields g ⟨rest,s.active,s.discovered,s.finished⟩ from ⟨hrest,h.discovered,h.finished⟩)

 theorem smallFields_iterate (g : MixedCode) (n : ℕ) : SmallFields g ((step g)^[n] (initial g)) := by
  induction n with
  | zero => exact smallFields_initial g
  | succ n ih => rw [Function.iterate_succ_apply']; exact smallFields_step g _ ih

 theorem goodPath_length (g : MixedCode) {path : List ℕ} (h : GoodPath g path) : path.length≤g.vertices := by
  have ht := List.toFinset_card_of_nodup h.1
  have hsub : path.toFinset ⊆ Finset.range g.vertices := by
    intro v hv
    exact Finset.mem_range.mpr (h.2 v (List.mem_toFinset.mp hv))
  simpa [ht] using Finset.card_le_card hsub

 theorem step_work_length (g : MixedCode) (s : State) :
    (step g s).work.length ≤ s.work.length+2*g.edges.length+1 := by
  cases hw : s.work with
  | nil => simp [step,hw]
  | cons t rest =>
    have hn := neighbours_length g t.vertex
    simp only [step,hw]
    split_ifs <;> simp only [List.length_append,childTasks_length,List.length_cons] <;> omega

 theorem step_finished_length (g : MixedCode) (s : State) :
    (step g s).finished.length ≤ s.finished.length+1 := by
  cases hw : s.work with
  | nil => simp [step,hw]
  | cons t rest => simp only [step,hw]; split_ifs <;> simp

 theorem iterate_work_length (g : MixedCode) (t : ℕ) :
    ((step g)^[t] (initial g)).work.length ≤ g.vertices+t*(2*g.edges.length+1) := by
  induction t with
  | zero => simp [initial]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_work_length g ((step g)^[t] (initial g))
    nlinarith

 theorem iterate_finished_length (g : MixedCode) (t : ℕ) :
    ((step g)^[t] (initial g)).finished.length ≤ t := by
  induction t with
  | zero => simp [initial]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_finished_length g ((step g)^[t] (initial g))
    omega

end PlanarHom.PlanarityDepthFirstSearch
