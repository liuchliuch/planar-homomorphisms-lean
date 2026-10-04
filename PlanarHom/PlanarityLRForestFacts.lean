import PlanarHom.PlanarityLRRawConstraints
import PlanarHom.PlanarityDepthFirstSearchSources

/-! NEW structural consequences of the actual verified DFS. No forest or
ancestor-order certificate is supplied by the caller. -/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PlanarityDepthFirstSearch

/-- Saved-path ancestry is transitive for valid vertices. -/
theorem ancestors_trans (g : MixedCode) {u v w : ℕ} (hw : w < g.vertices)
    (huv : u ∈ ancestors g v) (hvw : v ∈ ancestors g w) : u ∈ ancestors g w := by
  obtain ⟨pre,hpre⟩ := ancestors_suffix g hw hvw
  rw [hpre]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ huv)

/-- Every common-descendant ancestor set is linearly ordered by actual ancestry. -/
theorem ancestors_comparable (g : MixedCode) {u v w : ℕ} (hw : w < g.vertices)
    (hu : u ∈ ancestors g w) (hv : v ∈ ancestors g w) :
    u = v ∨ u ∈ ancestors g v ∨ v ∈ ancestors g u := by
  obtain ⟨pu,hpu⟩ := ancestors_suffix g hw hu
  obtain ⟨pv,hpv⟩ := ancestors_suffix g hw hv
  have hsu : (u::ancestors g u) <:+ ancestors g w := ⟨pu,hpu.symm⟩
  have hsv : (v::ancestors g v) <:+ ancestors g w := ⟨pv,hpv.symm⟩
  rcases List.suffix_or_suffix_of_suffix hsu hsv with h | h
  · have hh := h.subset (List.mem_cons_self (a := u) (l := ancestors g u))
    rcases List.mem_cons.mp hh with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hh := h.subset (List.mem_cons_self (a := v) (l := ancestors g v))
    rcases List.mem_cons.mp hh with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)

private theorem chain_nonempty {records : List Discovery} {path : List ℕ}
    (hc : Chain records path) (hne : path ≠ []) :
    ∃ r ∈ records, path = r.vertex::r.ancestors := by
  cases hc with
  | nil => exact (hne rfl).elim
  | cons r hr hpath => exact ⟨r,hr,rfl⟩

/-- The stored parent is the exact next link, not merely some ancestor. -/
theorem ancestors_parent (g : MixedCode) {v : ℕ} (hv : v < g.vertices) (hh : 0 < height g v) :
    ancestors g v = parentVertex g v :: ancestors g (parentVertex g v) := by
  have hc := (stackInvariant_iterate g (fuel g)).record_chains _ (discoveryAt_mem g hv).1
  change Chain (run g).discovered (ancestors g v) at hc
  have hex := chain_nonempty hc (List.ne_nil_of_length_pos hh)
  obtain ⟨r,hr,hpath⟩ := hex
  have hp : parentVertex g v = r.vertex := by simp [parentVertex,hpath]
  rw [hp,hpath]
  have he := discoveryAt_eq g hr
  simp only [ancestors,he]

theorem parent_height (g : MixedCode) {v : ℕ} (hv : v < g.vertices) (hh : 0 < height g v) :
    height g v = height g (parentVertex g v)+1 := by
  change (ancestors g v).length = (ancestors g (parentVertex g v)).length+1
  rw [ancestors_parent g hv hh,List.length_cons]

theorem edge_mem (g : MixedCode) {e : ℕ} (he : e < g.edges.length) : edge g e ∈ g.edges := by
  have hget : edge g e = g.edges[e] := by simp [edge,List.getD_eq_getElem?_getD,he]
  rw [hget]
  exact List.getElem_mem he

theorem edge_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) {e : ℕ} (he : e < g.edges.length) :
    (edge g e).1 < g.vertices ∧ (edge g e).2.1 < g.vertices := by
  have h := hg.1 (edge g e) (edge_mem g he)
  exact ⟨h.1,h.2.1⟩

theorem edge_adjacent (g : MixedCode) {e : ℕ} (he : e < g.edges.length) :
    Adjacent g (edge g e).1 (edge g e).2.1 := ⟨edge g e,edge_mem g he,Or.inl ⟨rfl,rfl⟩⟩

theorem lower_height_le_upper (g : MixedCode) (e : ℕ) : height g (lower g e) ≤ height g (upper g e) := by
  unfold lower upper
  split_ifs with h
  · exact h
  · omega

/-- The lower endpoint of any nonloop occurrence is a strict saved ancestor of
its upper endpoint in the actual computed forest. -/
theorem lower_ancestor_upper (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : e < g.edges.length) (hne : lower g e ≠ upper g e) :
    lower g e ∈ ancestors g (upper g e) := by
  have hv := edge_valid g hg he
  have hc := adjacent_ancestor_comparable g hv.1 hv.2 (edge_adjacent g he)
  unfold lower upper at hne ⊢
  split_ifs at hne ⊢ with h
  · rcases hc with hc | hc | hc
    · exact (hne hc).elim
    · exact hc
    · have hh := ancestors_height_lt g hv.1 hc
      omega
  · rcases hc with hc | hc | hc
    · exact (hne hc.symm).elim
    · have hh := ancestors_height_lt g hv.2 hc
      omega
    · exact hc

/-- Thus every computed strict back edge really returns to an ancestor. -/
theorem back_target_ancestor (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isBack g e = true) : target g e ∈ ancestors g (source g e) := by
  have hh : e < g.edges.length ∧ isTree g e = false ∧ source g e ≠ target g e := of_decide_eq_true he
  have hne : lower g e ≠ upper g e := by
    simpa only [source,target,hh.2.1,Bool.false_eq_true,if_false] using hh.2.2.symm
  simpa only [source,target,hh.2.1,Bool.false_eq_true,if_false] using lower_ancestor_upper g hg hh.1 hne

end PlanarHom.PlanarityLRRawConstraints
