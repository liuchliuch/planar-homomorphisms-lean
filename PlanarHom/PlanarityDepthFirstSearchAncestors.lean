import PlanarHom.PlanarityDepthFirstSearchCoverage

/-! NEW reconstruction. Every actual undirected edge has ancestor-comparable
endpoints in the computed DFS forest. This excludes cross edges using the
proved finished-neighbour invariant, without assuming a DFS certificate. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

def SavedAncestor (s : State) (u v : ℕ) : Prop :=
  ∃r∈s.discovered,r.vertex=v ∧ u∈r.ancestors

def EdgeComparable (g : MixedCode) (s : State) : Prop :=
  ∀u∈seen s,∀v∈seen s,Adjacent g u v → u=v ∨ SavedAncestor s u v ∨ SavedAncestor s v u

 theorem edgeComparable_initial (g : MixedCode) : EdgeComparable g (initial g) := by
  simp [EdgeComparable,seen,initial]

 theorem fresh_neighbour_active (g : MixedCode) (s : State)
    (hs : StackInvariant g s) (hc : CoverageInvariant g s)
    {u v : ℕ} (hu : u<g.vertices) (hun : u∉seen s) (hv : v∈seen s)
    (hadj : Adjacent g u v) : v∈s.active := by
  rcases hs.seen_split v hv with ha | hf
  · exact ha
  · obtain ⟨k,hk⟩ := adjacent_neighbours g (adjacent_symm g hadj)
    exact (hun (hc.finished v hf (u,k) hk hu)).elim

 theorem edgeComparable_step (g : MixedCode) (s : State)
    (hs : StackInvariant g s) (hc : CoverageInvariant g s) (he : EdgeComparable g s) :
    EdgeComparable g (step g s) := by
  cases hw : s.work with
  | nil => simpa [step,hw] using he
  | cons t rest =>
    cases ht : t.enter with
    | false => simpa [step,hw,ht,EdgeComparable,SavedAncestor,seen] using he
    | true =>
      by_cases hn : t.vertex<g.vertices ∧ t.vertex∉seen s
      · simp only [step,hw,ht,hn,↓reduceIte]
        intro u hu v hv ha
        change u∈t.vertex::seen s at hu
        change v∈t.vertex::seen s at hv
        rcases List.mem_cons.mp hu with rfl | hu
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨⟨t.vertex,t.edge,s.active⟩,List.mem_cons_self,rfl,
              fresh_neighbour_active g s hs hc hn.1 hn.2 hv ha⟩)
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr (Or.inl ⟨⟨t.vertex,t.edge,s.active⟩,List.mem_cons_self,rfl,
              fresh_neighbour_active g s hs hc hn.1 hn.2 hu (adjacent_symm g ha)⟩)
          · rcases he u hu v hv ha with huv | ⟨r,hr,heq,hm⟩ | ⟨r,hr,heq,hm⟩
            · exact Or.inl huv
            · exact Or.inr (Or.inl ⟨r,List.mem_cons_of_mem _ hr,heq,hm⟩)
            · exact Or.inr (Or.inr ⟨r,List.mem_cons_of_mem _ hr,heq,hm⟩)
      · simpa only [step,hw,ht,hn,↓reduceIte] using he

 theorem edgeComparable_iterate (g : MixedCode) (n : ℕ) :
    EdgeComparable g ((step g)^[n] (initial g)) := by
  induction n with
  | zero => exact edgeComparable_initial g
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact edgeComparable_step g _ (stackInvariant_iterate g n) (coverageInvariant_iterate g n) ih

 theorem discoveryAt_mem (g : MixedCode) {v : ℕ} (hv : v<g.vertices) :
    discoveryAt g v ∈ (run g).discovered ∧ (discoveryAt g v).vertex=v := by
  have hm := all_vertices_discovered g hv
  obtain ⟨r,hr,hrv⟩ := List.mem_map.mp hm
  cases hf : (run g).discovered.find? (fun d=>d.vertex==v) with
  | none =>
    have hh := List.find?_eq_none.mp hf r hr
    simp [hrv] at hh
  | some d =>
    have hd := List.mem_of_find?_eq_some hf
    have hv := List.find?_some hf
    exact ⟨by simpa [discoveryAt,hf] using hd,by simpa [discoveryAt,hf] using hv⟩

 theorem discoveryAt_eq (g : MixedCode) {r : Discovery} (hr : r∈(run g).discovered) :
    discoveryAt g r.vertex=r := by
  have hv := (run_goodSeen g).2 r.vertex (List.mem_map.mpr ⟨r,hr,rfl⟩)
  obtain ⟨hd,hv'⟩ := discoveryAt_mem g hv
  exact List.inj_on_of_nodup_map (run_goodSeen g).1 hd hr hv'

 theorem Chain.member_suffix {records : List Discovery} {path : List ℕ} (h : Chain records path)
    {u : ℕ} (hu : u∈path) :
    ∃r∈records,r.vertex=u ∧ ∃pre,path=pre++u::r.ancestors := by
  induction h with
  | nil => simp at hu
  | cons r hr hp ih =>
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨r,hr,rfl,[],rfl⟩
    · obtain ⟨s,hs,hsu,pre,hpre⟩ := ih hu
      exact ⟨s,hs,hsu,r.vertex::pre,by simp [hpre]⟩

/-- Saved ancestor lists are actual compatible parent-chain suffixes. -/
 theorem ancestors_suffix (g : MixedCode) {u v : ℕ} (hv : v<g.vertices)
    (hu : u∈ancestors g v) : ∃pre,ancestors g v=pre++u::ancestors g u := by
  obtain ⟨hr,hrv⟩ := discoveryAt_mem g hv
  have hc := (stackInvariant_iterate g (fuel g)).record_chains _ hr
  obtain ⟨r,hr',hru,pre,hpre⟩ := hc.member_suffix hu
  have he := discoveryAt_eq g hr'
  rw [hru] at he
  refine ⟨pre,?_⟩
  simpa only [ancestors,he] using hpre

 theorem ancestors_height_lt (g : MixedCode) {u v : ℕ} (hv : v<g.vertices)
    (hu : u∈ancestors g v) : height g u < height g v := by
  obtain ⟨pre,hpre⟩ := ancestors_suffix g hv hu
  unfold height
  rw [hpre,List.length_append,List.length_cons]
  omega

/-- The computed traversal has the genuine undirected DFS no-cross-edge property. -/
 theorem adjacent_ancestor_comparable (g : MixedCode) {u v : ℕ}
    (hu : u<g.vertices) (hv : v<g.vertices) (ha : Adjacent g u v) :
    u=v ∨ u∈ancestors g v ∨ v∈ancestors g u := by
  rcases edgeComparable_iterate g (fuel g) u (all_vertices_discovered g hu)
    v (all_vertices_discovered g hv) ha with he | ⟨r,hr,hrv,hm⟩ | ⟨r,hr,hru,hm⟩
  · exact Or.inl he
  · right; left
    have he := discoveryAt_eq g hr
    simpa only [ancestors,←hrv,he] using hm
  · right; right
    have he := discoveryAt_eq g hr
    simpa only [ancestors,←hru,he] using hm

end PlanarHom.PlanarityDepthFirstSearch
