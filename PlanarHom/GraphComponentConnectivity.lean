import PlanarHom.GraphComponentMachines
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Correctness of the explicit occurrence-by-occurrence component algorithm.
The returned parts form a genuine partition and precisely the classes of
reachability in the underlying undirected loopless support. -/
namespace PlanarHom.GraphComponentCode
open Complexity

/-- Loopless undirected support on the original numerical vertex indices. -/
def Adjacent (es : List Edge) (u v : ℕ) : Prop :=
  u ≠ v ∧ ∃ e ∈ es, (e.1=u ∧ e.2.1=v) ∨ (e.1=v ∧ e.2.1=u)

/-- Genuine finite-path reachability, not a label computed by the algorithm. -/
def Reach (es : List Edge) : ℕ → ℕ → Prop := Relation.ReflTransGen (Adjacent es)

def Together (ps : Parts) (u v : ℕ) : Prop := ∃ xs∈ps, u∈xs ∧ v∈xs

theorem adjacent_symm (es : List Edge) : Symmetric (Adjacent es) := by
  rintro u v ⟨hne,e,he,h⟩
  exact ⟨hne.symm,e,he,h.symm⟩

theorem reach_symm (es : List Edge) : Symmetric (Reach es) :=
  Relation.ReflTransGen.symmetric (adjacent_symm es)

theorem edge_reach (es : List Edge) (e : Edge) (he : e∈es) : Reach es e.1 e.2.1 := by
  by_cases h : e.1=e.2.1
  · rw [h]
    exact .refl
  · exact .single ⟨h,e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem fold_flatten_perm (ps : Parts) (es : List Edge) :
    (es.foldl merge ps).flatten.Perm ps.flatten := by
  induction es generalizing ps with
  | nil => exact .refl _
  | cons e es ih => exact (ih (merge ps e)).trans (GraphComponentMachines.merge_flatten_perm ps e)

@[simp] theorem initial_flatten (n : ℕ) : (initial n).flatten = (List.range n).reverse := by
  have h (xs : List ℕ) : (xs.map (fun v => [v])).flatten = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact h _

theorem flatten_filter_nonempty (ps : Parts) :
    (ps.filter (fun xs => !xs.isEmpty)).flatten = ps.flatten := by
  induction ps with
  | nil => rfl
  | cons xs ps ih => cases xs <;> simp_all

/-- Every original vertex occurs exactly once, with no omission of isolated
vertices and no silently inserted vertex. -/
theorem parts_flatten_perm (g : MixedCode) : (parts g).flatten.Perm (List.range g.vertices) := by
  rw [parts,flatten_filter_nonempty]
  exact (fold_flatten_perm _ _).trans (by simpa using (List.reverse_perm (List.range g.vertices)))

theorem parts_flatten_nodup (g : MixedCode) : (parts g).flatten.Nodup :=
  (parts_flatten_perm g).nodup_iff.mpr List.nodup_range

theorem part_nodup (g : MixedCode) (xs : List ℕ) (hx : xs∈parts g) : xs.Nodup :=
  (List.nodup_flatten.mp (parts_flatten_nodup g)).1 xs hx

theorem parts_pairwise_disjoint (g : MixedCode) : (parts g).Pairwise List.Disjoint :=
  (List.nodup_flatten.mp (parts_flatten_nodup g)).2

@[simp] theorem mem_parts_flatten (g : MixedCode) (v : ℕ) : v∈(parts g).flatten ↔ v<g.vertices := by
  rw [(parts_flatten_perm g).mem_iff,List.mem_range]

theorem part_vertex_lt (g : MixedCode) (xs : List ℕ) (hx : xs∈parts g) (v : ℕ) (hv : v∈xs) :
    v<g.vertices := (mem_parts_flatten g v).mp (List.mem_flatten.mpr ⟨xs,hx,hv⟩)

theorem vertex_mem_part (g : MixedCode) (v : ℕ) (hv : v<g.vertices) :
    ∃ xs∈parts g, v∈xs := List.mem_flatten.mp ((mem_parts_flatten g v).mpr hv)

theorem disjoint_parts_eq_of_common (ps : Parts) (hp : ps.Pairwise List.Disjoint)
    (xs ys : List ℕ) (hx : xs∈ps) (hy : ys∈ps) (v : ℕ) (hvx : v∈xs) (hvy : v∈ys) : xs=ys := by
  induction ps with
  | nil => simp at hx
  | cons zs ps ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with hxeq | hxt
    · subst xs
      rcases List.mem_cons.mp hy with hyeq | hyt
      · exact hyeq.symm
      · exact False.elim ((List.disjoint_left.mp (hhead ys hyt)) hvx hvy)
    · rcases List.mem_cons.mp hy with hyeq | hyt
      · subst ys
        exact False.elim ((List.disjoint_left.mp (hhead xs hxt)) hvy hvx)
      · exact ih htail hxt hyt

theorem part_eq_of_common (g : MixedCode) (xs ys : List ℕ) (hx : xs∈parts g) (hy : ys∈parts g)
    (v : ℕ) (hvx : v∈xs) (hvy : v∈ys) : xs=ys :=
  disjoint_parts_eq_of_common _ (parts_pairwise_disjoint g) xs ys hx hy v hvx hvy

theorem together_trans {ps : Parts} (hp : ps.Pairwise List.Disjoint) {u v w : ℕ}
    (h₁ : Together ps u v) (h₂ : Together ps v w) : Together ps u w := by
  obtain ⟨xs,hx,hu,hv⟩ := h₁
  obtain ⟨ys,hy,hv',hw⟩ := h₂
  have he := disjoint_parts_eq_of_common ps hp xs ys hx hy v hv hv'
  subst ys
  exact ⟨xs,hx,hu,hw⟩

/-- A part is wholly retained or wholly absorbed by the merged union. -/
theorem merge_contains_part (ps : Parts) (e : Edge) (xs : List ℕ) (hx : xs∈ps) :
    ∃ ys∈merge ps e, xs⊆ys := by
  by_cases ht : touches e xs = true
  · refine ⟨(ps.filter (touches e)).flatten,by simp [merge],?_⟩
    intro v hv
    exact List.mem_flatten.mpr ⟨xs,List.mem_filter.mpr ⟨hx,ht⟩,hv⟩
  · exact ⟨xs,by simp [merge,hx,ht],fun _ h => h⟩

theorem merge_preserves_together (ps : Parts) (e : Edge) {u v : ℕ}
    (h : Together ps u v) : Together (merge ps e) u v := by
  obtain ⟨xs,hx,hu,hv⟩ := h
  obtain ⟨ys,hy,hi⟩ := merge_contains_part ps e xs hx
  exact ⟨ys,hy,hi hu,hi hv⟩

theorem fold_preserves_together (ps : Parts) (es : List Edge) {u v : ℕ}
    (h : Together ps u v) : Together (es.foldl merge ps) u v := by
  induction es generalizing ps with
  | nil => exact h
  | cons e es ih => exact ih (merge ps e) (merge_preserves_together ps e h)

theorem merge_endpoint_together (ps : Parts) (e : Edge)
    (hu : e.1∈ps.flatten) (hv : e.2.1∈ps.flatten) : Together (merge ps e) e.1 e.2.1 := by
  obtain ⟨xs,hx,hu⟩ := List.mem_flatten.mp hu
  obtain ⟨ys,hy,hv⟩ := List.mem_flatten.mp hv
  refine ⟨(ps.filter (touches e)).flatten,by simp [merge],?_,?_⟩
  · exact List.mem_flatten.mpr ⟨xs,by simp [touches,hx,hu],hu⟩
  · exact List.mem_flatten.mpr ⟨ys,by simp [touches,hy,hv],hv⟩

theorem fold_endpoint_together (ps : Parts) (es : List Edge)
    (hvalid : ∀e∈es,e.1∈ps.flatten ∧ e.2.1∈ps.flatten) :
    ∀e∈es,Together (es.foldl merge ps) e.1 e.2.1 := by
  induction es generalizing ps with
  | nil => simp
  | cons e es ih =>
    intro a ha
    rcases List.mem_cons.mp ha with heq | ha
    · subst a
      exact fold_preserves_together _ es (merge_endpoint_together ps e
        (hvalid e (by simp)).1 (hvalid e (by simp)).2)
    · apply ih (merge ps e) _ a ha
      intro b hb
      have hp (v : ℕ) : v∈(merge ps e).flatten ↔ v∈ps.flatten :=
        (GraphComponentMachines.merge_flatten_perm ps e).mem_iff
      exact ⟨(hp _).mpr (hvalid b (by simp [hb])).1,(hp _).mpr (hvalid b (by simp [hb])).2⟩

theorem together_filter_nonempty (ps : Parts) (u v : ℕ) :
    Together (ps.filter (fun xs => !xs.isEmpty)) u v ↔ Together ps u v := by
  constructor
  · rintro ⟨xs,hx,hu,hv⟩
    exact ⟨xs,(List.mem_filter.mp hx).1,hu,hv⟩
  · rintro ⟨xs,hx,hu,hv⟩
    refine ⟨xs,List.mem_filter.mpr ⟨hx,?_⟩,hu,hv⟩
    have hne : xs≠[] := by intro h; simpa [h] using hu
    simpa using hne

theorem parts_endpoint_together {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (e : Edge) (he : e∈g.edges) :
    Together (parts g) e.1 e.2.1 := by
  apply (together_filter_nonempty _ _ _).mpr
  apply fold_endpoint_together _ _ _ e he
  intro a ha
  simpa using ⟨(hg.1 a ha).1,(hg.1 a ha).2.1⟩

/-- No binary occurrence crosses between distinct returned parts. -/
theorem part_edge_closed {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (xs : List ℕ) (hx : xs∈parts g)
    (e : Edge) (he : e∈g.edges) : e.1∈xs ↔ e.2.1∈xs := by
  obtain ⟨ys,hy,hu,hv⟩ := parts_endpoint_together g hg e he
  constructor
  · intro h
    have hxy := part_eq_of_common g xs ys hx hy e.1 h hu
    simpa [hxy] using hv
  · intro h
    have hxy := part_eq_of_common g xs ys hx hy e.2.1 h hv
    simpa [hxy] using hu

/-- Every pair of vertices in a part is joined by a path using actual input
occurrences; loop occurrences do not create spurious adjacency. -/
def Sound (es : List Edge) (ps : Parts) : Prop :=
  ∀xs∈ps, ∀u∈xs, ∀v∈xs, Reach es u v

theorem selected_reach_source (es : List Edge) (ps : Parts) (hs : Sound es ps)
    (e : Edge) (he : e∈es) (u : ℕ) (hu : u∈(ps.filter (touches e)).flatten) : Reach es u e.1 := by
  obtain ⟨xs,hxs,hu⟩ := List.mem_flatten.mp hu
  obtain ⟨hxs,ht⟩ := List.mem_filter.mp hxs
  have ht' : e.1∈xs ∨ e.2.1∈xs := by simpa [touches] using ht
  rcases ht' with h | h
  · exact hs xs hxs u hu e.1 h
  · exact (hs xs hxs u hu e.2.1 h).trans (reach_symm es (edge_reach es e he))

theorem merge_sound (es : List Edge) (ps : Parts) (hs : Sound es ps)
    (e : Edge) (he : e∈es) : Sound es (merge ps e) := by
  intro xs hxs u hu v hv
  rcases List.mem_cons.mp hxs with rfl | hxs
  · exact (selected_reach_source es ps hs e he u hu).trans
      (reach_symm es (selected_reach_source es ps hs e he v hv))
  · exact hs xs (List.mem_filter.mp hxs).1 u hu v hv

theorem fold_sound (all es : List Edge) (ps : Parts) (hs : Sound all ps)
    (he : es⊆all) : Sound all (es.foldl merge ps) := by
  induction es generalizing ps with
  | nil => exact hs
  | cons e es ih =>
    exact ih (merge ps e) (merge_sound all ps hs e (he (by simp)))
      (fun a ha => he (by simp [ha]))

theorem initial_sound (es : List Edge) (n : ℕ) : Sound es (initial n) := by
  intro xs hx u hu v hv
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  have hu' := List.mem_singleton.mp hu
  have hv' := List.mem_singleton.mp hv
  subst u; subst v
  exact .refl

theorem parts_sound (g : MixedCode) : Sound g.edges (parts g) := by
  intro xs hx
  exact fold_sound g.edges g.edges (initial g.vertices) (initial_sound _ _) (fun _ h => h)
    xs (List.mem_filter.mp hx).1

theorem together_reach (g : MixedCode) {u v : ℕ} (h : Together (parts g) u v) : Reach g.edges u v := by
  obtain ⟨xs,hxs,hu,hv⟩ := h
  exact parts_sound g xs hxs u hu v hv

theorem adjacent_together {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) {u v : ℕ} (h : Adjacent g.edges u v) :
    Together (parts g) u v := by
  obtain ⟨hne,e,he,h|h⟩ := h
  · simpa [←h.1,←h.2] using parts_endpoint_together g hg e he
  · obtain ⟨xs,hx,hu,hv⟩ := parts_endpoint_together g hg e he
    exact ⟨xs,hx,h.2 ▸ hv,h.1 ▸ hu⟩

theorem reach_together {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) {u v : ℕ} (hu : u<g.vertices)
    (h : Reach g.edges u v) : Together (parts g) u v := by
  induction h with
  | refl =>
    obtain ⟨xs,hx,hu⟩ := vertex_mem_part g u hu
    exact ⟨xs,hx,hu,hu⟩
  | tail hpath hadj ih =>
    exact together_trans (parts_pairwise_disjoint g) ih (adjacent_together g hg hadj)

/-- The computed partition is exactly the genuine support-path equivalence. -/
theorem together_iff_reach {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (u v : ℕ) (hu : u<g.vertices) :
    Together (parts g) u v ↔ Reach g.edges u v :=
  ⟨together_reach g,reach_together g hg hu⟩

theorem part_reach_closed {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (xs : List ℕ) (hx : xs∈parts g)
    {u v : ℕ} (hu : u∈xs) (h : Reach g.edges u v) : v∈xs := by
  obtain ⟨ys,hy,hu',hv⟩ := reach_together g hg (part_vertex_lt g xs hx u hu) h
  have hxy := part_eq_of_common g xs ys hx hy u hu hu'
  simpa [hxy] using hv

/-- Standard simple-graph support on the actual finite vertex set. -/
def support (g : MixedCode) : SimpleGraph (Fin g.vertices) where
  Adj u v := Adjacent g.edges u.val v.val
  symm := fun _ _ h => adjacent_symm g.edges h
  loopless := fun _ h => h.1 rfl

theorem adjacent_vertices_lt {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) {u v : ℕ} (h : Adjacent g.edges u v) :
    u<g.vertices ∧ v<g.vertices := by
  obtain ⟨_,e,he,h|h⟩ := h
  · exact ⟨h.1 ▸ (hg.1 e he).1,h.2 ▸ (hg.1 e he).2.1⟩
  · exact ⟨h.2 ▸ (hg.1 e he).2.1,h.1 ▸ (hg.1 e he).1⟩

theorem support_reachable {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) {u v : ℕ} (hu : u<g.vertices) (hv : v<g.vertices)
    (h : Reach g.edges u v) : (support g).Reachable ⟨u,hu⟩ ⟨v,hv⟩ := by
  induction h with
  | refl => exact .rfl
  | @tail v w hpath hadj ih =>
    have hmid := (adjacent_vertices_lt g hg hadj).1
    exact (ih hmid).trans (SimpleGraph.Adj.reachable (show (support g).Adj ⟨v,hmid⟩ ⟨w,hv⟩ from hadj))

theorem support_reachable_iff {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (u v : Fin g.vertices) :
    (support g).Reachable u v ↔ Reach g.edges u.val v.val := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift Fin.val (fun _ _ h => h)
      ((SimpleGraph.reachable_iff_reflTransGen u v).mp h)
  · exact support_reachable g hg u.isLt v.isLt

theorem extract_adjacent (g : MixedCode) (xs : List ℕ) {u v : ℕ}
    (hu : u∈xs) (hv : v∈xs) (h : Adjacent g.edges u v) :
    Adjacent (extract g xs).edges (xs.idxOf u) (xs.idxOf v) := by
  obtain ⟨hne,e,he,h|h⟩ := h
  all_goals
    refine ⟨fun hh => hne ((List.idxOf_inj hu hv).mp hh),
      (xs.idxOf e.1,xs.idxOf e.2.1,e.2.2),?_,?_⟩
  · apply List.mem_map.mpr
    exact ⟨e,List.mem_filter.mpr ⟨he,by simp [edgeInside,h.1,h.2,hu,hv]⟩,rfl⟩
  · exact Or.inl ⟨congrArg (List.idxOf · xs) h.1,congrArg (List.idxOf · xs) h.2⟩
  · apply List.mem_map.mpr
    exact ⟨e,List.mem_filter.mpr ⟨he,by simp [edgeInside,h.1,h.2,hu,hv]⟩,rfl⟩
  · exact Or.inr ⟨congrArg (List.idxOf · xs) h.1,congrArg (List.idxOf · xs) h.2⟩

theorem extract_reach {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (xs : List ℕ) (hx : xs∈parts g)
    {u v : ℕ} (hu : u∈xs) (h : Reach g.edges u v) :
    Reach (extract g xs).edges (xs.idxOf u) (xs.idxOf v) := by
  induction h with
  | refl => exact .refl
  | tail hpath hadj ih =>
    exact ih.tail (extract_adjacent g xs (part_reach_closed g hg xs hx hu hpath)
      (part_reach_closed g hg xs hx hu (hpath.tail hadj)) hadj)

/-- Each output is nonempty and connected in the standard loopless support,
with all original loops and repeated occurrences still present in its code. -/
theorem extract_connected {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (xs : List ℕ) (hx : xs∈parts g) :
    (support (extract g xs)).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_,?_⟩
  · intro u v
    have hu := List.get_mem xs u
    have hv := List.get_mem xs v
    have h := extract_reach g hg xs hx hu (parts_sound g xs hx _ hu _ hv)
    have hn := part_nodup g xs hx
    rw [List.get_idxOf hn u,List.get_idxOf hn v] at h
    exact support_reachable _ (extract_valid g hg xs) u.isLt v.isLt h
  · exact ⟨⟨0,List.length_pos_iff.mpr (parts_nonempty g xs hx)⟩⟩

theorem components_connected {binaryTypes unaryTypes : ℕ} (g : MixedCode)
    (hg : g.Valid binaryTypes unaryTypes) (c : MixedCode) (hc : c∈components g) :
    (support c).Connected := by
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hc
  exact extract_connected g hg xs hx

end PlanarHom.GraphComponentCode
