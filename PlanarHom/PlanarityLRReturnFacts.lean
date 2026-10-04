import PlanarHom.PlanarityLRForestFacts

/-! NEW correctness of literal tree/back orientation and lowpoint primitives
against the actual DFS parent chains. -/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PlanarityDepthFirstSearch

theorem lower_upper_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : e < g.edges.length) : lower g e < g.vertices ∧ upper g e < g.vertices := by
  have hv := edge_valid g hg he
  unfold lower upper
  split_ifs
  · exact hv
  · exact ⟨hv.2,hv.1⟩

theorem source_target_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : e < g.edges.length) : source g e < g.vertices ∧ target g e < g.vertices := by
  have hv := lower_upper_valid g hg he
  unfold source target
  split_ifs
  · exact hv
  · exact ⟨hv.2,hv.1⟩

/-- A computed tree occurrence is literally the parent occurrence of its target. -/
theorem tree_source_parent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isTree g e = true) :
    source g e = parentVertex g (target g e) ∧ parentEdge g (target g e) = e ∧
      0 < height g (target g e) := by
  have hh : e < g.edges.length ∧ 0 < height g (upper g e) ∧ parentEdge g (upper g e) = e :=
    of_decide_eq_true he
  let t := upper g e
  have ht : t < g.vertices := (lower_upper_valid g hg hh.1).2
  have hroot : 0 < height g t := hh.2.1
  have hparent : parentEdge g t = e := hh.2.2
  obtain ⟨c,hc,hends⟩ := neighbours_occurrence g _ (parentEdge_incidence g ht hroot)
  rw [hparent] at hc
  have hEdge : edge g e = c := by simp only [edge,List.getD_eq_getElem?_getD,hc,Option.getD_some]
  have hp := parentVertex_height_lt g ht hroot
  have hlo : lower g e = parentVertex g t := by
    rcases hends with ⟨hs,hd⟩ | ⟨hs,hd⟩
    · simp [lower,hEdge,hs,hd,le_of_lt hp]
    · simp [lower,hEdge,hs,hd,not_le_of_gt hp]
  simpa only [source,target,he,if_true] using ⟨hlo,hparent,hroot⟩

theorem tree_height_succ (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isTree g e = true) : height g (target g e) = height g (source g e)+1 := by
  have ht := tree_source_parent g hg he
  have hvalid := (source_target_valid g hg (of_decide_eq_true he).1).2
  rw [ht.1]
  exact parent_height g hvalid ht.2.2

theorem tree_source_ancestor (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isTree g e = true) : source g e ∈ ancestors g (target g e) := by
  have ht := tree_source_parent g hg he
  have hvalid := (source_target_valid g hg (of_decide_eq_true he).1).2
  rw [ht.1]
  exact parentVertex_ancestor g hvalid ht.2.2

theorem back_height_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isBack g e = true) : targetHeight g e < height g (source g e) :=
  ancestors_height_lt g (source_target_valid g hg (of_decide_eq_true he).1).1 (back_target_ancestor g hg he)

theorem mem_returns_back (g : MixedCode) (e : ℕ) {b : ℕ} (hb : b ∈ returns g e) : isBack g b = true := by
  unfold returns at hb
  split_ifs at hb with he hback
  · have h := (List.mem_filter.mp hb).2
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  · have heq : b = e := by simpa using hb
    exact heq ▸ hback
  · simp at hb

/-- All returned back edges originate at the source or in its actual descendant subtree. -/
theorem returns_source_descendant (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : ℕ) {b : ℕ} (hb : b ∈ returns g e) :
    source g e = source g b ∨ source g e ∈ ancestors g (source g b) := by
  unfold returns at hb
  split_ifs at hb with ht he
  · have hm := (List.mem_filter.mp hb).2
    simp only [Bool.and_eq_true] at hm
    have ha : target g e = source g b ∨ target g e ∈ ancestors g (source g b) :=
      of_decide_eq_true hm.1.2
    have hs := tree_source_ancestor g hg ht
    right
    rcases ha with ha | ha
    · simpa only [ha] using hs
    · exact ancestors_trans g (source_target_valid g hg
        (of_decide_eq_true hm.1.1).1).1 hs ha
  · have heq : b = e := by simpa using hb
    exact Or.inl (congrArg (source g) heq.symm)
  · simp at hb

private theorem le_foldl_min_iff (xs : List ℕ) (start k : ℕ) :
    k ≤ xs.foldl min start ↔ k ≤ start ∧ ∀ x ∈ xs, k ≤ x := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.le_min, List.mem_cons,forall_eq_or_imp]
    exact and_assoc

/-- A lowpoint lower bound means a lower bound on every literal return target
and on the source-depth default. -/
theorem le_lowpoint_iff (g : MixedCode) (e k : ℕ) :
    k ≤ lowpoint g e ↔ k ≤ height g (source g e) ∧ ∀ b ∈ returns g e, k ≤ targetHeight g b := by
  rw [lowpoint,le_foldl_min_iff]
  simp only [List.forall_mem_map]

theorem lowpoint_le_source (g : MixedCode) (e : ℕ) : lowpoint g e ≤ height g (source g e) :=
  ((le_lowpoint_iff g e _).mp le_rfl).1

theorem lowpoint_le_return (g : MixedCode) (e : ℕ) {b : ℕ} (hb : b ∈ returns g e) :
    lowpoint g e ≤ targetHeight g b := ((le_lowpoint_iff g e _).mp le_rfl).2 b hb

theorem lowpoint_back (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isBack g e = true) : lowpoint g e = targetHeight g e := by
  have ht : isTree g e = false := (of_decide_eq_true he).2.1
  simp only [lowpoint,returns,ht,Bool.false_eq_true,if_false,he,if_true,List.map_singleton,
    List.foldl_cons,List.foldl_nil]
  exact min_eq_right (back_height_lt g hg he).le

end PlanarHom.PlanarityLRRawConstraints
