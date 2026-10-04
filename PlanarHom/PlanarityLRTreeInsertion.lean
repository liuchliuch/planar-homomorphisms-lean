import PlanarHom.PlanarityLRBranchPaths

/-! NEW deterministic parent-before-child insertion order for the actual DFS forest.
This is the combinatorial leaf-extension interface for geometric tree cuts. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

def treeDepthLE (g : MixedCode) (e f : ℕ) : Bool :=
  decide (targetHeight g e < targetHeight g f ∨ targetHeight g e = targetHeight g f ∧ e ≤ f)

def treeInsertionOrder (g : MixedCode) : List ℕ :=
  ((List.range g.edges.length).filter (isTree g)).mergeSort (treeDepthLE g)

theorem treeDepthLE_trans (g : MixedCode) (a b c : ℕ)
    (hab : treeDepthLE g a b = true) (hbc : treeDepthLE g b c = true) : treeDepthLE g a c = true := by
  simp only [treeDepthLE,decide_eq_true_eq] at *
  omega

theorem treeDepthLE_total (g : MixedCode) (a b : ℕ) : (treeDepthLE g a b || treeDepthLE g b a) = true := by
  simp only [treeDepthLE,Bool.or_eq_true,decide_eq_true_eq]
  omega

theorem treeInsertionOrder_perm (g : MixedCode) :
    (treeInsertionOrder g).Perm ((List.range g.edges.length).filter (isTree g)) :=
  List.mergeSort_perm _ _

@[simp] theorem mem_treeInsertionOrder (g : MixedCode) (e : ℕ) :
    e ∈ treeInsertionOrder g ↔ isTree g e = true := by
  rw [(treeInsertionOrder_perm g).mem_iff,List.mem_filter,List.mem_range]
  exact ⟨And.right,fun h => ⟨(of_decide_eq_true h).1,h⟩⟩

theorem treeInsertionOrder_nodup (g : MixedCode) : (treeInsertionOrder g).Nodup :=
  (treeInsertionOrder_perm g).symm.nodup (List.nodup_range.filter _)

theorem treeInsertionOrder_sorted (g : MixedCode) :
    (treeInsertionOrder g).Pairwise (fun e f => targetHeight g e ≤ targetHeight g f) := by
  have h := List.sorted_mergeSort (treeDepthLE_trans g) (treeDepthLE_total g)
    ((List.range g.edges.length).filter (isTree g))
  apply h.imp
  intro e f h
  simp only [treeDepthLE,decide_eq_true_eq] at h
  omega

theorem tree_target_injective (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e f : ℕ} (he : isTree g e = true) (hf : isTree g f = true)
    (ht : target g e = target g f) : e = f := by
  have h₁ := (tree_source_parent g hg he).2.1
  have h₂ := (tree_source_parent g hg hf).2.1
  rw [ht] at h₁
  exact h₁.symm.trans h₂

/-- Every inserted tree edge starts at a root or at the target of an already
inserted occurrence. This is derived from raw-code DFS, not a tree certificate. -/
theorem treeInsertion_source_available (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {pre post : List ℕ} {e : ℕ} (horder : treeInsertionOrder g = pre ++ e::post) :
    height g (source g e) = 0 ∨ ∃ f ∈ pre, target g f = source g e := by
  have he : isTree g e = true := (mem_treeInsertionOrder g e).mp (by rw [horder]; simp)
  by_cases hroot : height g (source g e) = 0
  · exact Or.inl hroot
  · right
    let f := parentEdge g (source g e)
    have hsource := (source_target_valid g hg (of_decide_eq_true he).1).1
    have hf := parentEdge_tree g hg hsource (Nat.pos_of_ne_zero hroot)
    have hmem : f ∈ pre ++ e::post := by
      rw [← horder]
      exact (mem_treeInsertionOrder g f).mpr hf.1
    have hdepth := tree_height_succ g hg he
    have hsort := treeInsertionOrder_sorted g
    rw [horder] at hsort
    have htail := (List.pairwise_append.mp hsort).2.1
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact ⟨f,hmem,hf.2.1⟩
    · rcases List.mem_cons.mp hmem with hmem | hmem
      · have hff := hf.2.1
        change target g f = source g e at hff
        rw [hmem] at hff
        have := congrArg (height g) hff
        omega
      · have hle := (List.pairwise_cons.mp htail).1 f hmem
        change height g (target g e) ≤ height g (target g f) at hle
        rw [hf.2.1] at hle
        omega

/-- The new target is fresh against every prior endpoint and every root. -/
theorem treeInsertion_target_fresh (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {pre post : List ℕ} {e : ℕ} (horder : treeInsertionOrder g = pre ++ e::post) :
    0 < height g (target g e) ∧
      ∀ f ∈ pre, target g e ≠ source g f ∧ target g e ≠ target g f := by
  have he : isTree g e = true := (mem_treeInsertionOrder g e).mp (by rw [horder]; simp)
  refine ⟨(tree_source_parent g hg he).2.2,?_⟩
  intro f hf
  have hft : isTree g f = true := (mem_treeInsertionOrder g f).mp (by rw [horder]; exact List.mem_append_left _ hf)
  have hsort := treeInsertionOrder_sorted g
  have hn := treeInsertionOrder_nodup g
  rw [horder] at hsort hn
  have hle := (List.pairwise_append.mp hsort).2.2 f hf e (List.mem_cons_self ..)
  have hne : f ≠ e := (List.nodup_append.mp hn).2.2 f hf e (List.mem_cons_self ..)
  have hdepth := tree_height_succ g hg hft
  constructor
  · intro hh
    have hd := congrArg (height g) hh
    change height g (target g f) ≤ height g (target g e) at hle
    omega
  · intro hh
    exact hne (tree_target_injective g hg hft he hh.symm)

end PlanarHom.PlanarityLRDirect
