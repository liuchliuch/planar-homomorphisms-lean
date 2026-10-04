import PlanarHom.PlanarityLRTreeInsertion

/-! NEW component roots and exact per-component tree insertion order, computed
from the original occurrence DFS. No connectivity or root oracle is supplied. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

def componentRoot (g : MixedCode) (v : ℕ) : ℕ := (rootPath g v).getD 0 v

theorem componentRoot_spec (g : MixedCode) {v : ℕ} (hv : v < g.vertices) :
    componentRoot g v < g.vertices ∧ Desc g (componentRoot g v) v ∧
      height g (componentRoot g v) = 0 := by
  have hd := rootPath_mem_desc g (rootPath_getD_mem g v 0 (Nat.zero_le _))
  exact ⟨desc_valid g hv hd,hd,rootPath_getD_height g hv (Nat.zero_le _)⟩

theorem zeroHeight_desc_eq (g : MixedCode) {u v : ℕ} (hv : v < g.vertices)
    (hu : height g u = 0) (hz : height g v = 0) (hd : Desc g u v) : u = v := by
  rcases hd with h | h
  · exact h
  · have := ancestors_height_lt g hv h
    omega

theorem componentRoot_eq_self (g : MixedCode) {v : ℕ} (hv : v < g.vertices)
    (hz : height g v = 0) : componentRoot g v = v :=
  zeroHeight_desc_eq g hv (componentRoot_spec g hv).2.2 hz (componentRoot_spec g hv).2.1

theorem componentRoot_eq_of_desc (g : MixedCode) {u v : ℕ} (hv : v < g.vertices)
    (hd : Desc g u v) : componentRoot g u = componentRoot g v := by
  have hu := desc_valid g hv hd
  have ru := componentRoot_spec g hu
  have rv := componentRoot_spec g hv
  have huv := desc_trans g hv ru.2.1 hd
  rcases desc_comparable g hv huv rv.2.1 with h | h
  · exact zeroHeight_desc_eq g rv.1 ru.2.2 rv.2.2 h
  · exact (zeroHeight_desc_eq g ru.1 rv.2.2 ru.2.2 h).symm

theorem tree_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : isTree g e = true) :
    componentRoot g (source g e) = componentRoot g (target g e) :=
  componentRoot_eq_of_desc g (source_target_valid g hg (of_decide_eq_true he).1).2
    (Or.inr (tree_source_ancestor g hg he))

def componentTreeOrder (g : MixedCode) (r : ℕ) : List ℕ :=
  (treeInsertionOrder g).filter (fun e => decide (componentRoot g (target g e) = r))

@[simp] theorem mem_componentTreeOrder (g : MixedCode) (r e : ℕ) :
    e ∈ componentTreeOrder g r ↔ isTree g e = true ∧ componentRoot g (target g e) = r := by
  simp [componentTreeOrder]

theorem componentTreeOrder_nodup (g : MixedCode) (r : ℕ) : (componentTreeOrder g r).Nodup :=
  (treeInsertionOrder_nodup g).filter _

theorem componentTreeOrder_sorted (g : MixedCode) (r : ℕ) :
    (componentTreeOrder g r).Pairwise (fun e f => targetHeight g e ≤ targetHeight g f) :=
  (treeInsertionOrder_sorted g).filter _

/-- Root-relative leaf insertion, including disconnected inputs and isolates. -/
theorem componentTreeOrder_source_available (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) {pre post : List ℕ} {e : ℕ}
    (horder : componentTreeOrder g r = pre ++ e::post) :
    source g e = r ∨ ∃ f ∈ pre, target g f = source g e := by
  have hem : e ∈ componentTreeOrder g r := by rw [horder]; simp
  have he := (mem_componentTreeOrder g r e).mp hem
  have hs := (source_target_valid g hg (of_decide_eq_true he.1).1).1
  by_cases hz : height g (source g e) = 0
  · left
    rw [← componentRoot_eq_self g hs hz,tree_componentRoot g hg he.1]
    exact he.2
  · right
    let f := parentEdge g (source g e)
    have hf := parentEdge_tree g hg hs (Nat.pos_of_ne_zero hz)
    have hmem : f ∈ pre ++ e::post := by
      rw [← horder,mem_componentTreeOrder]
      exact ⟨hf.1,by rw [hf.2.1,tree_componentRoot g hg he.1]; exact he.2⟩
    have hdepth := tree_height_succ g hg he.1
    have hsort := componentTreeOrder_sorted g r
    rw [horder] at hsort
    have htail := (List.pairwise_append.mp hsort).2.1
    rcases List.mem_append.mp hmem with hm | hm
    · exact ⟨f,hm,hf.2.1⟩
    · rcases List.mem_cons.mp hm with hm | hm
      · have hff := hf.2.1
        change target g f = source g e at hff
        rw [hm] at hff
        have := congrArg (height g) hff
        omega
      · have hle := (List.pairwise_cons.mp htail).1 f hm
        change height g (target g e) ≤ height g (target g f) at hle
        rw [hf.2.1] at hle
        omega

theorem componentTreeOrder_target_fresh (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (r : ℕ) {pre post : List ℕ} {e : ℕ}
    (horder : componentTreeOrder g r = pre ++ e::post) :
    target g e ≠ r ∧ ∀ f ∈ pre, target g e ≠ source g f ∧ target g e ≠ target g f := by
  have he := (mem_componentTreeOrder g r e).mp (by rw [horder]; simp)
  have ht := (source_target_valid g hg (of_decide_eq_true he.1).1).2
  have hpos := (tree_source_parent g hg he.1).2.2
  have hr : height g r = 0 := by rw [← he.2]; exact (componentRoot_spec g ht).2.2
  constructor
  · intro h
    rw [h,hr] at hpos
    omega
  · intro f hf
    have hft := ((mem_componentTreeOrder g r f).mp (by rw [horder]; exact List.mem_append_left _ hf)).1
    have hsort := componentTreeOrder_sorted g r
    have hn := componentTreeOrder_nodup g r
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
      exact hne (tree_target_injective g hg hft he.1 hh.symm)

end PlanarHom.PlanarityLRDirect
