import PlanarHom.PlanarityLRDirectedContourWords
import PlanarHom.PlanarityLRRootedTreeComponents

/-! NEW exact child/parent classification in the DFS-directed host rows. -/
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityDepthFirstSearch

theorem directed_child_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) (a : Dart (Fin g.edges.length))
    (hhost : ((dfsGraph g hg).dartPair a).1=v) :
    a.1∈dfsChildren g v ↔ isTree g a.1.val=true ∧ a.2=true := by
  rw [dfsChildren_mem]
  rcases a with ⟨f,b⟩
  cases b
  · have hh : target g f.val=v.val := congrArg Fin.val hhost
    constructor
    · intro h
      have hne := tree_height_succ g hg h.1
      rw [hh,h.2] at hne
      omega
    · intro h
      cases h.2
  · have hh : source g f.val=v.val := congrArg Fin.val hhost
    simp only [Bool.true_eq,true_and,and_true]
    exact ⟨fun h => h.1,fun h => ⟨h,hh⟩⟩

theorem directed_tree_at_target_cases (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (parent : Fin g.edges.length) (hp : isTree g parent.val=true)
    (a : Dart (Fin g.edges.length)) (ha : isTree g a.1.val=true)
    (hhost : ((dfsGraph g hg).dartPair a).1=dfsTarget g hg parent) :
    a=(parent,false) ∨ a.1∈dfsChildren g (dfsTarget g hg parent) := by
  rcases a with ⟨f,b⟩
  cases b
  · have hh : target g f.val=target g parent.val := congrArg Fin.val hhost
    have hf : f=parent := Fin.ext (tree_target_injective g hg ha hp hh)
    exact Or.inl (by simp only [hf])
  · exact Or.inr ((directed_child_iff g hg _ _ hhost).mpr ⟨ha,rfl⟩)

theorem directed_tree_at_root_child (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : Fin g.vertices) (hv : height g v.val=0) (a : Dart (Fin g.edges.length))
    (ha : isTree g a.1.val=true) (hhost : ((dfsGraph g hg).dartPair a).1=v) :
    a.1∈dfsChildren g v := by
  apply (directed_child_iff g hg v a hhost).mpr
  refine ⟨ha,?_⟩
  rcases a with ⟨f,b⟩
  cases b
  · have hh : target g f.val=v.val := congrArg Fin.val hhost
    have hhpos := (tree_source_parent g hg ha).2.2
    rw [hh,hv] at hhpos
    omega
  · rfl

theorem parent_not_dfsChildren (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (parent : Fin g.edges.length) (hp : isTree g parent.val=true) :
    parent∉dfsChildren g (dfsTarget g hg parent) := by
  intro hm
  have hh := ((dfsChildren_mem g _ parent).mp hm).2
  have hd := tree_height_succ g hg hp
  change source g parent.val=target g parent.val at hh
  rw [hh] at hd
  omega

end PlanarHom.PlanarityLRRealization
