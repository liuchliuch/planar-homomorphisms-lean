import PlanarHom.PlanarityLRDirectedExcursions

/-! NEW exact recursive child/singleton expansion for the actual directed contour. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

def directedNodeBlock (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (parent : Fin g.edges.length)
    (a : Dart (Fin g.edges.length)) : List (Dart (Fin g.edges.length)) :=
  if a.1=parent then [] else if isTree g a.1.val then directedSubtreePorts g hg rows a.1 else [a]

theorem directed_node_excursion_block (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (parent : Fin g.edges.length) (hp : isTree g parent.val=true)
    (a : Dart (Fin g.edges.length)) (hhost : ((dfsGraph g hg).dartPair a).1=dfsTarget g hg parent) :
    (directedExcursionWord g hg rows a).filter (directedSubtreeKeep g parent)=
      directedNodeBlock g hg rows parent a := by
  by_cases ha : isTree g a.1.val=true
  · rcases directed_tree_at_target_cases g hg parent hp a ha hhost with rfl | hc
    · rw [directedExcursionWord_reverse g hg rows parent hp]
      simp [directedNodeBlock]
    · have hbit := ((directed_child_iff g hg _ a hhost).mp hc).2
      have heq : a=(a.1,true) := Prod.ext rfl hbit
      have hne : a.1≠parent := fun hh => parent_not_dfsChildren g hg parent hp (hh ▸ hc)
      rw [directedNodeBlock,if_neg hne,if_pos ha,
        ←filter_directedSubtreeKeep_ports g hg parent,
        heq,directedExcursionWord_forward g hg rows a.1 ha]
      exact directedSubtreePorts_child_filter g hg rows parent a.1 hc
  · have hf := Bool.eq_false_iff.mpr ha
    have hne : a.1≠parent := by intro h; exact ha (h ▸ hp)
    have hkeep : directedSubtreeKeep g parent a=true := by
      apply (directedSubtreeKeep_eq_true g hg parent a).mpr
      refine ⟨hf,Or.inl ?_⟩
      exact (congrArg Fin.val hhost).symm
    rw [directedExcursionWord_nonTree g hg rows a hf]
    simp [directedNodeBlock,hne,hf,hkeep]

theorem directedSubtreePorts_eq_afterParent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    directedSubtreePorts g hg rows e=
      afterParentInputs (rows.row (dfsTarget g hg e)) (e,false) (directedNodeBlock g hg rows e) := by
  rw [directedSubtreePorts_reverse_start g hg rows e he,
    directed_contour_filter_eq_afterParentInputs g hg rows (e,false) (directedSubtreeKeep g e)
      (directedExcursionWord_reverse g hg rows e he)]
  change afterParentInputs (rows.row (dfsTarget g hg e)) (e,false) _=_
  unfold afterParentInputs
  congr 1
  · apply List.flatMap_congr
    intro a ha
    exact directed_node_excursion_block g hg rows e he a
      ((rows.mem _ _).mp (List.mem_of_mem_drop ha))
  · apply List.flatMap_congr
    intro a ha
    exact directed_node_excursion_block g hg rows e he a
      ((rows.mem _ _).mp (List.mem_of_mem_take ha))

end PlanarHom.PlanarityLRRealization
