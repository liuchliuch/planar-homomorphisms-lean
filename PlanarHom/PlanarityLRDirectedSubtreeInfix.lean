import PlanarHom.PlanarityLRDirectedRootExpansion
import Mathlib.Data.List.Infix

/-! NEW literal contiguous occurrence-port blocks inside each computed root word. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityDepthFirstSearch FinitePermutationReturnWords

theorem block_infix_afterParentInputs {A : Type*} [DecidableEq A]
    (row : List A) (parent a : A) (block : A→List A)
    (hp : parent∈row) (ha : a∈row) (hne : a≠parent) :
    block a <:+: afterParentInputs row parent block := by
  have hi := List.idxOf_lt_length_iff.mpr hp
  have hs := List.take_append_drop (row.idxOf parent) row
  rw [List.drop_eq_getElem_cons hi,List.getElem_idxOf hi] at hs
  have hm : a∈row.drop (row.idxOf parent+1) ++ row.take (row.idxOf parent) := by
    rw [←hs,List.mem_append,List.mem_cons] at ha
    rcases ha with ha | ha | ha
    · exact List.mem_append_right _ ha
    · exact (hne ha).elim
    · exact List.mem_append_left _ ha
  simpa only [List.flatMap_append,afterParentInputs] using List.infix_flatMap_of_mem hm block

theorem directedSubtreePorts_infix_parent (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (parent child : Fin g.edges.length)
    (hp : isTree g parent.val=true) (hc : child∈dfsChildren g (dfsTarget g hg parent)) :
    directedSubtreePorts g hg rows child <:+: directedSubtreePorts g hg rows parent := by
  have hs := (dfsChildren_mem g _ child).mp hc
  have hm : (child,true)∈rows.row (dfsTarget g hg parent) := by
    apply (rows.mem _ _).mpr
    exact Fin.ext hs.2
  have hpRow : (parent,false)∈rows.row (dfsTarget g hg parent) := (rows.mem _ _).mpr rfl
  have hne : child≠parent := fun hh=>parent_not_dfsChildren g hg parent hp (hh ▸ hc)
  have hh := block_infix_afterParentInputs (rows.row (dfsTarget g hg parent)) (parent,false) (child,true)
    (directedNodeBlock g hg rows parent) hpRow hm (by simp)
  rw [←directedSubtreePorts_eq_afterParent g hg rows parent hp] at hh
  simpa only [directedNodeBlock,if_neg hne,if_pos hs.1] using hh

theorem directedSubtreePorts_infix_root_child (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (e : Fin g.edges.length) (he : isTree g e.val=true) (hs : source g e.val=r.val) :
    directedSubtreePorts g hg rows e <:+: directedRootPorts g hg rows r := by
  rw [directedRootPorts_eq_row_expansion g hg rows r hr]
  have hm : (e,true)∈rows.row r := (rows.mem _ _).mpr (Fin.ext hs)
  simpa only [directedRootBlock,if_pos he] using List.infix_flatMap_of_mem hm (directedRootBlock g hg rows)

theorem directedSubtreePorts_infix_root (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (e : Fin g.edges.length) (he : isTree g e.val=true)
    (hroot : componentRoot g (source g e.val)=r.val) :
    directedSubtreePorts g hg rows e <:+: directedRootPorts g hg rows r := by
  suffices ∀n,∀e : Fin g.edges.length, isTree g e.val=true → height g (source g e.val)=n →
      componentRoot g (source g e.val)=r.val →
      directedSubtreePorts g hg rows e <:+: directedRootPorts g hg rows r from this _ e he rfl hroot
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro e he hn hroot
      have hv := (source_target_valid g hg e.isLt).1
      by_cases hz : height g (source g e.val)=0
      · apply directedSubtreePorts_infix_root_child g hg rows r hr e he
        exact (componentRoot_eq_self g hv hz).symm.trans hroot
      · have hpos := Nat.pos_of_ne_zero hz
        let p : Fin g.edges.length := ⟨parentEdge g (source g e.val),parentEdge_lt g hv hpos⟩
        have hp := parentEdge_tree g hg hv hpos
        have hpt : target g p.val=source g e.val := hp.2.1
        have hchild : e∈dfsChildren g (dfsTarget g hg p) :=
          (dfsChildren_mem g _ e).mpr ⟨he,hpt.symm⟩
        apply (directedSubtreePorts_infix_parent g hg rows p e hp.1 hchild).trans
        have hd : height g (target g p.val)=height g (source g p.val)+1 := tree_height_succ g hg hp.1
        rw [hpt] at hd
        have hlt : height g (source g p.val)<n := by omega
        have hpRoot : componentRoot g (source g p.val)=r.val :=
          (tree_componentRoot g hg hp.1).trans ((congrArg (componentRoot g) hpt).trans hroot)
        exact ih (height g (source g p.val)) hlt p hp.1 rfl hpRoot

end PlanarHom.PlanarityLRRealization
