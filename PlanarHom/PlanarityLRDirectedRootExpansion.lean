import PlanarHom.PlanarityLRDirectedNodeExpansion

/-! NEW exact root-row expansion, including isolated vertices with empty rows. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityDepthFirstSearch FinitePermutationReturnWords

def directedRootBlock (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length)) : List (Dart (Fin g.edges.length)) :=
  if isTree g a.1.val then directedSubtreePorts g hg rows a.1 else [a]

def directedRootPorts (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) : List (Dart (Fin g.edges.length)) :=
  ((rows.row r).head?.map (contourPortWord rows (fun e=> isTree g e.val))).getD []

theorem directed_root_excursion_block (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (a : Dart (Fin g.edges.length)) (hhost : ((dfsGraph g hg).dartPair a).1=r) :
    (directedExcursionWord g hg rows a).filter (fun b=> !(isTree g b.1.val))=
      directedRootBlock g hg rows a := by
  by_cases ha : isTree g a.1.val=true
  · have hc := directed_tree_at_root_child g hg r hr a ha hhost
    have hbit := ((directed_child_iff g hg r a hhost).mp hc).2
    have heq : a=(a.1,true) := Prod.ext rfl hbit
    rw [directedRootBlock,if_pos ha,heq,directedExcursionWord_forward g hg rows a.1 ha]
  · have hf := Bool.eq_false_iff.mpr ha
    rw [directedExcursionWord_nonTree g hg rows a hf]
    simp [directedRootBlock,hf]

theorem directedRootPorts_eq_row_expansion (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0) :
    directedRootPorts g hg rows r=(rows.row r).flatMap (directedRootBlock g hg rows) := by
  cases hrow : rows.row r with
  | nil => simp [directedRootPorts,hrow]
  | cons a tail =>
      have ha : a∈rows.row r := by simp [hrow]
      have hhost := (rows.mem r a).mp ha
      have hexp := directed_contour_word_eq_row_expansion g hg rows a
      rw [hhost,hrow] at hexp
      simp only [List.idxOf_cons_self,List.rotate_zero] at hexp
      simp only [directedRootPorts,hrow,List.head?_cons,Option.map_some,Option.getD_some]
      change (orbitPrefix _ _ a).filter (fun b=> !(isTree g b.1.val))=_
      rw [hexp,List.filter_flatMap]
      apply List.flatMap_congr
      intro b hb
      exact directed_root_excursion_block g hg rows r hr b ((rows.mem r b).mp (hrow ▸ hb))

end PlanarHom.PlanarityLRRealization
