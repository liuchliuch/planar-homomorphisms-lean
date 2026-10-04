import PlanarHom.PlanarityLRVisitRanks

/-! NEW concrete local-rank keys for the actual DFS contour. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode

 def visitTreeWord (g : MixedCode) (bits : List Bool) (v : ℕ) : List ℕ :=
   ((rootPath g v).drop 1).map (fun w=>
     localRank g bits (parentVertex g w) (outward g (parentEdge g w)))
 def contourKey (g : MixedCode) (bits : List Bool) (a : Dart) : List ℕ :=
   visitTreeWord g bits (host g a)++[localRank g bits (host g a) a]
 def rawContourStep (g : MixedCode) (bits : List Bool) (a : Dart) : Dart :=
   directRotation g bits (if isTree g a.1 then reverse a else a)
 def RootFirst (g : MixedCode) (bits : List Bool) (a : Dart) : Prop :=
   height g (host g a)=0 ∧ (directRow g bits (host g a)).head?=some a

 theorem visitTreeWord_parent (g : MixedCode) (bits : List Bool) {v : ℕ}
    (hv : v<g.vertices) (hh : 0<height g v) :
    visitTreeWord g bits v=visitTreeWord g bits (parentVertex g v)++
      [localRank g bits (parentVertex g v) (outward g (parentEdge g v))] := by
  have hl : 1≤(rootPath g (parentVertex g v)).length:=by simp
  simp only [visitTreeWord,rootPath_parent g hv hh,List.drop_append_of_le_length hl,
    List.map_append,List.map_singleton]

 theorem visitTreeWord_tree_target (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isTree g e=true) :
    visitTreeWord g bits (target g e)=visitTreeWord g bits (source g e)++
      [localRank g bits (source g e) (outward g e)] := by
  have hp:=tree_source_parent g hg he
  rw [visitTreeWord_parent g bits (source_target_valid g hg (of_decide_eq_true he).1).2 hp.2.2,
    ← hp.1,hp.2.1]

end PlanarHom.PlanarityLRDirect
namespace PlanarHom.PlanarityLRRealization
open Complexity PlanarityLRDirect PlanarityLRRawConstraints
open MultiGraph.Kasteleyn

 theorem dfsContour_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    eraseDart (dfsContour g hg bits a)=rawContourStep g bits (eraseDart a) := by
  unfold rawContourStep
  cases ht:isTree g a.1.val
  · rw [dfsContour,dfsContourForRows,contourPermutation_port _ _ a ht,directRotationRows_erase]
    simp [eraseDart,ht]
  · rw [dfsContour,dfsContourForRows,contourPermutation_selected _ _ a ht,directRotationRows_erase]
    simp [eraseDart,ht,reversePerm,PlanarityRotationCode.reverse]

end PlanarHom.PlanarityLRRealization
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
open PlanarityLRRealization

 theorem rawContourStep_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) : (rawContourStep g bits a).1<g.edges.length := by
  have he:=dfsContour_erase g hg bits (liftDart a ha)
  rw [erase_liftDart] at he
  rw [← he]
  exact (dfsContour g hg bits (liftDart a ha)).1.isLt

 theorem rawContourStep_host_tree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) (ht : isTree g a.1=true) :
    host g (rawContourStep g bits a)=host g (reverse a) := by
  have h:=dfsContourForRows_host_tree g hg (directRotationRows g hg bits) (liftDart a ha) ht
  simpa only [dartHost,dfsContour_erase,erase_liftDart,erase_reversePerm] using h

 theorem rawContourStep_host_port (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {a : Dart} (ha : a.1<g.edges.length) (ht : isTree g a.1=false) :
    host g (rawContourStep g bits a)=host g a := by
  have h:=dfsContourForRows_host_port g hg (directRotationRows g hg bits) (liftDart a ha) ht
  simpa only [dartHost,dfsContour_erase,erase_liftDart] using h

end PlanarHom.PlanarityLRDirect
