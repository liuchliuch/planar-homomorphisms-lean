import PlanarHom.PlanarityLRDirectedSubtreeInfix
import PlanarHom.ListInfixRankInterval

/-! NEW exact descendant interval convexity and outside-port rank separation. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityDepthFirstSearch FinitePermutationReturnWords

theorem directedRootPorts_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) :
    (directedRootPorts g hg rows r).Nodup := by
  unfold directedRootPorts
  cases h : (rows.row r).head? with
  | none => simp
  | some a => simpa only [Option.map_some,Option.getD_some] using contourPortWord_nodup rows (fun e=>isTree g e.val) a

theorem mem_directedRootPorts_nonTree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (a : Dart (Fin g.edges.length))
    (ha : a∈directedRootPorts g hg rows r) : isTree g a.1.val=false := by
  unfold directedRootPorts at ha
  cases h : (rows.row r).head? with
  | none => simp [h] at ha
  | some b =>
      simp only [h,Option.map_some,Option.getD_some] at ha
      simpa only [Bool.not_eq_true'] using (List.mem_filter.mp ha).2

theorem directedSubtreePorts_root_membership (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices)
    (e : Fin g.edges.length) (he : isTree g e.val=true) (a : Dart (Fin g.edges.length))
    (ha : a∈directedRootPorts g hg rows r) :
    a∈directedSubtreePorts g hg rows e ↔ Desc g (target g e.val) ((dfsGraph g hg).dartPair a).1.val := by
  rw [mem_directedSubtreePorts g hg rows e he a,directedSubtreeKeep_eq_true g hg e a]
  exact and_iff_right (mem_directedRootPorts_nonTree g hg rows r a ha)

theorem directedSubtreePorts_outside_rank (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (e : Fin g.edges.length) (he : isTree g e.val=true)
    (hroot : componentRoot g (source g e.val)=r.val)
    (a b c : Dart (Fin g.edges.length))
    (ha : a∈directedRootPorts g hg rows r) (hb : b∈directedRootPorts g hg rows r)
    (hc : c∈directedRootPorts g hg rows r)
    (hda : Desc g (target g e.val) ((dfsGraph g hg).dartPair a).1.val)
    (hdc : Desc g (target g e.val) ((dfsGraph g hg).dartPair c).1.val)
    (hdb : ¬Desc g (target g e.val) ((dfsGraph g hg).dartPair b).1.val) :
    ((directedRootPorts g hg rows r).idxOf b<(directedRootPorts g hg rows r).idxOf a ∧
      (directedRootPorts g hg rows r).idxOf b<(directedRootPorts g hg rows r).idxOf c) ∨
    ((directedRootPorts g hg rows r).idxOf a<(directedRootPorts g hg rows r).idxOf b ∧
      (directedRootPorts g hg rows r).idxOf c<(directedRootPorts g hg rows r).idxOf b) := by
  simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using ListInfixRankInterval.outside_rank_separation
    (directedSubtreePorts_infix_root g hg rows r hr e he hroot)
    (directedRootPorts_nodup g hg rows r)
    ((directedSubtreePorts_root_membership g hg rows r e he a ha).mpr hda)
    ((directedSubtreePorts_root_membership g hg rows r e he c hc).mpr hdc) hb
    (fun h=>hdb ((directedSubtreePorts_root_membership g hg rows r e he b hb).mp h))

theorem directedSubtreePorts_convex (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (r : Fin g.vertices) (hr : height g r.val=0)
    (e : Fin g.edges.length) (he : isTree g e.val=true)
    (hroot : componentRoot g (source g e.val)=r.val)
    (a b c : Dart (Fin g.edges.length)) (hsub : [a,b,c].Sublist (directedRootPorts g hg rows r))
    (hda : Desc g (target g e.val) ((dfsGraph g hg).dartPair a).1.val)
    (hdc : Desc g (target g e.val) ((dfsGraph g hg).dartPair c).1.val) :
    Desc g (target g e.val) ((dfsGraph g hg).dartPair b).1.val := by
  have ha : a∈directedRootPorts g hg rows r := hsub.subset (by simp)
  have hb : b∈directedRootPorts g hg rows r := hsub.subset (by simp)
  have hc : c∈directedRootPorts g hg rows r := hsub.subset (by simp)
  apply (directedSubtreePorts_root_membership g hg rows r e he b hb).mp
  exact ListInfixRankInterval.sublist_middle_mem
    (directedSubtreePorts_infix_root g hg rows r hr e he hroot)
    (directedRootPorts_nodup g hg rows r) hsub
    ((directedSubtreePorts_root_membership g hg rows r e he a ha).mpr hda)
    ((directedSubtreePorts_root_membership g hg rows r e he c hc).mpr hdc)

end PlanarHom.PlanarityLRRealization
