import PlanarHom.PlanarityLRExcursionClassification
import PlanarHom.PlanarityLRDirectedContourWords
import PlanarHom.PlanarityLRDirectedRowChildren

/-! NEW occurrence-preserving excursion classification in the directed DFS graph. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

theorem directedExcursionWord_nonTree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (a : Dart (Fin g.edges.length))
    (ha : isTree g a.1.val=false) : directedExcursionWord g hg rows a=[a] := by
  unfold directedExcursionWord hostExcursionWord
  rw [hostExcursionLength_nonTree g hg _ _ (by simpa only [dfsDartEquiv_symm,dfsDartEquiv_index] using ha)]
  simpa only [orbitPrefix,List.range_one,List.map_cons,List.map_nil,Function.iterate_zero_apply,List.cons.injEq,and_true] using (dfsDartEquiv g).apply_symm_apply a

theorem directedExcursionWord_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    (directedExcursionWord g hg rows (e,true)).filter (fun a=> !(isTree g a.1.val))=
      directedSubtreePorts g hg rows e := by
  unfold directedExcursionWord directedSubtreePorts
  rw [←dfsDartEquiv_outward g e,Equiv.symm_apply_apply,List.filter_map]
  simp only [Function.comp_def,dfsDartEquiv_index]
  rw [hostExcursionWord_forward g hg _ e he]

theorem directedExcursionWord_reverse (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (e : Fin g.edges.length) (he : isTree g e.val=true) :
    (directedExcursionWord g hg rows (e,false)).filter (directedSubtreeKeep g e)=[] := by
  have heq : (e,false)=dfsDartEquiv g (reversePerm _ (typedOutward g e)) := by
    rw [dfsDartEquiv_reverse,dfsDartEquiv_outward]
    rfl
  unfold directedExcursionWord
  rw [heq,Equiv.symm_apply_apply,List.filter_map]
  simp only [directedSubtreeKeep,Function.comp_def,Equiv.symm_apply_apply]
  rw [hostExcursionWord_reverse g hg _ e he,List.map_nil]

theorem directedSubtreeKeep_implies_port (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : Fin g.edges.length) (a : Dart (Fin g.edges.length))
    (ha : directedSubtreeKeep g e a=true) : (!isTree g a.1.val)=true := by
  simp [(directedSubtreeKeep_eq_true g hg e a).mp ha |>.1]

theorem filter_directedSubtreeKeep_ports (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : Fin g.edges.length) (xs : List (Dart (Fin g.edges.length))) :
    (xs.filter (fun a=> !(isTree g a.1.val))).filter (directedSubtreeKeep g e)=
      xs.filter (directedSubtreeKeep g e) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro a ha
  cases hk : directedSubtreeKeep g e a
  · simp [hk]
  · simp [hk,directedSubtreeKeep_implies_port g hg e a hk]

theorem directedSubtreePorts_child_filter (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (dfsGraph g hg)) (parent child : Fin g.edges.length)
    (hc : child∈dfsChildren g (dfsTarget g hg parent)) :
    (directedSubtreePorts g hg rows child).filter (directedSubtreeKeep g parent)=
      directedSubtreePorts g hg rows child := by
  apply List.filter_eq_self.mpr
  intro a ha
  have hs := (dfsChildren_mem g _ child).mp hc
  have hd := (directedSubtreeKeep_eq_true g hg child a).mp
    ((mem_directedSubtreePorts g hg rows child hs.1 a).mp ha)
  apply (directedSubtreeKeep_eq_true g hg parent a).mpr
  refine ⟨hd.1,desc_trans g ((dfsGraph g hg).dartPair a).1.isLt ?_ hd.2⟩
  have ht : Desc g (source g child.val) (target g child.val) :=
    Or.inr (tree_source_ancestor g hg hs.1)
  simpa only [hs.2] using ht

end PlanarHom.PlanarityLRRealization
