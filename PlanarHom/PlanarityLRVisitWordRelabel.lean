import PlanarHom.PlanarityLRRowRelabel
import PlanarHom.PlanarityLRContourKeys

/-! NEW exact relabeling of existing DFS/event words into concrete contour keys. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
open StateWordRelabel

 theorem treeWord_relabel_spec (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) :
    StateWordRelabel.Valid (rankBound g bits) (rankStep g bits) (componentRoot g v) (treeWord g bits v) ∧
    walk (rankStep g bits) (componentRoot g v) (treeWord g bits v)=v ∧
    relabel (rankCode g bits) (rankStep g bits) (componentRoot g v) (treeWord g bits v)=visitTreeWord g bits v := by
  induction h : height g v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hz:height g v=0
    · simp [treeWord_root g bits hz,componentRoot_eq_self g hv hz,
        StateWordRelabel.Valid,walk,relabel,visitTreeWord,rootPath_eq_singleton g hz]
    · have hp:0<height g v:=by omega
      have ha:=parentVertex_ancestor g hv hp
      have hpv:=ancestors_valid g hv ha
      have hh:=parent_height g hv hp
      have hs:=ih (height g (parentVertex g v)) (by omega) hpv rfl
      have hr:=componentRoot_eq_of_desc g hv (Or.inr ha)
      rw [hr] at hs
      have hm:=parentEdge_mem_orderedOutgoing g hg bits hv hp
      have hi : (orderedOutgoing g bits (parentVertex g v)).idxOf (parentEdge g v)<rankBound g bits (parentVertex g v) :=
        List.idxOf_lt_length_of_mem hm
      have he:=outgoingAt_idxOf g bits hm
      have ht:=(parentEdge_tree g hg hv hp).2.1
      rw [treeWord_parent g bits hv hp]
      refine ⟨?_,?_,?_⟩
      · rw [valid_append]
        refine ⟨hs.1,?_⟩
        rw [hs.2.1]
        exact ⟨hi,trivial⟩
      · rw [walk_append,hs.2.1]
        simpa only [walk,rankStep,he] using ht
      · rw [relabel_append,hs.2.1,hs.2.2,visitTreeWord_parent g bits hv hp]
        simp only [relabel,rankCode,he,List.append_nil]

 theorem backWord_relabel_spec (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isBack g e=true) :
    StateWordRelabel.Valid (rankBound g bits) (rankStep g bits) (componentRoot g (source g e)) (backWord g bits e) ∧
    relabel (rankCode g bits) (rankStep g bits) (componentRoot g (source g e)) (backWord g bits e)=
      contourKey g bits (outward g e) := by
  have hv:=(source_target_valid g hg (of_decide_eq_true he).1).1
  have ht:=treeWord_relabel_spec g hg bits hv
  have hm:=backEdge_mem_orderedOutgoing g bits he
  have hi : (orderedOutgoing g bits (source g e)).idxOf e<rankBound g bits (source g e):=List.idxOf_lt_length_of_mem hm
  have hed:=outgoingAt_idxOf g bits hm
  constructor
  · rw [backWord,valid_append]
    refine ⟨ht.1,?_⟩
    rw [ht.2.1]
    exact ⟨hi,trivial⟩
  · rw [backWord,relabel_append,ht.2.1,ht.2.2]
    simp only [relabel,rankCode,hed,contourKey,host_outward]

 theorem contourKey_outward_lt_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e f : ℕ} (he : isBack g e=true) (hf : isBack g f=true)
    (hr : componentRoot g (source g e)=componentRoot g (source g f)) :
    contourKey g bits (outward g e)<contourKey g bits (outward g f) ↔ backWord g bits e<backWord g bits f := by
  have hse:=backWord_relabel_spec g hg bits he
  have hsf:=backWord_relabel_spec g hg bits hf
  rw [← hse.2,← hsf.2,hr]
  rw [hr] at hse
  exact relabel_lt_iff (rankBound g bits) (rankCode g bits) (rankStep g bits)
    (rankCode_strict g hg bits) _ _ _ hse.1 hsf.1

end PlanarHom.PlanarityLRDirect
