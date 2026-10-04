import PlanarHom.PlanarityLRWordSubtrees
import PlanarHom.PlanarityLREventOrder
import PlanarHom.NatWordPrefixConvexity

/-! NEW exact contiguous subtree intervals in the actual sorted back-event list. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem backEvents_sorted (g : MixedCode) (bits : List Bool) :
    (backEvents g bits).Pairwise (fun a b=>eventLE g bits a b=true) :=
   List.sorted_mergeSort (eventLE_trans g bits) (eventLE_total g bits) _

 theorem eventLE_of_rank_le (g : MixedCode) (bits : List Bool) {a b : ℕ}
    (ha : isBack g a=true) (hb : isBack g b=true)
    (hr : (backEvents g bits).idxOf a≤(backEvents g bits).idxOf b) : eventLE g bits a b=true := by
  have ham:=(mem_backEvents g bits a).mpr ha
  have hbm:=(mem_backEvents g bits b).mpr hb
  rcases lt_or_eq_of_le hr with h | h
  · have hi:=List.idxOf_lt_length_of_mem ham
    have hj:=List.idxOf_lt_length_of_mem hbm
    have hs:=(List.pairwise_iff_getElem.mp (backEvents_sorted g bits))
      ((backEvents g bits).idxOf a) ((backEvents g bits).idxOf b) hi hj h
    simpa only [List.getElem_idxOf] using hs
  · have he:=(List.idxOf_inj ham hbm).mp h
    subst b
    exact (eventLE_iff g bits a a).mpr (Or.inr ⟨rfl,le_rfl⟩)

 theorem backWord_le_of_rank_le (g : MixedCode) (bits : List Bool) {a b : ℕ}
    (ha : isBack g a=true) (hb : isBack g b=true)
    (hr : (backEvents g bits).idxOf a≤(backEvents g bits).idxOf b) :
    backWord g bits a≤backWord g bits b := by
  rcases (eventLE_iff g bits a b).mp (eventLE_of_rank_le g bits ha hb hr) with h | h
  · exact h.le
  · exact le_of_eq h.1

 theorem subtree_event_interval (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v a b c : ℕ} (hv : v<g.vertices)
    (ha : isBack g a=true) (hb : isBack g b=true) (hc : isBack g c=true)
    (hr : componentRoot g v=componentRoot g (source g b))
    (hva : Desc g v (source g a)) (hvc : Desc g v (source g c))
    (hab : (backEvents g bits).idxOf a≤(backEvents g bits).idxOf b)
    (hbc : (backEvents g bits).idxOf b≤(backEvents g bits).idxOf c) : Desc g v (source g b) := by
  have hsa:source g a<g.vertices:=(source_target_valid g hg (of_decide_eq_true ha).1).1
  have hsc:source g c<g.vertices:=(source_target_valid g hg (of_decide_eq_true hc).1).1
  have hpa:=(treeWord_prefix_backWord_iff_desc g hg bits hv ha
    (componentRoot_eq_of_desc g hsa hva)).mpr hva
  have hpc:=(treeWord_prefix_backWord_iff_desc g hg bits hv hc
    (componentRoot_eq_of_desc g hsc hvc)).mpr hvc
  exact (treeWord_prefix_backWord_iff_desc g hg bits hv hb hr).mp
    (NatWordPrefix.convex hpa hpc (backWord_le_of_rank_le g bits ha hb hab)
      (backWord_le_of_rank_le g bits hb hc hbc))

end PlanarHom.PlanarityLRDirect
