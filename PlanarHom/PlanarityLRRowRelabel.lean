import PlanarHom.PlanarityLRVisitRanks
import PlanarHom.StateWordRelabel

/-! NEW strict rank relabeling from ordered outgoing occurrences to their exact
positions in the actual local contour row. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
local instance rowRelabelDartBEq : BEq Dart := instBEqOfDecidableEq

 def outgoingAt (g : MixedCode) (bits : List Bool) (v i : ℕ) : ℕ :=
   (orderedOutgoing g bits v).getD i g.edges.length
 def rankBound (g : MixedCode) (bits : List Bool) (v : ℕ) : ℕ := (orderedOutgoing g bits v).length
 def rankStep (g : MixedCode) (bits : List Bool) (v i : ℕ) : ℕ := target g (outgoingAt g bits v i)
 def rankCode (g : MixedCode) (bits : List Bool) (v i : ℕ) : ℕ :=
   localRank g bits v (outward g (outgoingAt g bits v i))

 theorem rowIndex_pairwise (row : List Dart) (hn : row.Nodup) :
    row.Pairwise (fun a b=>rowIndex row a<rowIndex row b) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa only [rowIndex,List.idxOf_getElem hn] using hij

 theorem outward_localRank_pairwise (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v : ℕ} (hv : v<g.vertices) :
    (orderedOutgoing g bits v).Pairwise (fun e f=>localRank g bits v (outward g e)<localRank g bits v (outward g f)) := by
  have hs:=(rowIndex_pairwise _ (visitRow_nodup g hg bits hv)).filter (forwardFlag g)
  rw [visitRow_filter_forward g hg bits v] at hs
  simpa only [List.pairwise_map,localRank] using hs

 theorem rankCode_strict (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v i j : ℕ) (hij : i<j) (hj : j<rankBound g bits v) :
    rankCode g bits v i<rankCode g bits v j := by
  have hi:i<(orderedOutgoing g bits v).length:=lt_trans hij hj
  have hem: (orderedOutgoing g bits v)[j]∈orderedOutgoing g bits v:=List.getElem_mem hj
  have he:=outgoing_spec g ((mem_orderedOutgoing g bits v _).mp hem)
  have hv:v<g.vertices := by rw [← he.2.2]; exact (source_target_valid g hg he.1).1
  have hs:=(List.pairwise_iff_getElem.mp (outward_localRank_pairwise g hg bits hv)) i j hi hj hij
  simpa only [rankCode,outgoingAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] using hs

 theorem outgoingAt_idxOf (g : MixedCode) (bits : List Bool) {v e : ℕ}
    (he : e∈orderedOutgoing g bits v) : outgoingAt g bits v ((orderedOutgoing g bits v).idxOf e)=e := by
  simp only [outgoingAt,List.getD_eq_getElem?_getD,List.getElem?_idxOf he,Option.getD_some]

end PlanarHom.PlanarityLRDirect
