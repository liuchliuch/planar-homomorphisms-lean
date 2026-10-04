import PlanarHom.PlanarityLRContourCycles
import PlanarHom.PlanarityLRBranchEventOrder

/-! NEW exact projection of literal rows onto forward tree/back occurrences.
Incoming opposite darts, the parent dart, and loop darts are excluded by proof. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityRotationCode PlanarityLRRawConstraints

 def forwardFlag (g : MixedCode) (a : Dart) : Bool :=
   decide (a=outward g a.1) && (isTree g a.1 || isBack g a.1)

@[simp] theorem forwardFlag_reverse (g : MixedCode) (e : ℕ) : forwardFlag g (reverse (outward g e))=false := by
  simp [forwardFlag,(outward_ne_reversed g e e).symm]

 theorem forwardFlag_of_outgoing (g : MixedCode) (bits : List Bool) {v e : ℕ}
    (he : e∈orderedOutgoing g bits v) : forwardFlag g (outward g e)=true := by
  have hs:=(outgoing_spec g ((mem_orderedOutgoing g bits v e).mp he)).2.1
  rcases hs with h | h <;> simp [forwardFlag,h]

 theorem incoming_filter_forward (g : MixedCode) (bits : List Bool) (e : ℕ) (side : Bool) :
    (incoming g bits e side).filter (forwardFlag g)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  rw [(incoming_index g bits ha).2.2.2,forwardFlag_reverse]
  simp

 theorem parentRow_filter_forward (g : MixedCode) (v : ℕ) :
    (parentRow g v).filter (forwardFlag g)=[] := by
  unfold parentRow
  split_ifs <;> simp

 theorem loopRow_filter_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : ℕ) :
    (loopRow g v).filter (forwardFlag g)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro a ha
  have hl:=((mem_loopRow g v a).mp ha).2.1
  have ht:isTree g a.1=false := Bool.eq_false_iff.mpr (fun h=>tree_nonloop g hg h hl)
  have hb:isBack g a.1=false := Bool.eq_false_iff.mpr (fun h=>back_nonloop g h hl)
  simp [forwardFlag,ht,hb]

 theorem edgeBlock_filter_forward (g : MixedCode) (bits : List Bool) {v e : ℕ}
    (he : e∈orderedOutgoing g bits v) :
    (edgeBlock g bits e).filter (forwardFlag g)=[outward g e] := by
  simp [edgeBlock,incoming_filter_forward,forwardFlag_of_outgoing g bits he]

 theorem directRow_filter_forward (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (v : ℕ) :
    (directRow g bits v).filter (forwardFlag g)=(orderedOutgoing g bits v).map (outward g) := by
  simp only [directRow,List.filter_append,parentRow_filter_forward,loopRow_filter_forward g hg,
    List.nil_append,List.append_nil,List.filter_flatMap]
  calc
    _ = (orderedOutgoing g bits v).flatMap (fun e=>[outward g e]) := by
      apply List.flatMap_congr
      intro e he
      exact edgeBlock_filter_forward g bits he
    _ = _ := by
      induction orderedOutgoing g bits v with
      | nil => rfl
      | cons a xs ih => simpa using congrArg (List.cons (outward g a)) ih

end PlanarHom.PlanarityLRDirect
