import PlanarHom.PlanarityLRBranchKeySeparation

/-! NEW incoming-mate bounds around the whole actual child subtree, for every
original dart hosted there, including incoming mates and loops. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode

 theorem incoming_false_before_subtree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b : ℕ} (hb : isBack g b=true) (hs : bitSide bits b=false)
    {a : Dart} (ha : a.1<g.edges.length) (hd : Desc g (branchChild g b) (host g a)) :
    contourKey g bits (reverse (outward g b))<contourKey g bits a := by
  have hbranch:=branchEdge_spec g hg hb
  have hv:=(source_target_valid g hg (of_decide_eq_true hb).1).2
  have he:branchEdge g b∈orderedOutgoing g bits (target g b):=by
    simpa only [hbranch.2.1] using treeEdge_mem_orderedOutgoing g hg bits hbranch.1
  have hin:reverse (outward g b)∈incoming g bits (branchEdge g b) false:=
    (mem_incoming g bits _ _ _).mpr ⟨b,hb,rfl,hs,rfl⟩
  have hi:=incoming_false_rank_lt g hg bits hv he hin
  obtain ⟨tail,hkey⟩:=child_contourKey_decompose g hg bits hbranch.1 ha
    (by simpa only [hbranch.2.2] using hd)
  rw [hbranch.2.1] at hkey
  rw [hkey]
  unfold contourKey
  rw [host_reverse_outward]
  exact List.Lex.append_left (·<·) (List.Lex.rel hi) _

 theorem incoming_true_after_subtree (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b : ℕ} (hb : isBack g b=true) (hs : bitSide bits b=true)
    {a : Dart} (ha : a.1<g.edges.length) (hd : Desc g (branchChild g b) (host g a)) :
    contourKey g bits a<contourKey g bits (reverse (outward g b)) := by
  have hbranch:=branchEdge_spec g hg hb
  have hv:=(source_target_valid g hg (of_decide_eq_true hb).1).2
  have he:branchEdge g b∈orderedOutgoing g bits (target g b):=by
    simpa only [hbranch.2.1] using treeEdge_mem_orderedOutgoing g hg bits hbranch.1
  have hin:reverse (outward g b)∈incoming g bits (branchEdge g b) true:=
    (mem_incoming g bits _ _ _).mpr ⟨b,hb,rfl,hs,rfl⟩
  have hi:=incoming_true_rank_gt g hg bits hv he hin
  obtain ⟨tail,hkey⟩:=child_contourKey_decompose g hg bits hbranch.1 ha
    (by simpa only [hbranch.2.2] using hd)
  rw [hbranch.2.1] at hkey
  rw [hkey]
  unfold contourKey
  rw [host_reverse_outward]
  exact List.Lex.append_left (·<·) (List.Lex.rel hi) _

end PlanarHom.PlanarityLRDirect
