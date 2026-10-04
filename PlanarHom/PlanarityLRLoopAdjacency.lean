import PlanarHom.PlanarityLRIncomingMateOrder
import PlanarHom.OrderedCycleAdjacentPorts
import Mathlib.Data.List.Infix

/-! NEW literal loop-port adjacency in the actual computed contour. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityRotationCode
open PlanarityLRRealization

 theorem loop_hosts (g : MixedCode) {e : ℕ} (hl : (edge g e).1=(edge g e).2.1) :
    host g (e,true)=(edge g e).1 ∧ host g (e,false)=(edge g e).1 := by simp [host,hl]

 theorem loop_pair_infix (g : MixedCode) {e : ℕ} (he : e<g.edges.length)
    (hl : (edge g e).1=(edge g e).2.1) (bits : List Bool) :
    [(e,true),(e,false)].IsInfix (visitRow g bits (edge g e).1) := by
  have hm : e∈(List.range g.edges.length).filter (fun e'=>decide
      ((edge g e').1=(edge g e').2.1 ∧ (edge g e').1=(edge g e).1)) := by simp [he,hl]
  obtain ⟨pre,post,hparts⟩:=List.mem_iff_append.mp hm
  have hloop : [(e,true),(e,false)].IsInfix (loopRow g (edge g e).1) := by
    unfold loopRow
    rw [hparts,List.flatMap_append,List.flatMap_cons]
    exact ⟨pre.flatMap (fun e'=>[(e',true),(e',false)]),post.flatMap (fun e'=>[(e',true),(e',false)]),by simp⟩
  exact hloop.trans ((List.infix_append_right).trans List.infix_append_left)

 theorem formPerm_adjacent {A : Type} [DecidableEq A] (row : List A) (hn : row.Nodup)
    {a b : A} (hab : [a,b].IsInfix row) : row.formPerm a=b := by
  obtain ⟨pre,post,hrow⟩:=hab
  have hlen:pre.length+1<row.length:=by rw [← hrow]; simp
  have ha:row[pre.length]'(by omega)=a := by simp [← hrow,List.append_assoc]
  have hb:row[pre.length+1]'hlen=b := by simp [← hrow,List.append_assoc]
  have hf:=List.formPerm_apply_lt_getElem row hn pre.length hlen
  rw [ha,hb] at hf
  exact hf

 theorem loop_contour_successor (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : e<g.edges.length) (hl : (edge g e).1=(edge g e).2.1) :
    rawContourStep g bits (e,true)=(e,false) := by
  have ht:isTree g e=false:=Bool.eq_false_iff.mpr (fun h=>tree_nonloop g hg h hl)
  have hv:=(edge_valid g hg he).1
  have hp:=loop_pair_infix g he hl bits
  simp only [rawContourStep,ht,Bool.false_eq_true,if_false]
  rw [directRotation_eq_visitRow_formPerm g hg bits he]
  rw [(loop_hosts g hl).1]
  exact formPerm_adjacent _ (visitRow_nodup g hg bits hv) hp

 theorem loop_key_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : e<g.edges.length) (hl : (edge g e).1=(edge g e).2.1) :
    contourKey g bits (e,true)<contourKey g bits (e,false) := by
  have hv:=(edge_valid g hg he).1
  have hp:=localRank_lt_of_pair_sublist g hg bits hv (loop_pair_infix g he hl bits).sublist
  unfold contourKey
  rw [(loop_hosts g hl).1,(loop_hosts g hl).2]
  exact List.Lex.append_left (·<·) (List.Lex.rel hp) _

end PlanarHom.PlanarityLRDirect
