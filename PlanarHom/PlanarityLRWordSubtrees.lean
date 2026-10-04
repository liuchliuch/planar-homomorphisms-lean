import PlanarHom.PlanarityLRBackWords

/-! NEW exact subtree/event-word correspondence. A terminal back-edge symbol
is never a tree-path prefix, so tree-prefix blocks describe actual descendants. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem backWord_not_prefix_treeWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {b v : ℕ} (hb : isBack g b=true) (hv : v<g.vertices)
    (hr : componentRoot g (source g b)=componentRoot g v) :
    ¬(backWord g bits b).IsPrefix (treeWord g bits v) := by
  intro hp
  have hs:source g b<g.vertices:=(source_target_valid g hg (of_decide_eq_true hb).1).1
  have hts : (treeWord g bits (source g b)).IsPrefix (treeWord g bits v) :=
    (List.prefix_append _ _).trans hp
  rcases (treeWord_prefix_iff_desc g hg bits hs hv hr).mp hts with he | ha
  · have hl:=hp.length_le
    simp only [backWord_length,treeWord_length,he] at hl
    omega
  · obtain ⟨w,hw,hpw,hwv,hwh⟩:=exists_child_toward g hv ha
    have hwpos:0<height g w:=by omega
    have hwp:=treeWord_prefix_of_desc g bits hv hwv
    have heql:(backWord g bits b).length=(treeWord g bits w).length := by
      simp only [backWord_length,treeWord_length,hwh]
    have heq:=(List.prefix_of_prefix_length_le hp hwp heql.le).eq_of_length heql
    rw [treeWord_parent g bits hw hwpos,hpw] at heq
    have hi:(orderedOutgoing g bits (source g b)).idxOf b=
        (orderedOutgoing g bits (source g b)).idxOf (parentEdge g w) := by
      simpa only [backWord,List.append_right_inj,List.singleton_inj] using heq
    have hmem:parentEdge g w∈orderedOutgoing g bits (source g b) := by
      simpa only [hpw] using parentEdge_mem_orderedOutgoing g hg bits hw hwpos
    have hedge:b=parentEdge g w:=
      (List.idxOf_inj (backEdge_mem_orderedOutgoing g bits hb) hmem).mp hi
    have ht:=(parentEdge_tree g hg hw hwpos).1
    have hf:=(of_decide_eq_true hb).2.1
    rw [hedge,ht] at hf
    contradiction

 theorem treeWord_prefix_backWord_iff_desc (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {u b : ℕ} (hu : u<g.vertices) (hb : isBack g b=true)
    (hr : componentRoot g u=componentRoot g (source g b)) :
    (treeWord g bits u).IsPrefix (backWord g bits b) ↔ Desc g u (source g b) := by
  have hs:source g b<g.vertices:=(source_target_valid g hg (of_decide_eq_true hb).1).1
  have hsp:(treeWord g bits (source g b)).IsPrefix (backWord g bits b):=List.prefix_append _ _
  constructor
  · intro hp
    by_cases hle:height g u≤height g (source g b)
    · exact (treeWord_prefix_iff_desc g hg bits hu hs hr).mp
        (List.prefix_of_prefix_length_le hp hsp (by simpa only [treeWord_length] using hle))
    · have hlen:=hp.length_le
      simp only [treeWord_length,backWord_length] at hlen
      have heq:=hp.eq_of_length (by simp only [treeWord_length,backWord_length]; omega)
      exact (backWord_not_prefix_treeWord g hg bits hb hu hr.symm (by rw [heq])).elim
  · intro hd
    exact (treeWord_prefix_of_desc g bits hs hd).trans hsp

end PlanarHom.PlanarityLRDirect
