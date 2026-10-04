import PlanarHom.PlanarityLRSubtreeIntervals

/-! NEW exact event order between distinct actual tree-child subtrees. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem treeWord_tree_target (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isTree g e=true) :
    treeWord g bits (target g e)=treeWord g bits (source g e)++
      [(orderedOutgoing g bits (source g e)).idxOf e] := by
  have hp:=tree_source_parent g hg he
  have ht:=(source_target_valid g hg (of_decide_eq_true he).1).2
  rw [treeWord_parent g bits ht hp.2.2,← hp.1,hp.2.1]

 theorem treeEdge_mem_orderedOutgoing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e : ℕ} (he : isTree g e=true) :
    e∈orderedOutgoing g bits (source g e) := by
  have hp:=tree_source_parent g hg he
  have ht:=(source_target_valid g hg (of_decide_eq_true he).1).2
  simpa only [← hp.1,hp.2.1] using parentEdge_mem_orderedOutgoing g hg bits ht hp.2.2

 theorem rank_lt_of_backWord_lt (g : MixedCode) (bits : List Bool) {a b : ℕ}
    (ha : isBack g a=true) (hb : isBack g b=true)
    (hword : backWord g bits a<backWord g bits b) :
    (backEvents g bits).idxOf a<(backEvents g bits).idxOf b := by
  by_contra h
  exact (not_le_of_gt hword) (backWord_le_of_rank_le g bits hb ha (Nat.le_of_not_gt h))

 theorem treeBranch_backWord_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e f a b : ℕ} (he : isTree g e=true) (hf : isTree g f=true)
    (ha : isBack g a=true) (hb : isBack g b=true)
    (hsource : source g e=source g f)
    (hea : Desc g (target g e) (source g a)) (hfb : Desc g (target g f) (source g b))
    (hrank : (orderedOutgoing g bits (source g e)).idxOf e<
      (orderedOutgoing g bits (source g f)).idxOf f) : backWord g bits a<backWord g bits b := by
  have hva:source g a<g.vertices:=(source_target_valid g hg (of_decide_eq_true ha).1).1
  have hvb:source g b<g.vertices:=(source_target_valid g hg (of_decide_eq_true hb).1).1
  have hpa : (treeWord g bits (target g e)).IsPrefix (backWord g bits a) :=
    (treeWord_prefix_of_desc g bits hva hea).trans (List.prefix_append _ _)
  have hpb : (treeWord g bits (target g f)).IsPrefix (backWord g bits b) :=
    (treeWord_prefix_of_desc g bits hvb hfb).trans (List.prefix_append _ _)
  obtain ⟨as,has⟩:=hpa
  obtain ⟨bs,hbs⟩:=hpb
  rw [treeWord_tree_target g hg bits he,hsource] at has
  rw [treeWord_tree_target g hg bits hf] at hbs
  rw [← has,← hbs,List.append_assoc,List.append_assoc]
  apply List.Lex.append_left (·<·)
  exact List.Lex.rel (by simpa only [hsource] using hrank)

 theorem treeBranch_event_rank_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e f a b : ℕ} (he : isTree g e=true) (hf : isTree g f=true)
    (ha : isBack g a=true) (hb : isBack g b=true)
    (hsource : source g e=source g f)
    (hea : Desc g (target g e) (source g a)) (hfb : Desc g (target g f) (source g b))
    (hrank : (orderedOutgoing g bits (source g e)).idxOf e<
      (orderedOutgoing g bits (source g f)).idxOf f) :
    (backEvents g bits).idxOf a<(backEvents g bits).idxOf b :=
   rank_lt_of_backWord_lt g bits ha hb (treeBranch_backWord_lt g hg bits he hf ha hb hsource hea hfb hrank)

 theorem treeBranch_event_rank_lt_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e f a b : ℕ} (he : isTree g e=true) (hf : isTree g f=true)
    (ha : isBack g a=true) (hb : isBack g b=true) (hne : e≠f)
    (hsource : source g e=source g f)
    (hea : Desc g (target g e) (source g a)) (hfb : Desc g (target g f) (source g b)) :
    (backEvents g bits).idxOf a<(backEvents g bits).idxOf b ↔
    (orderedOutgoing g bits (source g e)).idxOf e<(orderedOutgoing g bits (source g f)).idxOf f := by
  refine ⟨?_,treeBranch_event_rank_lt g hg bits he hf ha hb hsource hea hfb⟩
  intro h
  have heMem:e∈orderedOutgoing g bits (source g f) := by
    simpa only [hsource] using treeEdge_mem_orderedOutgoing g hg bits he
  have hfMem:=treeEdge_mem_orderedOutgoing g hg bits hf
  have hidx : (orderedOutgoing g bits (source g e)).idxOf e≠
      (orderedOutgoing g bits (source g f)).idxOf f := by
    intro hh
    apply hne
    exact (List.idxOf_inj heMem hfMem).mp (by simpa only [hsource] using hh)
  by_contra hn
  have hrev : (orderedOutgoing g bits (source g f)).idxOf f<
      (orderedOutgoing g bits (source g e)).idxOf e := by omega
  have hevent:=treeBranch_event_rank_lt g hg bits hf he hb ha hsource.symm hfb hea hrev
  omega

 theorem treeReturn_source_desc (g : MixedCode) {e a : ℕ} (he : isTree g e=true)
    (ha : a∈returns g e) : Desc g (target g e) (source g a) := by
  simp only [returns,he,if_true,List.mem_filter,Bool.and_eq_true] at ha
  change target g e=source g a ∨ target g e∈ancestors g (source g a)
  exact of_decide_eq_true ha.2.1.2

 theorem treeReturn_event_rank_lt_iff (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {e f a b : ℕ} (he : isTree g e=true) (hf : isTree g f=true)
    (hne : e≠f) (hsource : source g e=source g f)
    (ha : a∈returns g e) (hb : b∈returns g f) :
    (backEvents g bits).idxOf a<(backEvents g bits).idxOf b ↔
    (orderedOutgoing g bits (source g e)).idxOf e<(orderedOutgoing g bits (source g f)).idxOf f :=
   treeBranch_event_rank_lt_iff g hg bits he hf (mem_returns_back g e ha) (mem_returns_back g f hb)
     hne hsource (treeReturn_source_desc g he ha) (treeReturn_source_desc g hf hb)

end PlanarHom.PlanarityLRDirect
