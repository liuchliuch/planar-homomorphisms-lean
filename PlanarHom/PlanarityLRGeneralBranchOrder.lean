import PlanarHom.PlanarityLRBackEdgeForks
import PlanarHom.PlanarityLRBranchEventOrder

/-! NEW event order for all outgoing branches, including terminal back events. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

 theorem BackBranch.word_prefix {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v b e : ℕ} (H : BackBranch g v b e) (hb : isBack g b=true) :
    (treeWord g bits v++[(orderedOutgoing g bits v).idxOf e]).IsPrefix (backWord g bits b) := by
  rcases H.branch with ⟨rfl,hsource⟩ | ⟨ht,hdesc⟩
  · simp only [backWord,hsource]
    exact ⟨[],by simp⟩
  · have hs := (source_target_valid g hg (of_decide_eq_true hb).1).1
    have hp : (treeWord g bits (target g e)).IsPrefix (backWord g bits b) :=
      (treeWord_prefix_of_desc g bits hs hdesc).trans (List.prefix_append _ _)
    rw [treeWord_tree_target g hg bits ht,(outgoing_spec g H.outgoing).2.2] at hp
    exact hp

 theorem BackBranch.backWord_lt {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v b c e f : ℕ} (H : BackBranch g v b e) (K : BackBranch g v c f)
    (hb : isBack g b=true) (hc : isBack g c=true)
    (hord : (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f) :
    backWord g bits b < backWord g bits c := by
  obtain ⟨bs,hbs⟩ := H.word_prefix hg bits hb
  obtain ⟨cs,hcs⟩ := K.word_prefix hg bits hc
  rw [← hbs,← hcs,List.append_assoc,List.append_assoc]
  apply List.Lex.append_left (· < ·)
  exact List.Lex.rel hord

 theorem BackBranch.event_rank_lt_iff {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v b c e f : ℕ} (H : BackBranch g v b e) (K : BackBranch g v c f)
    (hb : isBack g b=true) (hc : isBack g c=true) (hne : e≠f) :
    (backEvents g bits).idxOf b < (backEvents g bits).idxOf c ↔
      (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f := by
  have hforward : (orderedOutgoing g bits v).idxOf e < (orderedOutgoing g bits v).idxOf f →
      (backEvents g bits).idxOf b < (backEvents g bits).idxOf c :=
    fun h => rank_lt_of_backWord_lt g bits hb hc (H.backWord_lt hg bits K hb hc h)
  refine ⟨?_,hforward⟩
  intro hbc
  have hem := (mem_orderedOutgoing g bits v e).mpr H.outgoing
  have hfm := (mem_orderedOutgoing g bits v f).mpr K.outgoing
  have hidx : (orderedOutgoing g bits v).idxOf e≠(orderedOutgoing g bits v).idxOf f :=
    fun h => hne ((List.idxOf_inj hem hfm).mp h)
  by_contra hno
  have hrev : (orderedOutgoing g bits v).idxOf f < (orderedOutgoing g bits v).idxOf e := by omega
  have hcb := rank_lt_of_backWord_lt g bits hc hb (K.backWord_lt hg bits H hc hb hrev)
  omega

 theorem BackBranch.ne_of_deepest {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    {v b c e f : ℕ} (H : BackBranch g v b e) (K : BackBranch g v c f)
    (hb : isBack g b=true) (hc : isBack g c=true) (hne : b≠c)
    (hmax : ∀ x, x < g.vertices → Desc g x (source g b) → Desc g x (source g c) → height g x≤height g v) : e≠f := by
  intro hef
  subst f
  rcases H.branch with ⟨heb,_⟩ | ⟨het,hed⟩ <;> rcases K.branch with ⟨hec,_⟩ | ⟨het',hed'⟩
  · exact hne (heb.symm.trans hec)
  · have hfalse := (of_decide_eq_true hb).2.1
    rw [← heb,het'] at hfalse
    contradiction
  · have hfalse := (of_decide_eq_true hc).2.1
    rw [← hec,het] at hfalse
    contradiction
  · have htv := (source_target_valid g hg (of_decide_eq_true het).1).2
    have hle := hmax (target g e) htv hed hed'
    have hstep := tree_height_succ g hg het
    rw [(outgoing_spec g H.outgoing).2.2] at hstep
    omega

end PlanarHom.PlanarityLRDirect
