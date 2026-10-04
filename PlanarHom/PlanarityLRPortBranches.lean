import PlanarHom.PlanarityLRBackEdgeForks
import PlanarHom.PlanarityLRRowIncidence

/-! NEW ancestor and local-block membership facts for actual paired back ports. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode

 theorem desc_eq_of_equal_height (g : MixedCode) {a b v : ℕ} (hv : v < g.vertices)
    (ha : Desc g a v) (hb : Desc g b v) (hh : height g a=height g b) : a=b := by
  rcases desc_comparable g hv ha hb with h | h
  · rcases h with h | h
    · exact h
    · have hlt := ancestors_height_lt g (desc_valid g hv hb) h
      omega
  · rcases h with h | h
    · exact h.symm
    · have hlt := ancestors_height_lt g (desc_valid g hv ha) h
      omega

 theorem branchChild_desc_of_target_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b v : ℕ} (hb : isBack g b=true) (hv : Desc g v (source g b))
    (hlt : targetHeight g b < height g v) : Desc g (branchChild g b) v := by
  have hs := (source_target_valid g hg (of_decide_eq_true hb).1).1
  have hc := branchChild_spec g hg hb
  exact desc_of_height_le g hs hc.2.1 hv (by omega)

 theorem target_desc_of_target_lt (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b v : ℕ} (hb : isBack g b=true) (hv : Desc g v (source g b))
    (hlt : targetHeight g b < height g v) : Desc g (target g b) v :=
  desc_of_height_le g (source_target_valid g hg (of_decide_eq_true hb).1).1
    (Or.inr (back_target_ancestor g hg hb)) hv hlt.le

 theorem branchEdge_eq_of_common_target (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b c v : ℕ} (hb : isBack g b=true) (hc : isBack g c=true)
    (hvb : Desc g v (source g b)) (hvc : Desc g v (source g c))
    (ht : target g b=target g c) (hlt : targetHeight g b < height g v) : branchEdge g b=branchEdge g c := by
  have hs := (source_target_valid g hg (of_decide_eq_true hb).1).1
  have hv := desc_valid g hs hvb
  have hbc := branchChild_spec g hg hb
  have hcc := branchChild_spec g hg hc
  have hheight : targetHeight g b=targetHeight g c := congrArg (height g) ht
  have h₁ := branchChild_desc_of_target_lt g hg hb hvb hlt
  have h₂ := branchChild_desc_of_target_lt g hg hc hvc (by omega)
  have heq := desc_eq_of_equal_height g hv h₁ h₂ (by omega)
  exact congrArg (parentEdge g) heq

/-- An expanded outgoing block consists of its literal local ports and the
hosted darts of its child subtree, when the outgoing occurrence is a tree edge. -/
def InExpandedBranch (g : MixedCode) (bits : List Bool) (e : ℕ) (a : Dart) : Prop :=
  a ∈ edgeBlock g bits e ∨ isTree g e=true ∧ Desc g (target g e) (host g a)

 theorem BackBranch.outward_in_expanded {g : MixedCode} {v b e : ℕ}
    (H : BackBranch g v b e) (bits : List Bool) : InExpandedBranch g bits e (outward g b) := by
  rcases H.branch with ⟨rfl,_⟩ | ⟨he,hd⟩
  · left
    simp [edgeBlock]
  · exact Or.inr ⟨he,by simpa only [host_outward] using hd⟩

 theorem BackBranch.target_location {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    {v b e : ℕ} (H : BackBranch g v b e) (hb : isBack g b=true)
    (hge : height g v≤targetHeight g b) :
    isTree g e=true ∧ (Desc g (target g e) (target g b) ∨ (target g b=v ∧ branchEdge g b=e)) := by
  have hs := (source_target_valid g hg (of_decide_eq_true hb).1).1
  have ht := (source_target_valid g hg (of_decide_eq_true hb).1).2
  rcases H.branch with ⟨heb,hsv⟩ | ⟨he,hd⟩
  · have hlt := back_height_lt g hg hb
    rw [hsv] at hlt
    omega
  · have hsource := (outgoing_spec g H.outgoing).2.2
    have hstep := tree_height_succ g hg he
    rw [hsource] at hstep
    have hbc := branchChild_spec g hg hb
    refine ⟨he,?_⟩
    by_cases htv : target g b=v
    · right
      refine ⟨htv,?_⟩
      have hheight : height g (branchChild g b)=height g (target g e) := by
        have hch := hbc.2.2
        simp only [targetHeight,htv] at hch
        omega
      have hchild := desc_eq_of_equal_height g hs hbc.2.1 hd hheight
      change parentEdge g (branchChild g b)=e
      rw [hchild]
      exact (tree_source_parent g hg he).2.1
    · left
      have hvb : Desc g v (source g b) :=
        desc_trans g hs (Or.inr (by simpa only [hsource] using tree_source_ancestor g hg he)) hd
      have hvt : Desc g v (target g b) :=
        desc_of_height_le g hs hvb (Or.inr (back_target_ancestor g hg hb)) hge
      have hlt : height g v < height g (target g b) := by
        rcases hvt with h | h
        · exact False.elim (htv h.symm)
        · exact ancestors_height_lt g ht h
      exact desc_of_height_le g hs hd (Or.inr (back_target_ancestor g hg hb)) (by omega)

 theorem BackBranch.inward_in_expanded_of_target_ge {g : MixedCode} {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) {v b e : ℕ} (H : BackBranch g v b e) (hb : isBack g b=true)
    (hge : height g v≤targetHeight g b) : InExpandedBranch g bits e (reverse (outward g b)) := by
  obtain ⟨he,hd | ⟨_,hbranch⟩⟩ := H.target_location hg hb hge
  · exact Or.inr ⟨he,by simpa only [host_reverse_outward] using hd⟩
  · left
    have hin : reverse (outward g b) ∈ incoming g bits e (bitSide bits b) :=
      (mem_incoming g bits e _ _).mpr ⟨b,hb,hbranch,rfl,rfl⟩
    cases hs : bitSide bits b
    · rw [hs] at hin
      exact List.mem_append_left _ (List.mem_append_left _ hin)
    · rw [hs] at hin
      exact List.mem_append_right _ hin

end PlanarHom.PlanarityLRDirect
