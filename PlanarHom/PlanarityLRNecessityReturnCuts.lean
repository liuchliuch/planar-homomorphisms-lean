import PlanarHom.PlanarityLRComponents

/-! NEW actual DFS return witnesses and ancestor cuts used in LR necessity.
The shallower opposing return is derived from the computed lowpoint, and both
interval cuts are actual parent occurrences of the relevant DFS vertices. -/
namespace PlanarHom.PlanarityLRRawConstraints
open Complexity PlanarityDepthFirstSearch PlanarityLRDirect

theorem returns_target_lt_source (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : ℕ) {b : ℕ} (hb : b∈returns g e) : targetHeight g b<height g (source g e) := by
  by_cases he : isTree g e=true
  · exact ((returns_tree_iff g he b).mp hb).2.2
  · have he' : isTree g e=false := Bool.eq_false_iff.mpr he
    have hback := mem_returns_back g e hb
    have hbe : b=e := by
      unfold returns at hb
      simp only [he',Bool.false_eq_true,if_false] at hb
      split_ifs at hb with heback
      · exact List.mem_singleton.mp hb
      · simp at hb
    simpa only [← hbe] using back_height_lt g hg hback

theorem returns_target_desc_source (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : ℕ) {b : ℕ} (hb : b∈returns g e) : Desc g (target g b) (source g e) := by
  have hbvalid := returns_valid g e hb
  have hsb := (source_target_valid g hg hbvalid).1
  have hback := mem_returns_back g e hb
  exact desc_of_height_le g hsb (Or.inr (back_target_ancestor g hg hback))
    (returns_source_descendant g hg e hb) (returns_target_lt_source g hg e hb).le

theorem returns_component (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (e : ℕ) {b : ℕ} (hb : b∈returns g e) :
    componentRoot g (source g b)=componentRoot g (source g e) :=
  (componentRoot_eq_of_desc g (source_target_valid g hg (returns_valid g e hb)).1
    (returns_source_descendant g hg e hb)).symm

/-- A constrained fork return has an actual strictly shallower return in the
other outgoing branch. No minimum-return oracle is assumed. -/
theorem exists_shallower_return_of_fork (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v e f b : ℕ} (he : e∈outgoing g v) (hf : f∈outgoing g v)
    (hb : b∈(forkBlock g e f).1) : ∃ c∈returns g f, targetHeight g c<targetHeight g b := by
  have hbs := List.mem_filter.mp hb
  have hcut : lowpoint g f<targetHeight g b := of_decide_eq_true hbs.2
  have hbound := returns_target_lt_source g hg e hbs.1
  rw [(outgoing_spec g he).2.2] at hbound
  by_contra hno
  push_neg at hno
  have hh : targetHeight g b≤lowpoint g f := (le_lowpoint_iff g f _).mpr
    ⟨by rw [(outgoing_spec g hf).2.2]; exact hbound.le, hno⟩
  omega

/-- The two actual descendant sources lie in the deeper target's subtree;
the shallower target lies outside it, while the deeper target lies outside
the fork vertex's proper subtree. These are precisely the two rank cuts. -/
theorem return_pair_cut_ancestry (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v e f b c : ℕ} (he : e∈outgoing g v) (hf : f∈outgoing g v)
    (hb : b∈returns g e) (hc : c∈returns g f) (hcb : targetHeight g c<targetHeight g b) :
    Desc g v (source g b) ∧ Desc g v (source g c) ∧
      ¬Desc g v (target g b) ∧
      Desc g (target g b) (source g b) ∧ Desc g (target g b) (source g c) ∧
      ¬Desc g (target g b) (target g c) ∧ 0<height g (target g b) ∧ b≠c := by
  have hsb := (source_target_valid g hg (returns_valid g e hb)).1
  have hsc := (source_target_valid g hg (returns_valid g f hc)).1
  have htb := (source_target_valid g hg (returns_valid g e hb)).2
  have htc := (source_target_valid g hg (returns_valid g f hc)).2
  have hvsb : Desc g v (source g b) := by
    simpa only [(outgoing_spec g he).2.2] using returns_source_descendant g hg e hb
  have hvsc : Desc g v (source g c) := by
    simpa only [(outgoing_spec g hf).2.2] using returns_source_descendant g hg f hc
  have htbv : Desc g (target g b) v := by
    simpa only [(outgoing_spec g he).2.2] using returns_target_desc_source g hg e hb
  have hlt : height g (target g b)<height g v := by
    simpa only [targetHeight,(outgoing_spec g he).2.2] using returns_target_lt_source g hg e hb
  refine ⟨hvsb,hvsc,?_,desc_trans g hsb htbv hvsb,desc_trans g hsc htbv hvsc,?_,?_,?_⟩
  · intro hd
    have hh := desc_height_le g htb hd
    omega
  · intro hd
    have hh := desc_height_le g htc hd
    change height g (target g c)<height g (target g b) at hcb
    omega
  · change height g (target g c)<height g (target g b) at hcb
    omega
  · intro h
    rw [h] at hcb
    omega

end PlanarHom.PlanarityLRRawConstraints
