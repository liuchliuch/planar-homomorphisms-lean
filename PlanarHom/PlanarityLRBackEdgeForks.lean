import PlanarHom.PlanarityLRBackWords
import PlanarHom.PlanarityLROutgoingOrder

/-! NEW literal divergence-fork extraction for any two back occurrences.
The common ancestor and outgoing branches come from the actual computed DFS. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityDepthFirstSearch PlanarityLRRawConstraints

theorem exists_deepest_common_ancestor (g : MixedCode) {u v : ℕ}
    (hu : u < g.vertices) (hv : v < g.vertices)
    (hr : componentRoot g u=componentRoot g v) :
    ∃ w, w < g.vertices ∧ Desc g w u ∧ Desc g w v ∧
      ∀ x, x < g.vertices → Desc g x u → Desc g x v → height g x≤height g w := by
  let S := (Finset.range g.vertices).filter (fun w => Desc g w u ∧ Desc g w v)
  have hr₁ := componentRoot_spec g hu
  have hr₂ : Desc g (componentRoot g u) v := by rw [hr]; exact (componentRoot_spec g hv).2.1
  have hs : S.Nonempty := ⟨componentRoot g u,by simp only [S,Finset.mem_filter,Finset.mem_range]; exact ⟨hr₁.1,hr₁.2.1,hr₂⟩⟩
  obtain ⟨w,hw,hmax⟩ := Finset.exists_max_image S (height g) hs
  have hm : w < g.vertices ∧ Desc g w u ∧ Desc g w v := by simpa only [S,Finset.mem_filter,Finset.mem_range] using hw
  refine ⟨w,hm.1,hm.2.1,hm.2.2,?_⟩
  intro x hx hxu hxv
  apply hmax x
  simp only [S,Finset.mem_filter,Finset.mem_range]
  exact ⟨hx,hxu,hxv⟩

/-- The first actual outgoing occurrence toward a back-edge event: either that
back occurrence itself, or the literal tree child toward its source. -/
structure BackBranch (g : MixedCode) (v b e : ℕ) : Prop where
  outgoing : e ∈ PlanarityLRRawConstraints.outgoing g v
  branch : (e=b ∧ source g b=v) ∨ (isTree g e=true ∧ Desc g (target g e) (source g b))

theorem exists_back_branch (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {v b : ℕ} (hb : isBack g b=true) (hv : Desc g v (source g b)) : ∃ e, BackBranch g v b e := by
  have hbval := (of_decide_eq_true hb).1
  have hs := (source_target_valid g hg hbval).1
  by_cases heq : source g b=v
  · refine ⟨b,?_,Or.inl ⟨rfl,heq⟩⟩
    simp [PlanarityLRRawConstraints.outgoing,hbval,hb,heq]
  · have ha : v ∈ ancestors g (source g b) := hv.resolve_left (Ne.symm heq)
    obtain ⟨w,hw,hpar,hdesc,hh⟩ := exists_child_toward g hs ha
    have hp := parentEdge_tree g hg hw (by omega)
    have heval := (of_decide_eq_true hp.1).1
    refine ⟨parentEdge g w,?_,Or.inr ⟨hp.1,?_⟩⟩
    · have hsource : source g (parentEdge g w)=v := hp.2.2.trans hpar
      simp [PlanarityLRRawConstraints.outgoing,heval,hp.1,hsource]
    · simpa only [hp.2.1] using hdesc

 theorem BackBranch.return_mem {g : MixedCode} {v b e : ℕ} (H : BackBranch g v b e)
    (hb : isBack g b=true) (ht : targetHeight g b < height g v) : b ∈ returns g e := by
  rcases H.branch with ⟨rfl,_⟩ | ⟨he,hd⟩
  · have hnt := (of_decide_eq_true hb).2.1
    simp [returns,hnt,hb]
  · apply (returns_tree_iff g he b).mpr
    exact ⟨hb,hd,by simpa only [(outgoing_spec g H.outgoing).2.2] using ht⟩

/-- Every pair of distinct back events in one component diverges at two actual,
distinct outgoing occurrences of a deepest common source ancestor. -/
theorem exists_back_edge_fork (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {b c : ℕ} (hb : isBack g b=true) (hc : isBack g c=true) (hne : b≠c)
    (hr : componentRoot g (source g b)=componentRoot g (source g c)) :
    ∃ v e f, v < g.vertices ∧ Desc g v (source g b) ∧ Desc g v (source g c) ∧
      BackBranch g v b e ∧ BackBranch g v c f ∧ e≠f := by
  have hsb := (source_target_valid g hg (of_decide_eq_true hb).1).1
  have hsc := (source_target_valid g hg (of_decide_eq_true hc).1).1
  obtain ⟨v,hv,hvb,hvc,hmax⟩ := exists_deepest_common_ancestor g hsb hsc hr
  obtain ⟨e,he⟩ := exists_back_branch g hg hb hvb
  obtain ⟨f,hf⟩ := exists_back_branch g hg hc hvc
  refine ⟨v,e,f,hv,hvb,hvc,he,hf,?_⟩
  intro hef
  subst f
  rcases he.branch with ⟨heb,_⟩ | ⟨het,hed⟩ <;> rcases hf.branch with ⟨hec,_⟩ | ⟨het',hed'⟩
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
    rw [(outgoing_spec g he.outgoing).2.2] at hstep
    omega

end PlanarHom.PlanarityLRDirect
