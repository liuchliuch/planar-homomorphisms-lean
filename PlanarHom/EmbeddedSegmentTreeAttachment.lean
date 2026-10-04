import PlanarHom.EmbeddedSegmentTreeCollapse
import PlanarHom.PolygonalSegmentIncidence

/-! NEW bridge from actual simple polygonal edge chains to finite embedded
segment-tree insertion. Each piece's leaf-contact premise is derived from the
chain's proved self-separation and its contact with the old tree. -/
noncomputable section
open Set
open scoped Convex
namespace PlanarHom.MultiGraph.EmbeddedSegmentTree
open Polygonal
local instance : DecidableEq Plane := Classical.decEq _
variable {r : Plane} {V : Finset Plane} {E : Finset (Plane×Plane)}

/-- Attach a whole polygonal leaf arc by deriving, rather than supplying,
every individual segment's insertion condition. -/
theorem attach_simpleChain (T : EmbeddedSegmentTree r V E) {a z : Plane}
    (p : Chain Set.univ a z) (hp : p.IsSimple) (ha : a∈V)
    (hcontact : ∀ x, x∈p.support → x∈segmentTreeSupport V E → x=a) :
    ∃ V' E', EmbeddedSegmentTree r V' E' ∧ V⊆V' ∧ z∈V' ∧
      segmentTreeSupport V' E' = segmentTreeSupport V E ∪ p.support := by
  induction p generalizing V E with
  | nil a haU =>
      refine ⟨V,E,T,Finset.Subset.refl _,ha,?_⟩
      rw [Chain.support_nil]
      exact (Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr (vertex_mem_support ha))).symm
  | @cons a b z h q ih =>
      have hpiece : ∀ x, x∈[b -[ℝ] a] → x∈segmentTreeSupport V E → x=a := by
        intro x hx hS
        exact hcontact x (by rw [Chain.support_cons]; exact Or.inl (by simpa [segment_symm] using hx)) hS
      let T' := T.leaf b a ha hp.1.symm hpiece
      have hb : b∈insert b V := Finset.mem_insert_self _ _
      have hqcontact : ∀ x, x∈q.support → x∈segmentTreeSupport (insert b V) (insert (b,a) E) → x=b := by
        intro x hx hS
        rw [support_leaf b a ha] at hS
        rcases hS with hseg | hold
        · exact hp.2.2 x (by simpa [segment_symm] using hseg) hx
        · have hxa := hcontact x (by rw [Chain.support_cons]; exact Or.inr hx) hold
          exact False.elim (Chain.simple_source_notMem_tail h q hp (hxa ▸ hx))
      obtain ⟨V',E',hout,hsub,hz,hS⟩ := ih T' hp.2.1 hb hqcontact
      refine ⟨V',E',hout,(Finset.subset_insert _ _).trans hsub,hz,?_⟩
      rw [hS,support_leaf b a ha,Chain.support_cons,segment_symm ℝ b a]
      ext x
      simp only [Set.mem_union]
      tauto

/-- Every simple finite polygonal arc is the support of an explicitly generated
embedded segment tree rooted at its source. -/
theorem exists_tree_of_simpleChain {a z : Plane} (p : Chain Set.univ a z) (hp : p.IsSimple) :
    ∃ V E, EmbeddedSegmentTree a V E ∧ segmentTreeSupport V E = p.support := by
  obtain ⟨V,E,T,_,_,hS⟩ := (EmbeddedSegmentTree.root (r := a)).attach_simpleChain p hp
    (by simp) (by intro x _ hx; simpa [segmentTreeSupport] using hx)
  refine ⟨V,E,T,?_⟩
  rw [hS]
  have ha : segmentTreeSupport {a} ∅ ⊆ p.support := by
    intro x hx
    have he : x=a := by simpa [segmentTreeSupport] using hx
    exact he ▸ p.source_mem_support
  exact Set.union_eq_self_of_subset_left ha

/-- Unconditional complement homeomorphism of a simple polygonal arc. -/
theorem simpleChain_complementHomeomorph {a z : Plane}
    (p : Chain Set.univ a z) (hp : p.IsSimple) :
    Nonempty ({x : Plane // x∉p.support} ≃ₜ {y : Plane // y≠a}) := by
  obtain ⟨V,E,T,hS⟩ := exists_tree_of_simpleChain p hp
  obtain ⟨H⟩ := T.exists_complementHomeomorph
  have heq : p.supportᶜ = (segmentTreeSupport V E)ᶜ := congrArg Set.compl hS.symm
  exact ⟨(Homeomorph.setCongr heq).trans H⟩

end PlanarHom.MultiGraph.EmbeddedSegmentTree
