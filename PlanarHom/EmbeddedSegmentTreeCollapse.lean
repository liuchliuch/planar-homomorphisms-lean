import PlanarHom.EmbeddedSegmentTree

/-! NEW proper collapse and punctured-plane complement for a genuine finite
embedded segment tree. Leaf contraction preserves the retained literal tree
support by fixing nonadjacent pieces and mapping adjacent radial pieces onto
themselves. -/
noncomputable section
open Set Topology
open scoped Convex
namespace PlanarHom.MultiGraph.EmbeddedSegmentTree
local instance : DecidableEq Plane := Classical.decEq _
variable {r : Plane} {V : Finset Plane} {E : Finset (Plane×Plane)}

/-- Collapse one attached leaf while preserving the entire old tree as a set and
fixing every one of its vertices. The scale is derived from compact separation. -/
theorem exists_leafCollapse (T : EmbeddedSegmentTree r V E) (a b : Plane)
    (hb : b∈V) (hab : a≠b)
    (hcontact : ∀ x, x∈[a -[ℝ] b] → x∈segmentTreeSupport V E → x=b)
    {K : Set Plane} (hK : IsCompact K) (hKdis : Disjoint K [a -[ℝ] b]) :
    ∃ C : ProperPlaneCollapse [a -[ℝ] b] b,
      (∀ x∈K, C.map x=x) ∧ C.map '' segmentTreeSupport V E = segmentTreeSupport V E ∧
      ∀ v∈V, C.map v=v := by
  let far : Finset (Plane×Plane) := E.filter (fun e => e.1≠b ∧ e.2≠b)
  let L := K ∪ segmentTreeSupport (V.erase b) far
  have hL : IsCompact L := hK.union (isCompact_support _ _)
  have hLdis : Disjoint L [a -[ℝ] b] := by
    apply Set.disjoint_left.mpr
    intro x hx hfirst
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hKdis hx hfirst
    rcases hx with hv | hedge
    · have hv' := Finset.mem_erase.mp hv
      exact hv'.1 (hcontact x hfirst (vertex_mem_support hv'.2))
    · simp only [Set.mem_iUnion] at hedge
      obtain ⟨e,he,hseg⟩ := hedge
      have he' := Finset.mem_filter.mp he
      have hx := hcontact x hfirst (piece_subset_support he'.1 hseg)
      have hbseg : b∈[e.1 -[ℝ] e.2] := hx ▸ hseg
      rcases T.vertex_piece_contact hb he'.1 hbseg with hh | hh
      · exact he'.2.1 hh.symm
      · exact he'.2.2 hh.symm
  obtain ⟨C,hproper,hsur,_,_⟩ :=
    SegmentCollapse.exists_properLocalizedSegmentCollapse a b hab hL hLdis
  have hfix (v : Plane) (hv : v∈V) : C.map v=v := by
    by_cases heq : v=b
    · subst v; exact C.target
    · exact C.fixed v (Or.inr (Or.inl (Finset.mem_erase.mpr ⟨heq,hv⟩)))
  have hpiece (e : Plane×Plane) (he : e∈E) : C.map '' [e.1 -[ℝ] e.2] = [e.1 -[ℝ] e.2] := by
    have hend := T.endpoints_mem he
    by_cases h₁ : e.1=b
    · rw [h₁]
      exact C.ray_image e.2 (hfix e.2 hend.2)
    by_cases h₂ : e.2=b
    · rw [h₂,segment_symm ℝ e.1 b]
      exact C.ray_image e.1 (hfix e.1 hend.1)
    have hpoint (x : Plane) (hx : x∈[e.1 -[ℝ] e.2]) : C.map x=x := by
      apply C.fixed
      exact Or.inr (piece_subset_support (Finset.mem_filter.mpr ⟨he,h₁,h₂⟩) hx)
    apply Set.ext
    intro x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rwa [hpoint y hy]
    · intro hx
      exact ⟨x,hx,hpoint x hx⟩
  have hsupport : C.map '' segmentTreeSupport V E = segmentTreeSupport V E := by
    ext x
    constructor
    · rintro ⟨y,(hy | hy),rfl⟩
      · rw [hfix y hy]
        exact Or.inl hy
      · simp only [Set.mem_iUnion] at hy
        obtain ⟨e,he,hseg⟩ := hy
        apply piece_subset_support he
        rw [← hpiece e he]
        exact ⟨y,hseg,rfl⟩
    · rintro (hv | hedge)
      · exact ⟨x,Or.inl hv,hfix x hv⟩
      · simp only [Set.mem_iUnion] at hedge
        obtain ⟨e,he,hseg⟩ := hedge
        rw [← hpiece e he] at hseg
        obtain ⟨y,hy,hyx⟩ := hseg
        exact ⟨y,piece_subset_support he hy,hyx⟩
  let P : ProperPlaneCollapse [a -[ℝ] b] b := {
    map := C.map
    proper := hproper
    onto := hsur
    fibers := C.fibers
    center_mem := right_mem_segment ℝ a b
    center_fixed := C.target }
  exact ⟨P,fun x hx => C.fixed x (Or.inl hx),hsupport,hfix⟩

/-- A finite embedded segment tree admits a proper onto ambient collapse with
exactly the tree as its exceptional fiber, fixing any disjoint compact set. -/
theorem exists_properCollapse (T : EmbeddedSegmentTree r V E)
    {K : Set Plane} (hK : IsCompact K) (hdis : Disjoint K (segmentTreeSupport V E)) :
    ∃ C : ProperPlaneCollapse (segmentTreeSupport V E) r, ∀ x∈K, C.map x=x := by
  induction T with
  | root =>
      have hs : segmentTreeSupport {r} ∅ = {r} := by simp [segmentTreeSupport]
      rw [hs]
      exact ⟨ProperPlaneCollapse.singleton r,fun _ _ => rfl⟩
  | @leaf V E T a b hb hab hcontact ih =>
      rw [support_leaf a b hb] at hdis ⊢
      have hfirst : Disjoint K [a -[ℝ] b] := hdis.mono_right Set.subset_union_left
      have hold : Disjoint K (segmentTreeSupport V E) := hdis.mono_right Set.subset_union_right
      obtain ⟨C,hCfix,hCsupport,hCvertices⟩ := exists_leafCollapse T a b hb hab hcontact hK hfirst
      obtain ⟨D,hDfix⟩ := ih hold
      refine ⟨C.merge D (vertex_mem_support hb) hCsupport (hCvertices r T.root_mem),?_⟩
      intro x hx
      change D.map (C.map x)=x
      rw [hCfix x hx,hDfix x hx]

/-- Genuine complement chart, derived from leaf-incidence geometry alone. -/
theorem exists_complementHomeomorph (T : EmbeddedSegmentTree r V E) :
    Nonempty ({x : Plane // x∉segmentTreeSupport V E} ≃ₜ {y : Plane // y≠r}) := by
  obtain ⟨C,_⟩ := T.exists_properCollapse isCompact_empty (Set.empty_disjoint _)
  exact ⟨C.complementHomeomorph⟩

end PlanarHom.MultiGraph.EmbeddedSegmentTree
