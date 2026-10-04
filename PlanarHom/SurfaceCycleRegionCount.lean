import PlanarHom.SurfaceCycleBoundaryOrbits

/-! NEW exact selected-contour count for a disjoint union of simple cycles.
Every inside vertex contributes one orbit and every boundary component one,
including unions whose individual components have nonzero homology. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E} {A : Finset E} {n : ℕ}
variable (F : CycleBoundaryFamily G A n) (C : R.FaceCut A root)

theorem not_inside_of_cycle (i : Fin n) {v : V} (hv : v∈(F.cycle i).cycleVertices) : ¬C.InsideVertex v := by
  obtain ⟨a,ha,hv⟩:=F.vertex_has_boundary i hv
  exact fun hi=>(C.inside_excludes_boundary hi a hv) ha

theorem inside_of_no_cycle (a : {a : Dart E // C.side a=true})
    (ha : ¬∃i,(G.dartPair a.val).1∈(F.cycle i).cycleVertices) : C.InsideVertex (G.dartPair a.val).1 := by
  apply C.inside_of_selected_no_boundary _ a.val rfl a.property
  intro b hb hm
  obtain ⟨i,hi⟩:=F.boundary_has_vertex b hm
  exact ha ⟨i,hb ▸ hi⟩

def familyRegionLabel (a : {a : Dart E // C.side a=true}) :
    {v : V // C.InsideVertex v}⊕Fin n :=
  if h:∃i,(G.dartPair a.val).1∈(F.cycle i).cycleVertices then .inr h.choose
  else .inl ⟨_,inside_of_no_cycle F C a h⟩

theorem familyRegionLabel_cycle (a : {a : Dart E // C.side a=true}) (i : Fin n)
    (hi : (G.dartPair a.val).1∈(F.cycle i).cycleVertices) : familyRegionLabel F C a=.inr i := by
  have h:∃j,(G.dartPair a.val).1∈(F.cycle j).cycleVertices:=⟨i,hi⟩
  rw [familyRegionLabel,dif_pos h,F.vertex_index_unique h.choose_spec hi]

theorem familyRegionLabel_inside (a : {a : Dart E // C.side a=true})
    (hi : C.InsideVertex (G.dartPair a.val).1) : familyRegionLabel F C a=.inl ⟨_,hi⟩ := by
  have hn:¬∃i,(G.dartPair a.val).1∈(F.cycle i).cycleVertices:=by
    rintro ⟨i,hh⟩
    exact not_inside_of_cycle F C i hh hi
  simp only [familyRegionLabel,dif_neg hn]

theorem exists_selected_cycle_boundary (i : Fin n) :
    ∃a : Dart E,a.1∈(F.cycle i).cycleEdges ∧ C.side a=true := by
  let j : Fin (F.cycle i).length:=⟨0,by have hh:=(F.cycle i).length_ge_two; omega⟩
  let a:=(F.cycle i).dart j
  have ha:a.1∈(F.cycle i).cycleEdges:=Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  by_cases hs:C.side a=true
  · exact ⟨a,ha,hs⟩
  · refine ⟨reversePerm E a,ha,?_⟩
    have hx:=C.crosses_dart a
    rw [decide_eq_true (F.cycle_edge_mem i ha),Bool.eq_false_iff.mpr hs] at hx
    simpa using hx

theorem familyRegionLabel_surjective (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v) :
    Function.Surjective (familyRegionLabel F C) := by
  intro x
  rcases x with v|i
  · obtain ⟨a,ha⟩:=hinc v.val
    have hs:C.side a=true:=v.property a ha
    have hv:C.InsideVertex (G.dartPair a).1:=ha ▸ v.property
    refine ⟨⟨a,hs⟩,?_⟩
    rw [familyRegionLabel_inside F C _ hv]
    exact congrArg Sum.inl (Subtype.ext ha)
  · obtain ⟨a,ha,hs⟩:=exists_selected_cycle_boundary F C i
    exact ⟨⟨a,hs⟩,familyRegionLabel_cycle F C _ i ((F.cycle i).vertex_mem_of_incident a ha)⟩

theorem sameCycle_iff_familyRegionLabel (a b : {a : Dart E // C.side a=true}) :
    C.selectedContour.SameCycle a b ↔ familyRegionLabel F C a=familyRegionLabel F C b := by
  rw [selectedContour,Equiv.Perm.sameCycle_subtypePerm]
  by_cases ha:∃i,(G.dartPair a.val).1∈(F.cycle i).cycleVertices <;>
    by_cases hb:∃i,(G.dartPair b.val).1∈(F.cycle i).cycleVertices
  · obtain ⟨i,hi⟩:=ha
    obtain ⟨j,hj⟩:=hb
    rw [familyRegionLabel_cycle F C a i hi,familyRegionLabel_cycle F C b j hj,Sum.inr.injEq]
    constructor
    · intro hab
      exact F.vertex_index_unique (family_host_sameCycle F C i a.val b.val hi hab) hj
    · intro hij
      subst j
      obtain ⟨x,hx,hsx,hax⟩:=C.selected_reaches_boundary a (not_inside_of_cycle F C i hi)
      obtain ⟨y,hy,hsy,hby⟩:=C.selected_reaches_boundary b (not_inside_of_cycle F C i hj)
      have hxi:=F.incident_cycle_edge i x hx (family_host_sameCycle F C i a.val x hi hax)
      have hyi:=F.incident_cycle_edge i y hy (family_host_sameCycle F C i b.val y hj hby)
      exact hax.trans ((family_boundary_sameCycle_of_side F C i x y hxi hyi (hsx.trans hsy.symm)).trans hby.symm)
  · obtain ⟨i,hi⟩:=ha
    have hbi:=inside_of_no_cycle F C b hb
    rw [familyRegionLabel_cycle F C a i hi,familyRegionLabel_inside F C b hbi]
    simp only [Sum.inr_ne_inl,iff_false]
    intro hab
    exact hb ⟨i,family_host_sameCycle F C i a.val b.val hi hab⟩
  · obtain ⟨j,hj⟩:=hb
    have hai:=inside_of_no_cycle F C a ha
    rw [familyRegionLabel_inside F C a hai,familyRegionLabel_cycle F C b j hj]
    simp only [Sum.inl_ne_inr,iff_false]
    intro hab
    exact ha ⟨j,family_host_sameCycle F C j b.val a.val hj hab.symm⟩
  · have hai:=inside_of_no_cycle F C a ha
    have hbi:=inside_of_no_cycle F C b hb
    rw [familyRegionLabel_inside F C a hai,familyRegionLabel_inside F C b hbi]
    simp only [Sum.inl.injEq,Subtype.mk.injEq]
    constructor
    · intro hab
      exact (C.sameCycle_host_of_no_boundary (fun d hd=>C.inside_excludes_boundary hai d hd) a.val b.val rfl hab).symm
    · intro hab
      exact C.sameCycle_of_no_boundary (fun d hd=>C.inside_excludes_boundary hai d hd) a.val b.val rfl hab.symm

include F in
/-- One selected boundary orbit per actual disjoint cycle; no genus premise. -/
theorem count_selectedContour_family (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v) :
    FinitePermutationCycles.count C.selectedContour=Fintype.card {v : V // C.InsideVertex v}+n := by
  rw [FinitePermutationCycles.count_eq_card_of_label C.selectedContour (familyRegionLabel F C)
    (familyRegionLabel_surjective F C hinc) (sameCycle_iff_familyRegionLabel F C)]
  simp

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
