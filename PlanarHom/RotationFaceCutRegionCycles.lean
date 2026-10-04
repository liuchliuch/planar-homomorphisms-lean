import PlanarHom.RotationFaceCutContour

/-! NEW relative cycle count of the true-side cut contour. Its only boundary
connectivity input is an actual finite permutation orbit statement, to be
proved for simple cycles in the next module. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {A : Finset E} {root : Dart E}
variable (C : R.FaceCut A root)

def regionLabel (a : {a : Dart E // C.side a=true}) : {v : V // C.InsideVertex v} ⊕ Unit :=
  if h : C.InsideVertex (G.dartPair a.val).1 then .inl ⟨_,h⟩ else .inr ()

theorem selected_reaches_boundary (a : {a : Dart E // C.side a=true})
    (hi : ¬C.InsideVertex (G.dartPair a.val).1) :
    ∃b : Dart E,b.1∈A ∧ C.side b=true ∧ C.cutContour.SameCycle a.val b := by
  have hn : ¬∀b : Dart E,(G.dartPair b).1=(G.dartPair a.val).1 → b.1∉A := by
    intro h
    exact hi (C.inside_of_selected_no_boundary h a.val rfl a.property)
  push_neg at hn
  obtain ⟨b,hb,hbe⟩ := hn
  obtain ⟨d,hd,_,hs⟩ := C.exists_boundary_sameCycle a.val b hbe hb.symm
  exact ⟨d,hd,(C.side_eq_of_sameCycle hs).symm.trans a.property,hs⟩

theorem exists_selected_boundary (hA : A.Nonempty) :
    ∃a : Dart E,a.1∈A ∧ C.side a=true := by
  obtain ⟨e,he⟩ := hA
  have hc := C.crosses e
  rw [decide_eq_true he] at hc
  by_cases hs : C.side (e,true)=true
  · exact ⟨(e,true),he,hs⟩
  · refine ⟨(e,false),he,?_⟩
    change (C.side (e,true) ^^ C.side (e,false))=true at hc
    have hh : C.side (e,true)=false := Bool.eq_false_iff.mpr hs
    simpa [hh] using hc

theorem regionLabel_surjective (hA : A.Nonempty)
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v) : Function.Surjective C.regionLabel := by
  intro x
  rcases x with v|u
  · obtain ⟨a,ha⟩ := hinc v.val
    refine ⟨⟨a,v.property a ha⟩,?_⟩
    have hv : C.InsideVertex (G.dartPair a).1 := ha ▸ v.property
    simp only [regionLabel,dif_pos hv,Sum.inl.injEq,Subtype.mk.injEq]
    exact Subtype.ext ha
  · obtain ⟨a,ha,hs⟩ := C.exists_selected_boundary hA
    have hi : ¬C.InsideVertex (G.dartPair a).1 := fun h=>(C.inside_excludes_boundary h a rfl) ha
    refine ⟨⟨a,hs⟩,?_⟩
    cases u
    simp [regionLabel,hi]

theorem sameCycle_iff_regionLabel
    (hbdy : ∀a b : Dart E,a.1∈A → b.1∈A → C.side a=C.side b → C.cutContour.SameCycle a b)
    (a b : {a : Dart E // C.side a=true}) :
    C.selectedContour.SameCycle a b ↔ C.regionLabel a=C.regionLabel b := by
  rw [selectedContour,Equiv.Perm.sameCycle_subtypePerm]
  by_cases ha : C.InsideVertex (G.dartPair a.val).1 <;>
    by_cases hb : C.InsideVertex (G.dartPair b.val).1
  · simp only [regionLabel,dif_pos ha,dif_pos hb,Sum.inl.injEq,Subtype.mk.injEq]
    constructor
    · intro h
      exact (C.sameCycle_host_of_no_boundary (fun d hd=>C.inside_excludes_boundary ha d hd)
        a.val b.val rfl h).symm
    · intro h
      exact C.sameCycle_of_no_boundary (fun d hd=>C.inside_excludes_boundary ha d hd)
        a.val b.val rfl h.symm
  · simp only [regionLabel,dif_pos ha,dif_neg hb,Sum.inl_ne_inr,iff_false]
    intro h
    have he := C.sameCycle_host_of_no_boundary (fun d hd=>C.inside_excludes_boundary ha d hd)
      a.val b.val rfl h
    exact hb (he ▸ ha)
  · simp only [regionLabel,dif_neg ha,dif_pos hb,Sum.inr_ne_inl,iff_false]
    intro h
    have he := C.sameCycle_host_of_no_boundary (fun d hd=>C.inside_excludes_boundary hb d hd)
      b.val a.val rfl h.symm
    exact ha (he ▸ hb)
  · simp only [regionLabel,dif_neg ha,dif_neg hb,iff_true]
    obtain ⟨x,hx,hsx,ha'⟩ := C.selected_reaches_boundary a ha
    obtain ⟨y,hy,hsy,hb'⟩ := C.selected_reaches_boundary b hb
    exact ha'.trans ((hbdy x y hx hy (hsx.trans hsy.symm)).trans hb'.symm)

/-- Exactly one selected contour follows the simple boundary; every wholly
inside vertex contributes its original cyclic row. -/
theorem count_selectedContour (hA : A.Nonempty)
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v)
    (hbdy : ∀a b : Dart E,a.1∈A → b.1∈A → C.side a=C.side b → C.cutContour.SameCycle a b) :
    FinitePermutationCycles.count C.selectedContour=Fintype.card {v : V // C.InsideVertex v}+1 := by
  rw [FinitePermutationCycles.count_eq_card_of_label C.selectedContour C.regionLabel
    (C.regionLabel_surjective hA hinc) (C.sameCycle_iff_regionLabel hbdy)]
  simp

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
