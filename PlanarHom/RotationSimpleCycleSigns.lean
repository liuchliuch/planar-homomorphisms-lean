import PlanarHom.RotationSimpleCycleCut
import PlanarHom.RotationFaceCutSigns

/-! NEW relative Kasteleyn parity for an actual simple occurrence cycle. -/
set_option maxRecDepth 3000
set_option maxHeartbeats 800000
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E}
variable (c : DirectedSimpleCycle G) (C : R.FaceCut c.cycleEdges root)

theorem cycleEdges_card : c.cycleEdges.card=c.length := by
  rw [DirectedSimpleCycle.cycleEdges,Finset.card_image_of_injective _ c.edge_injective]
  simp

 theorem cutBoundaryProduct_simpleCycle (orientation : E→Bool)
    (heven : Even c.length) : C.cutBoundaryProduct orientation=boundarySign orientation c.cycleDarts := by
  let i₀ : Fin c.length := ⟨0,by have := c.length_ge_two; omega⟩
  have hs : ∀i,C.side (c.dart i)=C.side (c.dart i₀) :=
    fun i=>C.side_eq_of_sameCycle (forward_sameCycle c C i i₀)
  have hfactor : ∀i : Fin c.length,
      (if C.side ((c.dart i).1,true) then dartSign orientation ((c.dart i).1,true)
        else dartSign orientation ((c.dart i).1,false))=
      if C.side (c.dart i₀) then dartSign orientation (c.dart i) else -dartSign orientation (c.dart i) := by
    intro i
    have hm : (c.dart i).1∈c.cycleEdges := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hc := C.crosses (c.dart i).1
    rw [decide_eq_true hm] at hc
    change (C.side ((c.dart i).1,true) ^^ C.side ((c.dart i).1,false))=true at hc
    rw [←hs i]
    generalize hda : c.dart i=a at hc ⊢
    rcases a with ⟨e,b⟩
    cases b <;> cases ht : C.side (e,true) <;> cases hf : C.side (e,false) <;>
      simp_all [dartSign]
    all_goals cases orientation e <;> norm_num

  unfold cutBoundaryProduct
  rw [←Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  change (∏e∈c.cycleEdges, (if C.side (e,true) then dartSign orientation (e,true)
    else dartSign orientation (e,false)))=_
  change (∏e∈Finset.univ.image (fun i : Fin c.length=>(c.dart i).1),
    (if C.side (e,true) then dartSign orientation (e,true) else dartSign orientation (e,false)))=_
  rw [Finset.prod_image (fun _ _ _ _ h=>c.edge_injective h)]
  simp_rw [hfactor]
  have hp : (∏i : Fin c.length,dartSign orientation (c.dart i))=boundarySign orientation c.cycleDarts := by
    simp [boundarySign,DirectedSimpleCycle.cycleDarts,List.map_ofFn,List.prod_ofFn]
  cases hzero : C.side (c.dart i₀)
  · simp only [Bool.false_eq_true,if_false,Finset.prod_neg,
      Finset.card_univ,Fintype.card_fin,heven.neg_one_pow,mul_one,one_mul]
    exact hp
  · simp only [if_true]
    exact hp

 theorem boundarySign_eq_relative_parity (orientation : E→Bool)
    (heven : Even c.length)
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v)
    (hfaces : FinitePermutationCycles.CycleProductLaw C.selectedFace (fun a=>dartSign orientation a.val)) :
    boundarySign orientation c.cycleDarts=(-1:ℤ)^(c.length+Fintype.card {v : V // C.InsideVertex v}+1) := by
  rw [←cutBoundaryProduct_simpleCycle c C orientation heven,C.cutBoundaryProduct_eq_sign orientation hfaces,
    FinitePermutationCycles.sign_coe_eq_pow_card_add_count,C.selected_card,
    count_selectedContour_simpleCycle c C hinc,cycleEdges_card c]
  have he : 2*C.internalCount+c.length+(Fintype.card {v : V // C.InsideVertex v}+1)=
      2*C.internalCount+(c.length+Fintype.card {v : V // C.InsideVertex v}+1) := by omega
  rw [he,pow_add,pow_mul]
  norm_num

 theorem boundarySign_eq_neg_one (orientation : E→Bool)
    (heven : Even c.length)
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v)
    (hfaces : FinitePermutationCycles.CycleProductLaw C.selectedFace (fun a=>dartSign orientation a.val))
    (hinside : Even (Fintype.card {v : V // C.InsideVertex v})) :
    boundarySign orientation c.cycleDarts= -1 := by
  rw [boundarySign_eq_relative_parity c C orientation heven hinc hfaces,pow_add,pow_add,
    heven.neg_one_pow,hinside.neg_one_pow]
  norm_num

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
