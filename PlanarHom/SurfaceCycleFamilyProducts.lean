import PlanarHom.SurfaceCycleRegionCount
import PlanarHom.RotationSimpleCycleSigns

/-! NEW product and parity identities for every disjoint cycle boundary. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph.CycleBoundaryFamily
open Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : MultiGraph V E} {A : Finset E} {n : ℕ} (F : CycleBoundaryFamily G A n)

theorem edge_disjoint (i j : Fin n) (hij : i≠j) : Disjoint (F.cycle i).cycleEdges (F.cycle j).cycleEdges := by
  apply Finset.disjoint_left.mpr
  intro e hi hj
  exact hij (F.vertex_index_unique ((F.cycle i).vertex_mem_of_incident (e,true) hi)
    ((F.cycle j).vertex_mem_of_incident (e,true) hj))

theorem biUnion_edges : Finset.univ.biUnion (fun i=>(F.cycle i).cycleEdges)=A := by
  ext e
  simpa only [Finset.mem_biUnion,Finset.mem_univ,true_and] using (F.edge_cover e).symm

theorem prod_boundary_edges {K : Type*} [CommMonoid K] (w : E→K) :
    (∏e∈A,w e)=∏i : Fin n,∏e∈(F.cycle i).cycleEdges,w e := by
  conv_lhs => rw [←F.biUnion_edges]
  exact Finset.prod_biUnion (fun i _ j _ hij=>F.edge_disjoint i j hij)

theorem card_boundary_edges : A.card=∑i : Fin n,(F.cycle i).length := by
  conv_lhs => rw [←F.biUnion_edges]
  rw [Finset.card_biUnion (fun i _ j _ hij=>F.edge_disjoint i j hij)]
  apply Finset.sum_congr rfl
  intro i _
  rw [DirectedSimpleCycle.cycleEdges,Finset.card_image_of_injective _ (F.cycle i).edge_injective]
  simp

theorem boundary_even (heven : ∀i,Even (F.cycle i).length) : Even A.card := by
  rw [F.card_boundary_edges]
  exact Finset.even_sum _ (fun i _=>heven i)

end PlanarHom.MultiGraph.CycleBoundaryFamily
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E} {A : Finset E} {n : ℕ}
variable (F : CycleBoundaryFamily G A n) (C : R.FaceCut A root)

theorem family_cycle_product (orientation : E→Bool) (i : Fin n) (heven : Even (F.cycle i).length) :
    (∏e∈(F.cycle i).cycleEdges,
      (if C.side (e,true) then dartSign orientation (e,true) else dartSign orientation (e,false)))=
      boundarySign orientation (F.cycle i).cycleDarts := by
  let c:=F.cycle i
  have hcEven : Even c.length:=heven
  let j₀ : Fin c.length:=⟨0,by have hh:=c.length_ge_two; omega⟩
  have hs : ∀j,C.side (c.dart j)=C.side (c.dart j₀):=
    fun j=>C.side_eq_of_sameCycle (family_forward_sameCycle F C i j j₀)
  have hfactor : ∀j : Fin c.length,
      (if C.side ((c.dart j).1,true) then dartSign orientation ((c.dart j).1,true)
       else dartSign orientation ((c.dart j).1,false))=
      if C.side (c.dart j₀) then dartSign orientation (c.dart j) else -dartSign orientation (c.dart j) := by
    intro j
    have hc:=C.crosses (c.dart j).1
    rw [decide_eq_true (F.cycle_dart_mem i j)] at hc
    change (C.side ((c.dart j).1,true) ^^ C.side ((c.dart j).1,false))=true at hc
    rw [←hs j]
    generalize hda:c.dart j=a at hc ⊢
    rcases a with ⟨e,b⟩
    cases b <;> cases ht:C.side (e,true) <;> cases hf:C.side (e,false) <;> simp_all [dartSign]
    all_goals cases orientation e <;> norm_num
  change (∏e∈Finset.univ.image (fun j : Fin c.length=>(c.dart j).1),_)=_
  rw [Finset.prod_image (fun _ _ _ _ h=>c.edge_injective h)]
  simp_rw [hfactor]
  have hp : (∏j : Fin c.length,dartSign orientation (c.dart j))=boundarySign orientation c.cycleDarts := by
    simp [boundarySign,DirectedSimpleCycle.cycleDarts,List.map_ofFn,List.prod_ofFn]
  cases hzero:C.side (c.dart j₀)
  · simp only [Bool.false_eq_true,if_false,Finset.prod_neg,Finset.card_univ,Fintype.card_fin,
      hcEven.neg_one_pow,mul_one,one_mul]
    exact hp
  · simp only [if_true]
    exact hp

theorem cutBoundaryProduct_family (orientation : E→Bool) (heven : ∀i,Even (F.cycle i).length) :
    C.cutBoundaryProduct orientation=∏i : Fin n,boundarySign orientation (F.cycle i).cycleDarts := by
  unfold cutBoundaryProduct
  rw [←Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [F.prod_boundary_edges]
  exact Finset.prod_congr rfl (fun i _=>family_cycle_product F C orientation i (heven i))

/-- The full union boundary has sign (-1)^n once interior matching parity is
established, even if its component cycles are individually non-null. -/
theorem family_boundary_product_eq (orientation : E→Bool)
    (heven : ∀i,Even (F.cycle i).length)
    (hinc : ∀v : V,∃a : Dart E,(G.dartPair a).1=v)
    (hfaces : FinitePermutationCycles.CycleProductLaw C.selectedFace (fun a=>dartSign orientation a.val))
    (hinside : Even (Fintype.card {v : V // C.InsideVertex v})) :
    (∏i : Fin n,boundarySign orientation (F.cycle i).cycleDarts)=(-1:ℤ)^n := by
  rw [←cutBoundaryProduct_family F C orientation heven,C.cutBoundaryProduct_eq_sign orientation hfaces,
    FinitePermutationCycles.sign_coe_eq_pow_card_add_count,C.selected_card,count_selectedContour_family F C hinc]
  have he : 2*C.internalCount+A.card+(Fintype.card {v : V // C.InsideVertex v}+n)=
      2*C.internalCount+(A.card+Fintype.card {v : V // C.InsideVertex v})+n := by omega
  rw [he,pow_add,pow_add,pow_mul,(F.boundary_even heven).add hinside |>.neg_one_pow]
  norm_num

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
