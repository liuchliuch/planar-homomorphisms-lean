import PlanarHom.SurfaceCycleFamilyProducts
import PlanarHom.SurfaceMatchingBoundaryParity

/-! NEW full union parity gate. The entire matching symmetric difference is
null-homologous; its individual alternating cycles need not be. The resulting
product is exactly the one in the unrestricted matching-sign telescope. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

theorem matchingCycleFamily_signProduct_of_null
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N : Finset E} (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
    {n : ℕ} (F : CycleBoundaryFamily G (symmDiff M N) n)
    (heven : ∀i,Even (F.cycle i).length)
    (hnull : R.homologyClass (R.evenSubgraphCycle (symmDiff M N) (hM.symmDiff_even hN))=0) :
    (∏i : Fin n,-boundarySign orientation (F.cycle i).cycleDarts)=1 := by
  obtain ⟨C⟩:=R.exists_faceCut_of_null root _ _ hnull
  have hp:=FaceCut.family_boundary_product_eq F C orientation heven hM.exists_dart_at
    (C.selectedFace_productLaw_of_except orientation hfaces) (C.matching_symmDiff_inside_even hM hN)
  rw [Finset.prod_neg,Finset.card_univ,Fintype.card_fin,hp,←pow_add]
  exact (show Even (n+n) from ⟨n,rfl⟩).neg_one_pow

end PlanarHom.PlanarityLRRealization.RotationRows
