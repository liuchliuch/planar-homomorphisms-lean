import PlanarHom.SurfaceFaceRoots
import PlanarHom.SurfaceMatchingSignInvariance

/-! NEW disconnected matching-sign invariance with one actual omitted face
per component. Empty dart types are handled directly, with no dummy face. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

theorem matchingPfaffianSign_eq_of_null_roots
    (S : R.FaceRoots) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,S.root q≠q→
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N : Finset E} (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
    (hnull : R.homologyClass (R.evenSubgraphCycle (symmDiff M N) (hM.symmDiff_even hN))=0) :
    G.matchingPfaffianSign (R:=ℤ) orientation M=G.matchingPfaffianSign orientation N := by
  rcases isEmpty_or_nonempty E with hE|hE
  · letI:=hE
    have he:M=N:=by ext e; exact isEmptyElim e
    rw [he]
  · letI:=hE
    obtain ⟨n,⟨d⟩⟩:=hM.exists_cycleDecomposition hN
    obtain ⟨root,C,hzero⟩:=S.exists_faceCut_of_null _ _ hnull
    have hp:=FaceCut.family_boundary_product_eq d.family C orientation d.even_length hM.exists_dart_at
      (C.selectedFace_productLaw_of_roots S hzero orientation hfaces) (C.matching_symmDiff_inside_even hM hN)
    have hprod:(∏i : Fin n,-boundarySign orientation (d.family.cycle i).cycleDarts)=1:=by
      rw [Finset.prod_neg,Finset.card_univ,Fintype.card_fin,hp,←pow_add]
      exact (show Even (n+n) from ⟨n,rfl⟩).neg_one_pow
    rw [d.matchingPfaffianSign_product orientation,hprod,mul_one]

theorem matchingPfaffianSign_eq_of_homology_roots
    (S : R.FaceRoots) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,S.root q≠q→
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N M₀ : Finset E} (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
    (h₀ : G.PerfectMatching M₀)
    (heq : R.matchingHomologyClass M₀ h₀ M hM=R.matchingHomologyClass M₀ h₀ N hN) :
    G.matchingPfaffianSign (R:=ℤ) orientation M=G.matchingPfaffianSign orientation N :=
  R.matchingPfaffianSign_eq_of_null_roots S orientation hfaces hM hN
    ((R.matchingHomologyClass_eq_iff hM hN h₀).mp heq)

end PlanarHom.PlanarityLRRealization.RotationRows
