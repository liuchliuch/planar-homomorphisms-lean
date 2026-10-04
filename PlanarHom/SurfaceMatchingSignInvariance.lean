import PlanarHom.SurfaceNullUnionSigns
import PlanarHom.SurfaceMatchingHomology
import PlanarHom.OccurrenceMatchingCycleDecomposition
import PlanarHom.OccurrenceMatchingCycleProduct

/-! NEW full homology-class invariance of the actual occurrence matching
Pfaffian sign. The complete disjoint symmetric-difference cycle decomposition
is constructed internally. Individual cycles may have nonzero homology. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [LinearOrder V] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

theorem matchingPfaffianSign_eq_of_null
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N : Finset E} (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
    (hnull : R.homologyClass (R.evenSubgraphCycle (symmDiff M N) (hM.symmDiff_even hN))=0) :
    G.matchingPfaffianSign (R:=ℤ) orientation M=G.matchingPfaffianSign orientation N := by
  obtain ⟨n,⟨d⟩⟩:=hM.exists_cycleDecomposition hN
  rw [d.matchingPfaffianSign_product orientation,
    R.matchingCycleFamily_signProduct_of_null root orientation hfaces hM hN d.family d.even_length hnull,mul_one]

/-- Actual matching signs descend to the actual finite face-boundary quotient. -/
theorem matchingPfaffianSign_eq_of_homology
    (root : Dart E) (orientation : E→Bool)
    (hfaces : ∀q : R.Face,q≠R.faceOf root →
      (∏a : {a : Dart E // R.faceOf a=q},dartSign orientation a.val)=
        (-1:ℤ)^(Fintype.card {a : Dart E // R.faceOf a=q}+1))
    {M N M₀ : Finset E} (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
    (h₀ : G.PerfectMatching M₀)
    (heq : R.matchingHomologyClass M₀ h₀ M hM=R.matchingHomologyClass M₀ h₀ N hN) :
    G.matchingPfaffianSign (R:=ℤ) orientation M=G.matchingPfaffianSign orientation N :=
  R.matchingPfaffianSign_eq_of_null root orientation hfaces hM hN
    ((R.matchingHomologyClass_eq_iff hM hN h₀).mp heq)

end PlanarHom.PlanarityLRRealization.RotationRows
