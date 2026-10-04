import PlanarHom.SurfaceRotationFacePotentials

/-! NEW semantic specification of computed binary quotient coordinates.
The executable Gaussian layer constructs these fields from literal incidence
and face rows. No matching, orientation or sign assertion is part of the data. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn Module
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

structure QuotientCoordinates (d : ℕ) where
  encode : (E→ZMod 2)→ₗ[ZMod 2](Fin d→ZMod 2)
  lift : (Fin d→ZMod 2)→ₗ[ZMod 2] R.cycleSpace
  encode_lift : ∀x,encode (lift x).val=x
  kernel : ∀c : R.cycleSpace,encode c.val=0 ↔ R.homologyClass c=0

namespace QuotientCoordinates
variable {R} {d : ℕ} (D : R.QuotientCoordinates d)

theorem same_coordinates_iff (a b : R.cycleSpace) :
    D.encode a.val=D.encode b.val ↔ R.homologyClass a=R.homologyClass b := by
  have hh:=D.kernel (a+b)
  change D.encode (a.val+b.val)=0 ↔ R.homologyClass (a+b)=0 at hh
  simpa only [map_add,add_eq_zero_iff_eq_neg,ZModModule.neg_eq_self] using hh

theorem lift_encode_class (c : R.cycleSpace) :
    R.homologyClass (D.lift (D.encode c.val))=R.homologyClass c :=
  (D.same_coordinates_iff _ c).mp (D.encode_lift _)

def onCycles : R.cycleSpace→ₗ[ZMod 2](Fin d→ZMod 2) := D.encode.comp R.cycleSpace.subtype

theorem onCycles_surjective : Function.Surjective D.onCycles :=
  fun x=>⟨D.lift x,D.encode_lift x⟩

theorem onCycles_kernel : LinearMap.ker D.onCycles=R.faceBoundariesInCycles := by
  ext c
  change D.encode c.val=0 ↔ c∈R.faceBoundariesInCycles
  rw [D.kernel]
  exact Submodule.Quotient.mk_eq_zero R.faceBoundariesInCycles

include D in
/-- The computed quotient dimension is proved from its actual kernel and
section, rather than inserted as an unchecked rank field. -/
theorem dimension_eq : d=finrank (ZMod 2) R.Homology := by
  have hq:=R.faceBoundariesInCycles.finrank_quotient_add_finrank
  have hc:=D.onCycles.finrank_range_add_finrank_ker
  rw [D.onCycles_kernel,LinearMap.range_eq_top.mpr D.onCycles_surjective,
    finrank_top,Module.finrank_pi,Fintype.card_fin] at hc
  change finrank (ZMod 2) R.Homology+finrank (ZMod 2) R.faceBoundariesInCycles=finrank (ZMod 2) R.cycleSpace at hq
  omega

include D in
theorem dimension_of_genus (root : Dart E)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) {h : ℕ} (hh : R.HasGenus h) : d=2*h :=
  D.dimension_eq.trans (R.homology_finrank_of_genus root hG hh)

end QuotientCoordinates
end PlanarHom.PlanarityLRRealization.RotationRows
