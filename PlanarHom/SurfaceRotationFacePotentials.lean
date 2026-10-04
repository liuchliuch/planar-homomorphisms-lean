import PlanarHom.SurfaceRotationHomology

/-! NEW exact null-homology/face-potential equivalence. The potential is derived
from the actual quotient definition and can be normalized at any literal face.
No genus-zero hypothesis is needed for a null-homologous chain. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

def homologyClass : R.cycleSpace→ₗ[ZMod 2] R.Homology := R.faceBoundariesInCycles.mkQ

theorem homologyClass_eq_zero_iff (c : R.cycleSpace) :
    R.homologyClass c=0 ↔ ∃f : R.Face→ZMod 2,
      (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec f=c.val := by
  rw [homologyClass,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨f,hf⟩:=b.property
    exact ⟨f,hf.trans (congrArg Subtype.val hb)⟩
  · rintro ⟨f,hf⟩
    let b : R.faceBoundarySpace:=⟨c.val,⟨f,hf⟩⟩
    exact ⟨b,Subtype.ext rfl⟩

theorem exists_normalized_face_potential_of_null (root : Dart E) (c : R.cycleSpace)
    (hc : R.homologyClass c=0) :
    ∃f : R.Face→ZMod 2,f (R.faceOf root)=0 ∧
      (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec f=c.val := by
  obtain ⟨f,hf⟩:=(R.homologyClass_eq_zero_iff c).mp hc
  refine ⟨fun F=>f F-f (R.faceOf root),sub_self _,?_⟩
  funext e
  rw [R.dualGraph.coboundaryMatrix_apply]
  have hh:=congrFun hf e
  rw [R.dualGraph.coboundaryMatrix_apply] at hh
  exact (by linear_combination hh)

/-- Coordinates exist on the actual quotient of the supplied rotation. This is
an algebraic basis choice, not an encoded basis-construction algorithm. -/
def homologyCoordinates (root : Dart E)
    (hG : ∀u v,G.componentSetoid Finset.univ u v) {h : ℕ} (hh : R.HasGenus h) :
    R.Homology≃ₗ[ZMod 2](Fin (2*h)→ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) R.Homology (R.homology_finrank_of_genus root hG hh)).equivFun

end PlanarHom.PlanarityLRRealization.RotationRows
