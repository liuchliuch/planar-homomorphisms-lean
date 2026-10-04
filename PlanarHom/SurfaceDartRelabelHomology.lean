import PlanarHom.SurfaceChainBoundary
import PlanarHom.SurfaceRotationFacePotentials

/-! NEW exact null-homology transport under actual vertex/dart relabelings,
including independent orientation reversal of every occurrence. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

theorem dualBoundary_dart (f : R.Face→ZMod 2) (a : Dart E) :
    (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec f a.1=
      f (R.faceOf a)-f (R.faceOf (reversePerm E a)) := by
  rw [R.dualGraph.coboundaryMatrix_apply]
  rcases a with ⟨a,b⟩
  cases b <;> simp [dualGraph,reversePerm,sub_eq_add_neg,ZMod.neg_eq_self_mod_two,add_comm]

end PlanarHom.PlanarityLRRealization.RotationRows
namespace PlanarHom.MultiGraph.DartRelabel
open Kasteleyn PlanarityLRRealization
variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
variable [DecidableEq (Dart E)] [DecidableEq (Dart F)]
variable {G : MultiGraph V E} {H : MultiGraph W F} (e : DartRelabel G H) (R : RotationRows G)

def faceEquiv : R.Face≃(e.rows R).Face := Quotient.congr e.dart
  (FinitePermutationCycles.sameCycle_iff_of_step R.facePerm (e.rows R).facePerm e.dart
    (fun a=>(e.rows_face R a).symm))

@[simp] theorem faceEquiv_faceOf (a : Dart E) :
    e.faceEquiv R (R.faceOf a)=(e.rows R).faceOf (e.dart a) := rfl

theorem pullEdgeVector_injective : Function.Injective e.pullEdgeVector := by
  intro x y h
  funext f
  obtain ⟨a,ha⟩:=e.dart.surjective (f,true)
  have hh:=congrFun h a.1
  rw [e.pullEdgeVector_dart,e.pullEdgeVector_dart,ha] at hh
  exact hh

theorem faceBoundary_pull (f : (e.rows R).Face→ZMod 2) :
    (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec (fun q=>f (e.faceEquiv R q))=
      e.pullEdgeVector (((e.rows R).dualGraph.coboundaryMatrix (ZMod 2)).mulVec f) := by
  funext a
  rw [R.dualGraph.coboundaryMatrix_apply]
  change f (e.faceEquiv R (R.faceOf (a,true)))-f (e.faceEquiv R (R.faceOf (a,false)))=
    (((e.rows R).dualGraph.coboundaryMatrix (ZMod 2)).mulVec f) (e.dart (a,true)).1
  rw [faceEquiv_faceOf,faceEquiv_faceOf,(e.rows R).dualBoundary_dart f (e.dart (a,true))]
  have hr:=e.reverse (a,true)
  change e.dart (a,false)=reversePerm F (e.dart (a,true)) at hr
  rw [hr]

/-- Actual face-boundary membership is preserved in both directions. -/
theorem pullCycle_homology_zero_iff (c : (e.rows R).cycleSpace) :
    R.homologyClass (e.pullCycle R c)=0 ↔ (e.rows R).homologyClass c=0 := by
  rw [R.homologyClass_eq_zero_iff,(e.rows R).homologyClass_eq_zero_iff]
  constructor
  · rintro ⟨f,hf⟩
    let q : (e.rows R).Face→ZMod 2:=fun q=>f ((e.faceEquiv R).symm q)
    refine ⟨q,?_⟩
    apply e.pullEdgeVector_injective
    rw [←e.faceBoundary_pull R q]
    have he : (fun a=>q (e.faceEquiv R a))=f := by
      funext a
      exact congrArg f ((e.faceEquiv R).symm_apply_apply a)
    rw [he]
    exact hf
  · rintro ⟨f,hf⟩
    refine ⟨fun q=>f (e.faceEquiv R q),?_⟩
    rw [e.faceBoundary_pull R f,hf]
    rfl

end PlanarHom.MultiGraph.DartRelabel
