import PlanarHom.SurfaceFisherPolygonKernel
import PlanarHom.SurfaceChainBoundary

/-! NEW actual external-edge projection of closed Fisher polygon chains. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

theorem polygon_external_boundary_zero (c : (polygonRows R).cycleSpace) :
    (G.coboundaryMatrix (ZMod 2)).transpose.mulVec (fun e=>c.val (.inl e))=0 := by
  funext v
  rw [chainBoundary_eq_dartSum]
  have hr (a : Dart E) : (G.dartPair (R.rotation.symm a)).1=(G.dartPair a).1 := by
    have hh:=R.rotation_host (R.rotation.symm a)
    rw [R.rotation.apply_symm_apply] at hh
    exact hh.symm
  have hs : (∑a : Dart E,if (G.dartPair a).1=v then c.val (.inr (R.rotation.symm a)) else 0)=
      ∑a : Dart E,if (G.dartPair a).1=v then c.val (.inr a) else 0 := by
    have hh:=Equiv.sum_comp R.rotation.symm
      (fun a : Dart E=>if (G.dartPair a).1=v then c.val (.inr a) else 0)
    simpa only [hr] using hh
  have ht : (∑a : Dart E,if (G.dartPair a).1=v then c.val (.inl a.1) else 0)+
      (∑a : Dart E,if (G.dartPair a).1=v then c.val (.inr a) else 0)+
      (∑a : Dart E,if (G.dartPair a).1=v then c.val (.inr (R.rotation.symm a)) else 0)=0 := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha:(G.dartPair a).1=v
    · simp only [ha,if_true]
      exact polygon_cycle_equation R c a
    · simp [ha]
  rw [hs,add_assoc,ZModModule.add_self,add_zero] at ht
  exact ht

def polygonExternalCycle (c : (polygonRows R).cycleSpace) : R.cycleSpace :=
  ⟨fun e=>c.val (.inl e),polygon_external_boundary_zero R c⟩

end PlanarHom.Fisher
