import PlanarHom.SurfaceMatchingBoundaryParity

/-! NEW actual matching homology classes relative to a genuine reference
matching, and exact reduction of class equality to null-homology of M△N. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

/-- The reference is an actual perfect matching, not a sign certificate. -/
def matchingHomologyClass (M₀ : Finset E) (h₀ : G.PerfectMatching M₀)
    (M : Finset E) (hM : G.PerfectMatching M) : R.Homology :=
  R.homologyClass (R.evenSubgraphCycle (symmDiff M M₀) (hM.symmDiff_even h₀))

theorem matchingDifference_cycle_add {M N M₀ : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (h₀ : G.PerfectMatching M₀) :
    R.evenSubgraphCycle (symmDiff M N) (hM.symmDiff_even hN)=
      R.evenSubgraphCycle (symmDiff M M₀) (hM.symmDiff_even h₀)+
        R.evenSubgraphCycle (symmDiff N M₀) (hN.symmDiff_even h₀) := by
  apply Subtype.ext
  change edgeIndicator (symmDiff M N)=edgeIndicator (symmDiff M M₀)+edgeIndicator (symmDiff N M₀)
  rw [edgeIndicator_symmDiff,edgeIndicator_symmDiff,edgeIndicator_symmDiff,add_add_add_comm,
    ZModModule.add_self,add_zero]

theorem matchingDifference_class_add {M N M₀ : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (h₀ : G.PerfectMatching M₀) :
    R.homologyClass (R.evenSubgraphCycle (symmDiff M N) (hM.symmDiff_even hN))=
      R.matchingHomologyClass M₀ h₀ M hM+R.matchingHomologyClass M₀ h₀ N hN := by
  rw [R.matchingDifference_cycle_add hM hN h₀,map_add]
  rfl

theorem matchingHomologyClass_eq_iff {M N M₀ : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (h₀ : G.PerfectMatching M₀) :
    R.matchingHomologyClass M₀ h₀ M hM=R.matchingHomologyClass M₀ h₀ N hN ↔
      R.homologyClass (R.evenSubgraphCycle (symmDiff M N) (hM.symmDiff_even hN))=0 := by
  rw [R.matchingDifference_class_add hM hN h₀,add_eq_zero_iff_eq_neg,ZModModule.neg_eq_self]

@[simp] theorem matchingHomologyClass_reference (M₀ : Finset E) (h₀ : G.PerfectMatching M₀) :
    R.matchingHomologyClass M₀ h₀ M₀ h₀=0 := by
  have hh:=R.matchingHomologyClass_eq_iff h₀ h₀ h₀
  exact hh.mp rfl

end PlanarHom.PlanarityLRRealization.RotationRows
