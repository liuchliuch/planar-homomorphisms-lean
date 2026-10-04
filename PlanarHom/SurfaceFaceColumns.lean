import PlanarHom.SurfaceRotationHomology

/-! NEW literal generating columns of the actual F2 face-boundary subspace. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PlanarityLRRealization.RotationRows
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} (R : RotationRows G)

def faceColumn (q : R.Face) : E→ZMod 2 :=
  (R.dualGraph.coboundaryMatrix (ZMod 2)).mulVec (Pi.single q 1)

theorem faceColumn_apply (q : R.Face) (e : E) : R.faceColumn q e=
    (if R.faceOf (e,true)=q then 1 else 0)+(if R.faceOf (e,false)=q then 1 else 0) := by
  rw [faceColumn,R.dualGraph.coboundaryMatrix_apply]
  simp only [dualGraph,Pi.single_apply,sub_eq_add_neg,ZMod.neg_eq_self_mod_two,eq_comm]

theorem faceBoundarySpace_eq_span_columns :
    R.faceBoundarySpace=Submodule.span (ZMod 2) (Set.range R.faceColumn) := by
  apply le_antisymm
  · rintro z ⟨f,rfl⟩
    have hf : f=∑q : R.Face,(f q) • Pi.single q (1:ZMod 2) := by
      funext q
      simp [Pi.single_apply]
    rw [hf,map_sum]
    apply Submodule.sum_mem
    intro q _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨q,rfl⟩
    exact ⟨Pi.single q 1,rfl⟩

end PlanarHom.PlanarityLRRealization.RotationRows
