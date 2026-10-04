import PlanarHom.FiniteGraphCycleDuality

/-! NEW ordinary incidence rank for arbitrary finite multigraphs, including
isolates and the empty graph. The kernel is the actual component-constant space. -/
noncomputable section
open Classical
open Matrix Module
namespace PlanarHom.MultiGraph
variable {V E K : Type*} [Fintype V] [Fintype E] [Field K]

 def componentPullback (G : MultiGraph V E) : (G.Components Finset.univ→K)→ₗ[K](V→K) where
  toFun f v:=f (Quotient.mk _ v)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

 theorem componentPullback_injective (G : MultiGraph V E) : Function.Injective (G.componentPullback (K:=K)) := by
  intro f h he
  funext c
  induction c using Quotient.inductionOn with | h v=>exact congrFun he v

 theorem coboundary_ker_eq_componentRange (G : MultiGraph V E) :
    LinearMap.ker (G.coboundaryMatrix K).mulVecLin=LinearMap.range (G.componentPullback (K:=K)) := by
  ext f
  constructor
  · intro hf
    have hconst:G.EdgeConstant Finset.univ f := by
      intro e he
      have h:=congrFun (show (G.coboundaryMatrix K).mulVec f=0 from hf) e
      rw [G.coboundaryMatrix_apply] at h
      exact sub_eq_zero.mp h
    refine ⟨Quotient.lift f (fun u v huv=>G.edgeConstant_respects Finset.univ f hconst huv),rfl⟩
  · rintro ⟨f,rfl⟩
    change (G.coboundaryMatrix K).mulVec (fun v=>f (Quotient.mk _ v))=0
    funext e
    rw [G.coboundaryMatrix_apply]
    have he:(Quotient.mk _ (G.src e):G.Components Finset.univ)=Quotient.mk _ (G.dst e):=
      Quotient.sound (Relation.EqvGen.rel _ _ ⟨e,Finset.mem_univ _,rfl,rfl⟩)
    simp [he]

 theorem coboundary_rank_add_components (G : MultiGraph V E) :
    (G.coboundaryMatrix K).rank+G.componentCount Finset.univ=Fintype.card V := by
  have hr:finrank K (LinearMap.range (G.componentPullback (K:=K)))=G.componentCount Finset.univ := by
    rw [LinearMap.finrank_range_of_inj (G.componentPullback_injective),Module.finrank_pi]
    rfl
  have hn:=(G.coboundaryMatrix K).mulVecLin.finrank_range_add_finrank_ker
  rw [G.coboundary_ker_eq_componentRange,hr,Module.finrank_pi] at hn
  exact hn

end PlanarHom.MultiGraph
