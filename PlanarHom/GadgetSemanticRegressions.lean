import PlanarHom.ColoredEdgeGadgetJointReduction
import PlanarHom.ContextualColoredMatrix
import PlanarHom.TypedGadgetAppendRestrictedSemantics
import PlanarHom.PlanarHeterogeneousGadgetInsertion

noncomputable section
open PlanarHom PlanarHom.FixedGadgetNetwork PlanarHom.EdgeSubstitution
namespace GadgetSemanticRegressions

theorem no_private_no_occurrences (M : Fin 0→Matrix (Fin 2) (Fin 2) ℚ)
    (U : Fin 0→Fin 2→ℚ) (i j : Fin 2) :
    templateInteraction ⟨2,0,[],[]⟩ M U i j=1 := by
  simp [templateInteraction,templateSignature,factor,Template.code]

theorem one_isolated_private (M : Fin 0→Matrix (Fin 2) (Fin 2) ℚ)
    (U : Fin 0→Fin 2→ℚ) (i j : Fin 2) :
    templateInteraction ⟨2,1,[],[]⟩ M U i j=2 := by
  simp [templateInteraction,templateSignature,factor,Template.code,Fintype.card_fun]

theorem empty_color_signature (G : TwoTerminal (Fin 1) (Fin 0))
    (M : Fin 0→Matrix (Fin 0) (Fin 0) ℚ) (U : Fin 0→Fin 0→ℚ)
    (τ : Fin 2→Fin 0) : templateSignature (ofColoredTwoTerminal G id) M U τ=0 := by
  exact Fin.elim0 (τ 0)

/-- Different numbers of private vertices are permitted for every occurrence. -/
theorem actual_heterogeneous_planarity {V E : Type} {W F : E→Type}
    [Finite V] [Finite E] [∀ e,Finite (W e)] [∀ e,Finite (F e)]
    {G : MultiGraph V E} (hG : G.Planar) (K : ∀ e,TwoTerminal (W e) (F e))
    (hK : ∀ e,TwoTerminal.PlanarEdgeGadget (K e)) : (G.insertFamily K).Planar :=
  hG.insertFamily K hK

#check PlanarHom.TwoTerminal.map_coloredSignature
#check PlanarHom.TwoTerminal.coloredSignature_reindexInternal
#check PlanarHom.FixedGadgetNetwork.ofTypedColoredTwoTerminal_signature_restricted
#check PlanarHom.AlgebraicProductInterpolation.RealLanguage.coloredGadgetMatrix_algebraic

end GadgetSemanticRegressions
