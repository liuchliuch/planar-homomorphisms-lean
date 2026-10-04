import PlanarHom.TypedContextualGadgetReduction
import PlanarHom.TypedContextualGadgetFieldMap
import PlanarHom.ContextualGadgetClosure

/-! Genuine mixed typed gadget closure in arbitrary retained contexts. The
private tags and every source endpoint policy remain literal compiler inputs. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open TypedGadgetAppend TypedBipartiteContext
variable {q dt s n p e : ℕ}

/-- A physical colored gadget built from jointly available typed matrices is
available in the same retained-context family, with its actual private domains. -/
theorem typed_contextual_colored_gadget (D : Fin dt→Set (Fin q))
    (F : Fin s→Matrix (Fin q) (Fin q) ℝ) (FB : Fin s→Fin dt→Fin dt→Prop)
    (A : Fin n→Matrix (Fin q) (Fin q) ℝ) (AB : Fin n→Fin dt→Fin dt→Prop)
    (hA : ∀l,TypedContextuallyAvailable D F FB (A l) (AB l))
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin n)
    (tag : Fin p→Fin dt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (NB : Fin dt→Fin dt→Prop) (fallback : Fin dt)
    (hedges : ∀a b,NB a b→∀k,AB (label k)
      (TwoTerminal.extend a b tag (G.src k))
      (TwoTerminal.extend a b tag (G.dst k))) :
    TypedContextuallyAvailable D F FB (coloredDomainInteraction G label tag A D) NB := by
  let L₀ := unitLanguage A (fun l=>(hA l).algebraic)
  have halg := L₀.typedColoredGadgetMatrix_algebraic G label tag D
  refine typed_contextual_operation D F FB A AB hA _ NB halg ?_
  intro bt ut L B T hunit index hi
  have he : L.typedColoredGadgetMatrix G (index ∘ label) tag D =
      coloredDomainInteraction G label tag A D := by
    unfold typedColoredGadgetMatrix coloredDomainInteraction
    funext i j
    apply Finset.sum_congr rfl
    intro η _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    change L.matrices (index (label k)) _ _ = _
    rw [(hi (label k)).1]
  refine ⟨coloredAppendRealizationReduction L D B T hunit G (index ∘ label) tag hG
    NB fallback ?_ _ halg (L.typedColoredGadgetMatrixK G (index ∘ label) tag D) ?_ ?_⟩
  · intro a b hab k
    change B (index (label k)) _ _
    rw [(hi (label k)).2]
    exact hedges a b hab k
  · intro i j
    rw [L.typedColoredGadgetMatrixK_coe,he]
    rfl
  · intros
    rfl

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
