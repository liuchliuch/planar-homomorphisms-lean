import PlanarHom.TypedContextualGadgetReduction
import PlanarHom.TypedContextualGadgetSemantics
import PlanarHom.TypedContextualSpectralBlocks
import PlanarHom.ColoredSignatureFieldMap
import PlanarHom.ColoredGadgetReindex

/-! The literal X-restricted colored gadget, realized in the original field.
Private colors stay in X even for isolated vertices and empty edge types. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PrescribedDomains FiniteLanguageAliases TypedGadgetAppend
open TypedBipartiteSpectral
variable {x y bt ut p e : ℕ} {J E : Type} [Fintype J] [Fintype E]

def xColoredGadgetMatrix (L : RealLanguage (x+y) bt ut) (G : TwoTerminal J E)
    (label : E→Fin bt) : Matrix (Fin x) (Fin x) ℝ :=
  TwoTerminal.coloredSignature G (fun k=>xBlock L.matrices (label k)) (fun _=>1)

def xColoredGadgetMatrixK (L : RealLanguage (x+y) bt ut) (G : TwoTerminal J E)
    (label : E→Fin bt) : Matrix (Fin x) (Fin x) L.field :=
  TwoTerminal.coloredSignature G (fun k=>xBlock L.matricesK (label k)) (fun _=>1)

theorem xColoredGadgetMatrixK_coe (L : RealLanguage (x+y) bt ut) (G : TwoTerminal J E)
    (label : E→Fin bt) (i j : Fin x) :
    (xColoredGadgetMatrixK L G label i j:ℝ)=xColoredGadgetMatrix L G label i j := by
  simpa only [xColoredGadgetMatrixK,xColoredGadgetMatrix,xBlock,map_one,matricesK_coe] using
    TwoTerminal.map_coloredSignature L.field.val.toRingHom G
      (fun k=>xBlock L.matricesK (label k)) (fun _=>1) i j

theorem xColoredGadgetMatrix_algebraic (L : RealLanguage (x+y) bt ut) (G : TwoTerminal J E)
    (label : E→Fin bt) (i j : Fin x) : IsAlgebraic ℚ (xColoredGadgetMatrix L G label i j) := by
  rw [←xColoredGadgetMatrixK_coe L G label i j]
  exact (IsAlgebraic.of_finite ℚ (xColoredGadgetMatrixK L G label i j)).algHom L.field.val

/-- The two old terminal tags and all new private tags are exactly X. -/
theorem extend_X_tag (v : Bool⊕Fin p) :
    TwoTerminal.extend (0:Fin 2) 0 (fun _:Fin p=>0) v=0 := by
  cases v with
  | inl b => cases b <;> rfl
  | inr i => rfl

/-- Canonical APPEND for a Fin-serialized colored gadget. Only the selected
edge labels need XX policy; all other B/T/U data remain arbitrary. -/
def xColoredAppendFinReduction (L : RealLanguage (x+y) bt ut)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (hlabel : ∀k,B (label k)=sameX) :
    PromisePolyTimeTuringReduction
      ((L.appendBinary (zeroExtendFin (xColoredGadgetMatrix L G label))
        (zeroExtendFin_algebraic _ (xColoredGadgetMatrix_algebraic L G label))).typedProblem
        (domains x y) (appendOne B sameX) T)
      (L.typedProblem (domains x y) B T) := by
  apply coloredAppendRealizationReduction L (domains x y) B T hunit
    G label (fun _=>0) hG sameX 0
    (fun a b hab k=>by
      obtain ⟨rfl,rfl⟩ := hab
      rw [hlabel k,extend_X_tag,extend_X_tag]
      exact ⟨rfl,rfl⟩)
    _ _ (zeroExtendFin (xColoredGadgetMatrixK L G label))
  · intro i j
    rw [zeroExtendFin_coe]
    congr 2
    funext a b
    exact xColoredGadgetMatrixK_coe L G label a b
  · intro a b hab i hi j hj
    obtain ⟨rfl,rfl⟩ := hab
    obtain ⟨i,rfl⟩ := hi
    obtain ⟨j,rfl⟩ := hj
    change coloredDomainInteraction G label (fun _=>0) L.matricesK (domains x y)
      (leftEmbedding i) (leftEmbedding j)=
      zeroExtendFin (xColoredGadgetMatrixK L G label) (leftEmbedding i) (leftEmbedding j)
    rw [coloredDomainInteraction_X,zeroExtendFin_left]
    rfl

/-- Arbitrary finite private/edge types are serialized by fixed equivalences;
the resulting literal real signature and original source are unchanged. -/
def xColoredAppendReduction (L : RealLanguage (x+y) bt ut)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (G : TwoTerminal J E)
    (label : E→Fin bt) (hG : TwoTerminal.PlanarEdgeGadget G)
    (hlabel : ∀k,B (label k)=sameX) :
    PromisePolyTimeTuringReduction
      ((L.appendBinary (zeroExtendFin (xColoredGadgetMatrix L G label))
        (zeroExtendFin_algebraic _ (xColoredGadgetMatrix_algebraic L G label))).typedProblem
        (domains x y) (appendOne B sameX) T)
      (L.typedProblem (domains x y) B T) := by
  let G' := G.reindexInternal (Fintype.equivFin J) (Fintype.equivFin E)
  let label' := fun k=>label ((Fintype.equivFin E).symm k)
  have hp : TwoTerminal.PlanarEdgeGadget G' := TwoTerminal.reindexInternal_planar G _ _ hG
  have he : xColoredGadgetMatrix L G' label'=xColoredGadgetMatrix L G label :=
    TwoTerminal.coloredSignature_reindexInternal G _ _
      (fun k=>xBlock L.matrices (label k)) (fun _=>1)
  have r := xColoredAppendFinReduction L B T hunit G' label' hp
    (fun k=>hlabel ((Fintype.equivFin E).symm k))
  have hre := congrArg (fun V : RealLanguage (x+y) (bt+1) ut=>
    V.typedProblem (domains x y) (appendOne B sameX) T)
    (L.appendBinary_congr _ _
      (zeroExtendFin_algebraic _ (xColoredGadgetMatrix_algebraic L G' label'))
      (zeroExtendFin_algebraic _ (xColoredGadgetMatrix_algebraic L G label))
      (congrArg zeroExtendFin he))
  dsimp only at hre
  rw [hre] at r
  exact r

end PlanarHom.TypedBipartiteContext
