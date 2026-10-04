import PlanarHom.TypedContextualGadgetReductionX
import PlanarHom.TypedContextualSpectralClosure
import PlanarHom.ContextualGadgetClosure
import PlanarHom.AlgebraicClosedMatrixFamily

/-! Source-facing gadget and parallel closure of the actual typed X family.
All signatures are obtained by actual APPEND programs in retained mixed contexts;
no operation-closure certificate is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open Complexity FiniteLanguageAliases TypedBipartiteSpectral ClosedMatrixFamily
variable {x y s n : ℕ} {J E : Type} [Fintype J] [Fintype E]

/-- A finite collection of available X matrices can be used independently at
each occurrence of any fixed planar colored gadget. -/
theorem xFamily_colored_gadget (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop)
    (A : Fin n→Matrix (Fin x) (Fin x) ℝ) (hA : ∀l,A l∈xFamily F FB)
    (G : TwoTerminal J E) (label : E→Fin n) (hG : TwoTerminal.PlanarEdgeGadget G)
    (hsym : (TwoTerminal.coloredSignature G (fun k=>A (label k)) (fun _=>1)).IsHermitian) :
    TwoTerminal.coloredSignature G (fun k=>A (label k)) (fun _=>1)∈xFamily F FB := by
  let L₀ := unitLanguage A (fun l=>xFamily_algebraic F FB (A l) (hA l))
  have halg := L₀.coloredGadgetMatrix_algebraic G label
  refine ⟨hsym,typed_contextual_operation (domains x y) F FB
    (fun l=>zeroExtendFin (A l)) (fun _=>sameX) (fun l=>(hA l).2)
    (zeroExtendFin (TwoTerminal.coloredSignature G (fun k=>A (label k)) (fun _=>1)))
    sameX (zeroExtendFin_algebraic _ halg) ?_⟩
  intro bt ut L B T hunit index hindex
  have he : xColoredGadgetMatrix L G (index ∘ label)=
      TwoTerminal.coloredSignature G (fun k=>A (label k)) (fun _=>1) := by
    unfold xColoredGadgetMatrix
    congr 1
    funext k i j
    change L.matrices (index (label k)) (leftEmbedding i) (leftEmbedding j)=_
    rw [(hindex (label k)).1]
    exact zeroExtendFin_left _ i j
  have r := xColoredAppendReduction L B T hunit G (index ∘ label) hG
    (fun k=>(hindex (label k)).2)
  have hp := congrArg (fun V : RealLanguage (x+y) (bt+1) ut=>
    V.typedProblem (domains x y) (appendOne B sameX) T)
    (L.appendBinary_congr _ _
      (zeroExtendFin_algebraic _ (xColoredGadgetMatrix_algebraic L G (index ∘ label)))
      (zeroExtendFin_algebraic _ halg) (congrArg zeroExtendFin he))
  dsimp only at hp
  rw [hp] at r
  exact ⟨r⟩

/-- Arbitrary finite occurrence-indexed edge labels are jointly realized; no
single-generator restriction is imposed on mixed colored gadgets. -/
theorem xFamily_mixedPlanarGadgetClosed (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) : MixedPlanarGadgetClosed (xFamily F FB) where
  signature_mem J E _ _ G hG W hW hsym := by
    let A : Fin (Fintype.card E)→Matrix (Fin x) (Fin x) ℝ :=
      fun k=>W ((Fintype.equivFin E).symm k)
    have hA : ∀k,A k∈xFamily F FB := fun k=>hW _
    have he : (fun k=>A (Fintype.equivFin E k))=W := by
      funext k
      simp only [A,Equiv.symm_apply_apply]
    have r := xFamily_colored_gadget F FB A hA G (Fintype.equivFin E) hG
      (by rw [he]; exact hsym)
    simpa only [he] using r

/-- Parallel multiplication follows from the actual two-edge planar gadget. -/
theorem xFamily_parallel (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) (H K : Matrix (Fin x) (Fin x) ℝ)
    (hH : H∈xFamily F FB) (hK : K∈xFamily F FB) :
    (fun i j=>H i j*K i j)∈xFamily F FB := by
  let A : Fin 2→Matrix (Fin x) (Fin x) ℝ := Fin.cases H (fun _=>K)
  have ha : ∀l,A l∈xFamily F FB := Fin.cases hH (fun _=>hK)
  have hs : (show Matrix (Fin x) (Fin x) ℝ from fun i j=>H i j*K i j).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    have h₁ := congrFun (congrFun hH.1.eq i) j
    have h₂ := congrFun (congrFun hK.1.eq i) j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrArg₂ (· * ·) h₁ h₂
  have r := xFamily_colored_gadget F FB A ha (TwoTerminal.parallelEdges 2) id
    (TwoTerminal.StripDrawing.parallelEdges_planarEdgeGadget 2)
    (by simpa only [Function.comp_def,id_eq,colored_parallel_pair,A] using hs)
  simpa only [Function.comp_def,id_eq,colored_parallel_pair,A] using r

/-- All source algebraic/spectral/parallel requirements are proved for the
literal typed contextual family, alongside its separately proved effective and
arbitrary mixed planar-gadget closure. -/
theorem xFamily_algebraicSourceClosed (F : Fin s→Matrix (Fin (x+y)) (Fin (x+y)) ℝ)
    (FB : Fin s→Fin 2→Fin 2→Prop) : AlgebraicSourceClosed (xFamily F FB) where
  symmetric := xFamily_symmetric F FB
  algebraic := xFamily_algebraic F FB
  spectral H hH hpd _ r := xFamily_rationalPower F FB H hH hpd r
  parallel H hH _ K hK _ := xFamily_parallel F FB H K hH hK

end PlanarHom.TypedBipartiteContext
