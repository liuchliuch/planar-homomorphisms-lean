import PlanarHom.PositivePottsInterface
import PlanarHom.CommonCubeChartDefinition

/-! NEW genuine conditional common-cube classification. The independent
all-size Potts foundation remains explicit; the clique-isolation source program
and all numerical/structural consequences are proved. -/
noncomputable section
open Classical
namespace PlanarHom.ClosedMatrixFamily
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open LogarithmicSupport Boolean CartesianGeometry
variable {q : ℕ}

theorem available_maximum_is_cube (hPotts : PositivePottsFoundation)
    (S : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed S)
    (htransfer : EffectiveSpectralClosed S) (hgadget : MixedPlanarGadgetClosed S)
    (P : PromiseProblem)
    (havail : ∀ N,∀ hN : N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hne : ∃ H,Admissible S H) (hnot : ¬PromisedSharpPHard P) :
    ∃ d : ℕ,∃ M : Matrix (Fin q) (Fin q) ℝ,Admissible S M ∧ IsMaximum S M ∧
      (∀ i j,(logSupport M).Adj i j→0<EntropyCompletion.matrixLog M i j) ∧
      Nonempty (logSupport M ≃g cubeGraph d) := by
  obtain ⟨M,hM,hmax,hconn,hpos⟩:=lemma41 S hA hne
  obtain ⟨d,sizes,hsizes,⟨e⟩⟩:=lemma47 S hA htransfer hgadget.toPlanarGadgetClosed M hM hmax
  have hbinary : ∀r,sizes r=2 := by
    intro r
    by_contra hneq
    have hlarge : 3≤sizes r := by have := hsizes r;omega
    let L:=unitLanguage (fun _:Fin 1=>M) (fun _=>hA.algebraic M hM.mem)
    have hsource:=HammingPottsToSource.reduction L.basis L.matricesK L.unariesK 0
      hM.posDef hconn hpos sizes hsizes e (sizes r) (hsizes r) ⟨r,rfl⟩
    have hsource' : PromisePolyTimeTuringReduction
        (FullLogarithmicPottsReduction.pottsProblem L.basis (sizes r)) L.problem := by
      simpa only [RealLanguage.problem,weightsK_eq_one L (fun _=>rfl)] using hsource
    obtain ⟨ha⟩:=havail M hM.mem
    exact hnot (((positivePottsField_hard hPotts L.basis (sizes r) hlarge).trans hsource').trans ha)
  let ebool : ∀r,Fin (sizes r) ≃ Bool:=fun r=>(finCongr (hbinary r)).trans finTwoEquiv
  exact ⟨d,M,hM,hmax,hpos,⟨e.trans (hammingGraph_congr ebool)⟩⟩

/-- The exact surviving conditional chart constructor, with all fields retained. -/
theorem exists_common_cube_chart (hPotts : PositivePottsFoundation)
    (S : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed S)
    (htransfer : EffectiveSpectralClosed S) (hgadget : MixedPlanarGadgetClosed S)
    (P : PromiseProblem)
    (havail : ∀ N,∀ hN : N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _:Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hne : ∃ H,Admissible S H) (hnot : ¬PromisedSharpPHard P) :
    Nonempty (CommonCubeChart S) := by
  obtain ⟨d,M,hM,hmax,hpos,⟨e⟩⟩ := available_maximum_is_cube hPotts S hA htransfer hgadget P havail hne hnot
  exact ⟨⟨d,M,hM,hmax,hpos,e⟩⟩

end PlanarHom.ClosedMatrixFamily
