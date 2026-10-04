import PlanarHom.BodyUnconditionalClassification

/-! NEW full common-coordinate consequence, including disconnected PD members
and strictly positive singular or indefinite members in the same one chart. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.ClosedMatrixFamily
open Complexity AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
variable {q : ℕ}

theorem corollary62 (S : Set (Matrix (Fin q) (Fin q) ℝ)) (hA : AlgebraicSourceClosed S)
    (htransfer : EffectiveSpectralClosed S) (hgadget : MixedPlanarGadgetClosed S) (P : PromiseProblem)
    (havail : ∀N,∀hN:N∈S,Nonempty (PromisePolyTimeTuringReduction
      (unitLanguage (fun _ : Fin 1=>N) (fun _=>hA.algebraic N hN)).problem P))
    (hne : ∃H,Admissible S H) (hnot : ¬PromisedSharpPHard P) :
    ∃W : CommonCubeChart S,q=2^W.dimension ∧
      (∀N : Matrix (Fin q) (Fin q) ℝ,N∈S → N.PosDef → (∀i j,0≤N i j) →
        ∃γ : ℝ,∃A : Fin W.dimension→Matrix Bool Bool ℝ,0<γ ∧
          (∀r,(A r).PosDef ∧ ∀i j,0≤A r i j) ∧
          Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • CubeTensorExponential.tensor A) ∧
      (∀N : Matrix (Fin q) (Fin q) ℝ,Admissible S N →
        ∃γ : ℝ,∃ρ : Fin W.dimension→ℝ,0<γ ∧ (∀r,0<ρ r ∧ ρ r<1) ∧
          Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • Boolean.tensor ρ) ∧
      (∀N : Matrix (Fin q) (Fin q) ℝ,N∈S → (∀i j,0<N i j) →
        ∃γ : ℝ,∃ρ : Fin W.dimension→ℝ,0<γ ∧ (∀r,0<ρ r) ∧
          Matrix.reindex W.graphIso.toEquiv W.graphIso.toEquiv N=γ • Boolean.tensor ρ) := by
  obtain ⟨W⟩:=exists_common_cube_chart positivePottsFoundation S hA htransfer hgadget P havail hne hnot
  refine ⟨W,W.cardinality,?_,?_,?_⟩
  · intro N hN hpd hnn
    obtain ⟨γ,A,hγ,_,hA',he⟩:=W.nonnegative_factors hA htransfer hgadget N hN hpd hnn
    exact ⟨γ,A,hγ,fun r=>⟨(hA' r).1,(hA' r).2.1⟩,he⟩
  · intro N hN
    obtain ⟨γ,ρ,hγ,_,hr,he⟩:=W.connected_tensor hA htransfer hgadget P havail hnot N hN
    exact ⟨γ,ρ,hγ,fun r=>⟨(hr r).1,(hr r).2.1⟩,he⟩
  · intro N hN hp
    exact W.positive_tensor hA htransfer hgadget P havail hnot N hN hp

end PlanarHom.ClosedMatrixFamily
