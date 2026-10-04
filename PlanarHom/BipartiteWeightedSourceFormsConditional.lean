/- Conditional assembly lemma. All explicit hypotheses remain visible;
the final closed endpoints instantiate the required foundations. -/
import PlanarHom.RectangularMomentConstancyConditional
import PlanarHom.Structures

/-! Literal original weighted rectangular amplitudes give the exact allowed
bipartite block, without identifying the two side charts or their masses. -/
noncomputable section
open Classical
namespace PlanarHom.BipartiteWeightedSourceForms
open Boolean Structures RectangularSourceNormSimulation
open RectangularBackgroundSourceNormSimulation (weights)
open RectangularTwinQuotient RectangularWeightedNormNormalization
open RectangularMomentConstancy Complexity Complexity.MixedCode
variable {p s k l d n : ℕ}

def sumProductEquiv : ((Fin k×Cube d)⊕(Fin l×Cube d)) ≃ (Fin k⊕Fin l)×Cube d where
  toFun := Sum.elim (fun z=>(Sum.inl z.1,z.2)) (fun z=>(Sum.inr z.1,z.2))
  invFun := fun z=>Sum.elim (fun a=>Sum.inl (a,z.2)) (fun b=>Sum.inr (b,z.2)) z.1
  left_inv := by intro z; cases z <;> rfl
  right_inv := by rintro ⟨z,c⟩; cases z <;> rfl

def colorChart (eX : Fin p≃Fin k×Cube d) (eY : Fin s≃Fin l×Cube d) :
    Fin (p+s) ≃ (Fin k⊕Fin l)×Cube d :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr eX eY).trans sumProductEquiv)

theorem allowedWeighted_of_amplitudes (V : Matrix (Fin p) (Fin s) ℝ)
    (μ : Fin p→ℝ) (ν : Fin s→ℝ)
    (a massX : Fin k→ℝ) (b massY : Fin l→ℝ) (ρ : Fin d→ℝ)
    (hk : 0<k) (hl : 0<l) (ha : ∀ i,0<a i) (hb : ∀ j,0<b j)
    (hmX : ∀ i,0<massX i) (hmY : ∀ j,0<massY j) (hρ : ∀ r,0<ρ r ∧ ρ r≠1)
    (eX : Fin p≃Fin k×Cube d) (eY : Fin s≃Fin l×Cube d)
    (hV : ∀ i j,V i j=a (eX i).1*b (eY j).1*tensor ρ (eX i).2 (eY j).2)
    (hμ : ∀ i,μ i=massX (eX i).1) (hν : ∀ j,ν j=massY (eY j).1) :
    AllowedWeightedBlock (block V) (weights μ ν) := by
  refine .bipartite k l d hk hl a massX b massY ρ ha hb hmX hmY hρ (colorChart eX eY) ?_ ?_
  · intro i j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
      refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp [block,colorChart,sumProductEquiv,bipartiteAmplitude,hV,tensor_symm]
  · intro i
    refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;>
      simp [weights,colorChart,sumProductEquiv,hμ,hν]

variable [Nonempty (Fin p)] [Nonempty (Fin s)] {K₀ : IntermediateField ℚ ℝ}

theorem source_allowedWeighted_of_core_of_potts (hPotts : AlgebraicProductInterpolation.RealLanguage.PositivePottsFoundation) (basis : Module.Basis (Fin n) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j,0<(V i j:ℝ))
    (hinjR : Function.Injective (realRectangular V))
    (hinjC : Function.Injective (realRectangular V).transpose)
    (μ : Fin p→K₀) (ν : Fin s→K₀) (hμ : ∀ i,0<(μ i:ℝ)) (hν : ∀ j,0<(ν j:ℝ))
    (eR : Rows (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Cube d)
    (eC : Columns (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ)))≃Cube d)
    (γ : ℝ) (hγ : 0<γ) (ρ : Fin d→ℝ) (hρ : ∀ r,0<ρ r ∧ ρ r≠1)
    (hcore : ∀ r s,core (normalized (realRectangular V) (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) r s=
      γ*tensor ρ (eR r) (eC s))
    (hnot : ¬PromisedSharpPHard
      (evaluationProblem basis (fun _:Fin 1=>block V) (fun u:Fin 0=>u.elim0) (weights μ ν))) :
    AllowedWeightedBlock (block (realRectangular V))
      (weights (fun i=>(μ i:ℝ)) (fun j=>(ν j:ℝ))) := by
  obtain ⟨k,l,a,massX,b,massY,eX,eY,hk,hl,ha,hmX,hb,hmY,hval,hx,hy⟩ :=
    source_weighted_amplitude_tensor_of_potts hPotts basis V hV hinjR hinjC μ ν hμ hν eR eC γ hγ ρ hρ hcore hnot
  exact allowedWeighted_of_amplitudes _ _ _ a massX b massY ρ hk hl ha hb hmX hmY hρ eX eY hval hx hy

end PlanarHom.BipartiteWeightedSourceForms
