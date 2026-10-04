-- NEW conditional assembly; independent foundations remain explicit.
import PlanarHom.RectangularCoreSourceEntranceConditional
import PlanarHom.RectangularTypedSourceRigidityConditional
noncomputable section
open Classical
namespace PlanarHom.RectangularCoreSourceRigidity
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext RectangularCoreSourceEntrance Complexity
open RectangularSourceNormSimulation (block)
variable {x y : ℕ} [Nonempty (Fin x)] [Nonempty (Fin y)]
theorem rectangular_tensor_of_source_of_potts
    (hPotts : PositivePottsFoundation)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hM : L.matrices 0=block B)
    (hrows : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j)
    (hcolumns : ∀ i j,i≠j → ∀ t : ℝ,B.transpose i≠t•B.transpose j)
    (hnot : ¬PromisedSharpPHard L.problem) :
    ∃ d : ℕ,∃ eX : Fin x≃Boolean.Cube d,∃ eY : Fin y≃Boolean.Cube d,
      ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
      ∀ i j,B i j=γ*Boolean.tensor ρ (eX i) (eY j) :=
  rectangular_tensor_of_homogeneous_source_of_potts hPotts (fun _:Fin 1=>crossFin B) (fun _=>crossPolicy)
    (source_algebraic L B hM) 0 L hunit (source_contains L B hM) (source_crosses L B hM)
    B hB hrows hcolumns rfl rfl hnot
theorem non_tensor_source_hard_of_potts
    (hPotts : PositivePottsFoundation)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hM : L.matrices 0=block B)
    (hrows : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j)
    (hcolumns : ∀ i j,i≠j → ∀ t : ℝ,B.transpose i≠t•B.transpose j)
    (hbad : ¬∃ d : ℕ,∃ eX : Fin x≃Boolean.Cube d,∃ eY : Fin y≃Boolean.Cube d,
      ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
      ∀ i j,B i j=γ*Boolean.tensor ρ (eX i) (eY j)) :
    PromisedSharpPHard L.problem := by
  by_contra hn
  exact hbad (rectangular_tensor_of_source_of_potts hPotts L hunit B hB hM hrows hcolumns hn)
theorem proposition92_of_potts
    (hPotts : PositivePottsFoundation)
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hM : L.matrices 0=block B)
    (hrows : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j)
    (hcolumns : ∀ i j,i≠j → ∀ t : ℝ,B.transpose i≠t•B.transpose j) :
    PromisedSharpPHard L.problem ∨
      ∃ d : ℕ, x=2^d ∧ y=2^d ∧ ∃ eX : Fin x≃Boolean.Cube d,∃ eY : Fin y≃Boolean.Cube d,
        ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i<1) ∧
        ∀ i j,B i j=γ*Boolean.tensor ρ (eX i) (eY j) := by
  by_cases hn : PromisedSharpPHard L.problem
  · exact Or.inl hn
  · obtain ⟨d,eX,eY,γ,ρ,hγ,hρ,he⟩ := rectangular_tensor_of_source_of_potts hPotts L hunit B hB hM hrows hcolumns hn
    refine Or.inr ⟨d,?_,?_,eX,eY,γ,ρ,hγ,hρ,he⟩
    · simpa [Boolean.Cube,Fintype.card_fun] using Fintype.card_congr eX
    · simpa [Boolean.Cube,Fintype.card_fun] using Fintype.card_congr eY
end PlanarHom.RectangularCoreSourceRigidity
