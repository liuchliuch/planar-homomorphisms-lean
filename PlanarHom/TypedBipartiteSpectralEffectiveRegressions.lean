import PlanarHom.TypedBipartiteSpectralEffectiveAvailability
import PlanarHom.TypedBipartiteSpectralRegressions

/-! Effective-side regressions explicitly reject the dangerous dummy-one
alphabet and exercise unequal sides with cross companions and source fields. -/
noncomputable section
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains PlanarHom.TypedBipartiteSpectral
open PlanarHom.ExponentProductTables PlanarHom.ExponentProductSemantics
open PlanarHom.EffectiveProductTransfer PlanarHom.SpectralFieldPresentation

namespace PlanarHom.TypedBipartiteSpectral.EffectiveRegressions

/-- X's length-two products impose no collision between the mixed coordinates. -/
theorem original_compatible : CompatibleAt ![(2:ℚ),4] ![(3:ℚ),7] 2 := by
  have hw : ExponentVectors.weak 2 2=[[2,0],[1,1],[0,2]] := by decide
  norm_num [CompatibleAt,hw,value,Fin.prod_univ_succ]

/-- Repeating a true coordinate preserves exactly those original collisions. -/
example : CompatibleAt (![(2:ℚ),4] ∘ ![(0:Fin 2),1,0])
    (![(3:ℚ),7] ∘ ![(0:Fin 2),1,0]) 2 :=
  compatibleAt_comp _ _ _ 2 original_compatible

/-- By contrast, adjoining a dummy 1 invents the relation 2·2=4·1.
The target 3·3≠7·1 proves why ambient-completion compatibility is invalid. -/
example : ¬CompatibleAt ![(2:ℚ),4,1] ![(3:ℚ),7,1] 2 := by
  intro h
  have he := h [2,0,0] (by norm_num [ExponentVectors.weak,ExponentVectors.box])
    [0,1,1] (by norm_num [ExponentVectors.weak,ExponentVectors.box])
    (by norm_num [value,Fin.prod_univ_succ]) (by norm_num [value,Fin.prod_univ_succ])
  norm_num [value,Fin.prod_univ_succ] at he

def sides : Fin 2 → Set (Fin (2+3)) :=
  fun d=>if d=0 then Set.range (leftEmbedding (q:=2) (y:=3)) else Set.range (Fin.natAdd 2)

theorem endpoint_typing : ∀ x z,Regressions.permissions 0 x z →
    sides x⊆Set.range (leftEmbedding (q:=2) (y:=3)) ∧
    sides z⊆Set.range (leftEmbedding (q:=2) (y:=3)) := by
  intro x z h
  obtain ⟨rfl,rfl⟩ := (by simpa [Regressions.permissions] using h : x=0 ∧ z=0)
  simp [sides]

variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀] {dimension : ℕ}

/-- Unequal sides, arbitrary original selected completion and arbitrary cross
companion, original basis, algebraic real target, and ordinary-unary offset 1. -/
def realTargetReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin 2 → Matrix (Fin (2+3)) (Fin (2+3)) K₀)
    (U : Fin 1 → Fin (2+3) → K₀) (A : Matrix (Fin 2) (Fin 2) K₀)
    (hblock : ∀ i j,M 0 (leftEmbedding i) (leftEmbedding j)=A i j)
    (N : Matrix (Fin 2) (Fin 2) ℝ) (hN : ∀ i j,IsAlgebraic ℚ (N i j))
    (hpd : (realMatrix A).PosDef) (hNs : N.IsHermitian)
    (n₀ : ℕ) (hn₀ : 1≤n₀)
    (hp : ∀ n,n₀≤n → ∀ i j,0<matrixPowerRealFamily A n i j)
    (hi : ProductIdentities (matrixPowerRealFamily A) N) :=
  typedEffectiveOverfieldReduction b₀ M U sides Regressions.permissions Regressions.unaryPermissions
    0 0 (by simp [sides]) Regressions.actual_path_typing endpoint_typing
    A hblock N hN 0 hpd hNs n₀ hn₀ hp hi

end PlanarHom.TypedBipartiteSpectral.EffectiveRegressions
