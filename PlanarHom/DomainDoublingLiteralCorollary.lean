import PlanarHom.DomainDoublingClassificationConditional
import PlanarHom.PottsComponentCode

/-! NEW literal rectangular and component-count forms of Corollary 12.2. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.DomainDoublingClassification
open Complexity Complexity.MixedCode AlgebraicProductInterpolation
open AlgebraicProductInterpolation.RealLanguage Structures
open ComputedDomainDoubling BipartiteRankTwoTractability

 theorem equation121 {C K : Type} [Fintype C] [Field K]
    (g : MixedCode) (hg : g.Valid 1 0) (hb : HasProperSides g hg)
    (M : Matrix C C K) (w : C→K) :
    g.evaluate hg (fun _ : Fin 1=>ComputedDomainDoubling.matrix M) (fun u : Fin 0=>u.elim0)
      (ComputedDomainDoubling.weights w)=
      2^((g.toMultiGraph hg).componentCount Finset.univ)*
        g.evaluate hg (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w := by
  rw [GraphComponentCode.componentCount_eq_components_length]
  exact components_value g hg ((coloring_iff_proper g hg).mpr hb) M w

variable {x y : ℕ}

def rectangularIndex (x y : ℕ) : Fin (x+y)≃Fin x⊕Fin y := finSumFinEquiv.symm

def rectangularMatrix (V : Matrix (Fin x) (Fin y) ℝ) : Matrix (Fin (x+y)) (Fin (x+y)) ℝ :=
  fun i j=>Matrix.fromBlocks 0 V V.transpose 0 (rectangularIndex x y i) (rectangularIndex x y j)

def rectangularSide (i : Fin (x+y)) : Bool :=
  Sum.elim (fun _=>false) (fun _=>true) (rectangularIndex x y i)

def rectangularLanguage (V : Matrix (Fin x) (Fin y) ℝ) (μ : Fin x→ℝ) (ν : Fin y→ℝ)
    (hV : ∀i j,IsAlgebraic ℚ (V i j)) (hμ : ∀i,IsAlgebraic ℚ (μ i)) (hν : ∀i,IsAlgebraic ℚ (ν i)) :
    RealLanguage (x+y) 1 0 where
  matrices _:=rectangularMatrix V
  unaries u:=u.elim0
  weights i:=Sum.elim μ ν (rectangularIndex x y i)
  matrices_algebraic _ i j:=by
    unfold rectangularMatrix
    cases rectangularIndex x y i <;> cases rectangularIndex x y j <;>
      first | exact isAlgebraic_zero | exact hV _ _
  unaries_algebraic u:=u.elim0
  weights_algebraic i:=by
    cases rectangularIndex x y i <;> first | exact hμ _ | exact hν _

theorem rectangular_crosses (V : Matrix (Fin x) (Fin y) ℝ) :
    ∀i j,rectangularMatrix V i j≠0 → rectangularSide i≠rectangularSide j := by
  intro i j hn
  cases hi : rectangularIndex x y i <;> cases hj : rectangularIndex x y j <;>
    simp_all [rectangularMatrix,rectangularSide]

theorem rectangular_symm (V : Matrix (Fin x) (Fin y) ℝ) :
    ∀i j,rectangularMatrix V i j=rectangularMatrix V j i := by
  intro i j
  cases hi : rectangularIndex x y i <;> cases hj : rectangularIndex x y j <;>
    simp [rectangularMatrix,hi,hj,Matrix.transpose_apply]

theorem rectangular_nonneg (V : Matrix (Fin x) (Fin y) ℝ) (hV : ∀i j,0≤V i j) :
    ∀i j,0≤rectangularMatrix V i j := by
  intro i j
  cases hi : rectangularIndex x y i <;> cases hj : rectangularIndex x y j <;>
    simp only [rectangularMatrix,hi,hj,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,Matrix.transpose_apply] <;>
      first | exact le_rfl | exact hV _ _

theorem corollary122_rectangular_of_potts (hPotts : PositivePottsFoundation)
    (V : Matrix (Fin x) (Fin y) ℝ) (μ : Fin x→ℝ) (ν : Fin y→ℝ)
    (hV : ∀i j,IsAlgebraic ℚ (V i j)) (hμ : ∀i,IsAlgebraic ℚ (μ i)) (hν : ∀i,IsAlgebraic ℚ (ν i))
    (hnn : ∀i j,0≤V i j) (hμpos : ∀i,0<μ i) (hνpos : ∀i,0<ν i) :
    let L:=rectangularLanguage V μ ν hV hμ hν
    (PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      (prescribedProblem L rectangularSide).InFP) ∧
    (¬PositiveVertexWeightClass (rectangularMatrix V) L.weights (rectangular_symm V) →
      PromisedSharpPHard (prescribedProblem L rectangularSide)) := by
  dsimp only
  apply corollary122_prescribed_of_potts hPotts (rectangularLanguage V μ ν hV hμ hν)
    rectangularSide (rectangular_crosses V) (rectangular_symm V) (rectangular_nonneg V hnn)
  intro i
  change 0<Sum.elim μ ν (rectangularIndex x y i)
  cases rectangularIndex x y i <;> first | exact hμpos _ | exact hνpos _

end PlanarHom.DomainDoublingClassification
