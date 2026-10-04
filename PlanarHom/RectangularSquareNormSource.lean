import PlanarHom.FixedSquareNormPowers
import PlanarHom.RectangularBipartiteBlock
import PlanarHom.RectangularWeightedNormNormalization
import PlanarHom.FiniteFieldQuotientLanguage

/-!
# Rectangular weighted norm source prerequisites — NEW reconstruction

The definitions match the literal formulas consumed by the surviving
RectangularSideMomentPresentation. This module stops before the missing
normalized-edge source program and does not assert its availability.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.RectangularSourceNormSimulation
variable {p s : ℕ} {K₀ : IntermediateField ℚ ℝ}

def realRectangular (V : Matrix (Fin p) (Fin s) K₀) : Matrix (Fin p) (Fin s) ℝ :=
  fun i j => (V i j : ℝ)

end PlanarHom.RectangularSourceNormSimulation

namespace PlanarHom.RectangularBackgroundSourceNormSimulation
open RectangularSourceNormSimulation RectangularWeightedNormNormalization
open Complexity Complexity.MixedCode FiniteLanguageAliases FixedSquareNormSource

variable {p s d : ℕ} {K₀ F : IntermediateField ℚ ℝ}

def weights {R : Type} (μ : Fin p → R) (ν : Fin s → R) : Fin (p+s) → R :=
  Fin.addCases μ ν

/-- Both weighted norms use the original rectangular matrix. -/
def norm (V : Matrix (Fin p) (Fin s) ℝ) (μ : Fin p → ℝ) (ν : Fin s → ℝ) :
    Fin (p+s) → ℝ := Fin.addCases (rowNorm V ν) (columnNorm V μ)

@[simp] theorem squareNorm_left {R : Type} [CommSemiring R]
    (V : Matrix (Fin p) (Fin s) R) (μ : Fin p → R) (ν : Fin s → R) (i : Fin p) :
    squareNorm (block V) (weights μ ν) (Fin.castAdd s i) = ∑ j, ν j * (V i j)^2 := by
  unfold squareNorm
  rw [Fin.sum_univ_add]
  simp [weights]

@[simp] theorem squareNorm_right {R : Type} [CommSemiring R]
    (V : Matrix (Fin p) (Fin s) R) (μ : Fin p → R) (ν : Fin s → R) (j : Fin s) :
    squareNorm (block V) (weights μ ν) (Fin.natAdd p j) = ∑ i, μ i * (V i j)^2 := by
  unfold squareNorm
  rw [Fin.sum_univ_add]
  simp [weights]

theorem squareNorm_real {q : ℕ} (B : Matrix (Fin q) (Fin q) K₀)
    (w : Fin q → K₀) (i : Fin q) :
    ((squareNorm B w i : K₀) : ℝ) = squareNorm (fun i j => (B i j : ℝ)) (fun i => (w i : ℝ)) i := by
  change K₀.val (∑ j, w j * (B i j)^2) = _
  simp only [map_sum, map_mul, map_pow, squareNorm]
  rfl

/-- The field conditional unary is literally a² on X and b² on Y. -/
theorem squareNorm_eq_norm_sq
    (V : Matrix (Fin p) (Fin s) K₀) (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 ≤ (μ i : ℝ)) (hν : ∀ j, 0 ≤ (ν j : ℝ)) (i : Fin (p+s)) :
    ((squareNorm (block V) (weights μ ν) i : K₀) : ℝ) =
      (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)^2 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [squareNorm_left]
    simp only [norm, Fin.addCases_left]
    change K₀.val (∑ j, ν j * (V i j)^2) = (rowNorm (realRectangular V) (fun j => (ν j : ℝ)) i)^2
    rw [rowNorm, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => mul_nonneg (hν j) (sq_nonneg _)))]
    simp only [map_sum, map_mul, map_pow, realRectangular]
    rfl
  · rw [squareNorm_right]
    simp only [norm, Fin.addCases_right]
    change K₀.val (∑ i, μ i * (V i j)^2) = (columnNorm (realRectangular V) (fun i => (μ i : ℝ)) j)^2
    rw [columnNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (sq_nonneg _)))]
    simp only [map_sum, map_mul, map_pow, realRectangular]
    rfl

/-- Fixed integer moments retain each original background factor. -/
theorem moment_real (h₀ : K₀ ≤ F)
    (V : Matrix (Fin p) (Fin s) K₀) (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 ≤ (μ i : ℝ)) (hν : ∀ j, 0 ≤ (ν j : ℝ)) (m : ℕ) (i : Fin (p+s)) :
    ((IntermediateField.inclusion h₀ (weights μ ν i) *
      (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^m : F) : ℝ) =
      ((weights μ ν i : K₀) : ℝ) *
        (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)^(2*m) := by
  change ((weights μ ν i : K₀) : ℝ) * ((squareNorm (block V) (weights μ ν) i : K₀) : ℝ)^m = _
  rw [squareNorm_eq_norm_sq V μ ν hμ hν i, pow_mul]

/-- Exact real/field quotient moment identity used by the surviving consumer.
No source reduction follows from this mathematical transport alone. -/
theorem quotient_moment_real (h₀ : K₀ ≤ F)
    (V : Matrix (Fin p) (Fin s) K₀) (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 ≤ (μ i : ℝ)) (hν : ∀ j, 0 ≤ (ν j : ℝ))
    (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
    (hc : ∀ i j, (C i j : ℝ) = block
      (normalized (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) i j)
    (m : ℕ) (z : Quotient (Twins.rowSetoid C)) :
    ((Twins.quotientWeight C (fun i => IntermediateField.inclusion h₀ (weights μ ν i) *
      (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^m) z : F) : ℝ) =
      Twins.quotientWeight
        (block (normalized (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))))
        (fun i => ((weights μ ν i : K₀) : ℝ) *
          (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)^(2*m))
        (FiniteFieldQuotientLanguage.realQuotientEquiv C _ hc z) := by
  rw [FiniteFieldQuotientLanguage.quotientWeight_real C _ hc]
  congr 1
  funext i
  exact moment_real h₀ V μ ν hμ hν m i

/-- A complete original-source program for the unnormalized rectangular
matrix with its m-th norm-moment background. The matrix is still block V. -/
def rectangularMomentReduction (basis : Module.Basis (Fin d) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (μ : Fin p → K₀) (ν : Fin s → K₀) (m : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0)
        (fun i => weights μ ν i * (squareNorm (block V) (weights μ ν) i)^m))
      (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν)) :=
  squareNormMomentReduction basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0)
    (weights μ ν) 0 (block_symm V) m

variable [Nonempty (Fin p)] [Nonempty (Fin s)]

theorem squareNorm_pos
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j, 0 < (V i j : ℝ))
    (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 < (μ i : ℝ)) (hν : ∀ j, 0 < (ν j : ℝ)) (i : Fin (p+s)) :
    0 < ((squareNorm (block V) (weights μ ν) i : K₀) : ℝ) := by
  rw [squareNorm_eq_norm_sq V μ ν (fun i => (hμ i).le) (fun j => (hν j).le)]
  apply sq_pos_of_pos
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa only [norm, Fin.addCases_left] using rowNorm_pos _ hV _ hν i
  · simpa only [norm, Fin.addCases_right] using columnNorm_pos _ hV _ hμ j

/-- The fixed algebraic field and the inverse square-root unary required at
normalized edge endpoints are genuinely constructed from the rectangular
source, keeping its original oracle field/basis on the right. -/
theorem exists_rectangular_inverse_norm_unary (basis : Module.Basis (Fin d) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j, 0 < (V i j : ℝ))
    (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 < (μ i : ℝ)) (hν : ∀ j, 0 < (ν j : ℝ)) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (v : Fin (p+s) → F),
      (∀ i, (v i : ℝ) =
        (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)⁻¹) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun _ : Fin 1 => fun i j => IntermediateField.inclusion h₀ (block V i j))
          (appendOne (fun l i => IntermediateField.inclusion h₀
            (appendOne (fun l : Fin 0 => l.elim0) (squareNorm (block V) (weights μ ν)) l i)) v)
          (fun i => IntermediateField.inclusion h₀ (weights μ ν i)))
        (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν))) := by
  obtain ⟨F,h₀,e,bF,v,hv,hr⟩ := exists_squareNorm_inverse_sqrt_unary basis
    (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν) 0
    (block_symm V) (squareNorm_pos V hV μ ν hμ hν)
  refine ⟨F,h₀,e,bF,v,?_,hr⟩
  intro i
  rw [hv i, squareNorm_eq_norm_sq V μ ν (fun i => (hμ i).le) (fun j => (hν j).le)]
  congr 1
  apply Real.sqrt_sq
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa only [norm, Fin.addCases_left] using (rowNorm_pos _ hV _ hν i).le
  · simpa only [norm, Fin.addCases_right] using (columnNorm_pos _ hV _ hμ j).le

end PlanarHom.RectangularBackgroundSourceNormSimulation
