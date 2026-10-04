import PlanarHom.FixedRealNormNormalization

/-! NEW exact real semantics of the represented rectangular normalization.
Both RectangularBackgroundSourceNormSimulation.norm sums use the original opposite-side weights; moments retain each
original vertex weight. No equality of side sizes is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealRectangularNormalization
open DensePolynomial RectangularSourceNormSimulation RectangularBackgroundSourceNormSimulation
open RectangularWeightedNormNormalization EndpointUnarySource FixedRealNormNormalization
variable {n e p s : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K] [Algebra K ℝ]
variable [Nonempty (Fin p)] [Nonempty (Fin s)]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K)

theorem normSquare_real (V : Matrix (Fin p) (Fin s) K) (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0≤algebraMap K ℝ (μ i)) (hν : ∀ j,0≤algebraMap K ℝ (ν j)) (i : Fin (p+s)) :
    algebraMap K ℝ (squareNorm (block V) (weights μ ν) i) =
      RectangularBackgroundSourceNormSimulation.norm (fun i j => algebraMap K ℝ (V i j)) (fun i => algebraMap K ℝ (μ i))
        (fun j => algebraMap K ℝ (ν j)) i ^ 2 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [squareNorm_left]
    simp only [RectangularBackgroundSourceNormSimulation.norm,Fin.addCases_left,rowNorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => mul_nonneg (hν j) (sq_nonneg _)))]
    simp only [map_sum,map_mul,map_pow]
  · rw [squareNorm_right]
    simp only [RectangularBackgroundSourceNormSimulation.norm,Fin.addCases_right,columnNorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (sq_nonneg _)))]
    simp only [map_sum,map_mul,map_pow]

theorem norm_pos (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) (i : Fin (p+s)) :
    0<RectangularBackgroundSourceNormSimulation.norm (fun i j => algebraMap K ℝ (V i j)) (fun i => algebraMap K ℝ (μ i))
      (fun j => algebraMap K ℝ (ν j)) i := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa only [RectangularBackgroundSourceNormSimulation.norm,Fin.addCases_left] using rowNorm_pos _ hV _ hν i
  · simpa only [RectangularBackgroundSourceNormSimulation.norm,Fin.addCases_right] using columnNorm_pos _ hV _ hμ j

theorem normSquare_pos (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) (i : Fin (p+s)) :
    0<algebraMap K ℝ (squareNorm (block V) (weights μ ν) i) := by
  rw [normSquare_real V μ ν (fun i => (hμ i).le) (fun j => (hν j).le)]
  exact sq_pos_of_pos (norm_pos V hV μ ν hμ hν i)

def model (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) :=
  normModel basis (fun _ : Fin 1 => block V) (weights μ ν) 0 (normSquare_pos V hV μ ν hμ hν)

def matrix (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) :=
  normalizedMatrix basis (fun _ : Fin 1 => block V) (weights μ ν) 0 (normSquare_pos V hV μ ν hμ hν)

theorem matrix_real (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) :
    let P := model basis V hV μ ν hμ hν
    (fun i j => algebraMap P.Carrier ℝ (matrix basis V hV μ ν hμ hν i j)) =
      block (normalized (fun i j => algebraMap K ℝ (V i j))
        (fun i => algebraMap K ℝ (μ i)) (fun j => algebraMap K ℝ (ν j))) := by
  dsimp only
  let P := model basis V hV μ ν hμ hν
  have hv : ∀ i,algebraMap P.Carrier ℝ (P.powers 0 i) =
      (RectangularBackgroundSourceNormSimulation.norm (fun i j => algebraMap K ℝ (V i j)) (fun i => algebraMap K ℝ (μ i))
        (fun j => algebraMap K ℝ (ν j)) i)⁻¹ := by
    intro i
    have h := normModel_power_real basis (fun _ : Fin 1 => block V) (weights μ ν) 0
      (normSquare_pos V hV μ ν hμ hν) i
    change algebraMap P.Carrier ℝ (P.powers 0 i) = (Real.sqrt (algebraMap K ℝ (squareNorm (block V) (weights μ ν) i)))⁻¹ at h
    rw [h]
    rw [normSquare_real V μ ν (fun i => (hμ i).le) (fun j => (hν j).le),
      Real.sqrt_sq (norm_pos V hV μ ν hμ hν i).le]
  funext i j
  change algebraMap P.Carrier ℝ (P.powers 0 i*P.inclusion (block V i j)*P.powers 0 j)=_
  rw [map_mul,map_mul,P.real_inclusion,hv,hv]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [block_left_left,block_left_right,block_right_left,block_right_right,
        RectangularBackgroundSourceNormSimulation.norm,Fin.addCases_left,Fin.addCases_right,normalized,map_zero]
  · simp
  · simp only [div_eq_mul_inv,mul_inv_rev];ring
  · simp only [div_eq_mul_inv,mul_inv_rev];ring
  · simp

theorem moment_real (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j,0<algebraMap K ℝ (V i j))
    (μ : Fin p → K) (ν : Fin s → K)
    (hμ : ∀ i,0<algebraMap K ℝ (μ i)) (hν : ∀ j,0<algebraMap K ℝ (ν j)) (m : ℕ) (i : Fin (p+s)) :
    let P := model basis V hV μ ν hμ hν
    algebraMap P.Carrier ℝ (P.inclusion (weights μ ν i)*P.inclusion (squareNorm (block V) (weights μ ν) i)^m) =
      algebraMap K ℝ (weights μ ν i) * RectangularBackgroundSourceNormSimulation.norm (fun i j => algebraMap K ℝ (V i j))
        (fun i => algebraMap K ℝ (μ i)) (fun j => algebraMap K ℝ (ν j)) i ^ (2*m) := by
  dsimp only
  rw [map_mul,map_pow,(model basis V hV μ ν hμ hν).real_inclusion,
    (model basis V hV μ ν hμ hν).real_inclusion,
    normSquare_real V μ ν (fun i => (hμ i).le) (fun j => (hν j).le),pow_mul]

end PlanarHom.FixedRealRectangularNormalization
