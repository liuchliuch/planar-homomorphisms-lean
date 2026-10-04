import PlanarHom.WeightedStretchAppend
import PlanarHom.RealSpectralInterpolation
import PlanarHom.TensorPower
import Mathlib.Data.Real.Sqrt

/-! Actual positive weighted Gram cores and spectral resolution of weighted
chains, including the h=0 inverse-diagonal limit used in source3.7. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.PositiveWeightRemoval
open Matrix
variable {q : ℕ}

def sqrtDiagonal (w : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ := Matrix.diagonal (fun i=>Real.sqrt (w i))
def invSqrtDiagonal (w : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ := Matrix.diagonal (fun i=>(Real.sqrt (w i))⁻¹)
def weightedConjugate (K : Matrix (Fin q) (Fin q) ℝ) (w : Fin q → ℝ) :=
  sqrtDiagonal w * K * sqrtDiagonal w

theorem sqrtDiagonal_sq (w : Fin q → ℝ) (hw : ∀ i,0<w i) :
    sqrtDiagonal w * sqrtDiagonal w = Matrix.diagonal w := by
  rw [sqrtDiagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (hw i).le

theorem sqrt_mul_invSqrt (w : Fin q → ℝ) (hw : ∀ i,0<w i) :
    sqrtDiagonal w * invSqrtDiagonal w = 1 := by
  simp only [sqrtDiagonal,invSqrtDiagonal,Matrix.diagonal_mul_diagonal]
  rw [show (fun i => Real.sqrt (w i) * (Real.sqrt (w i))⁻¹) = fun _ => 1 from
    funext (fun i => mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hw i))))]
  exact Matrix.diagonal_one

theorem invSqrt_mul_sqrt (w : Fin q → ℝ) (hw : ∀ i,0<w i) :
    invSqrtDiagonal w * sqrtDiagonal w = 1 := by
  simp only [sqrtDiagonal,invSqrtDiagonal,Matrix.diagonal_mul_diagonal]
  rw [show (fun i => (Real.sqrt (w i))⁻¹ * Real.sqrt (w i)) = fun _ => 1 from
    funext (fun i => inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hw i))))]
  exact Matrix.diagonal_one

theorem invSqrt_sq (w : Fin q → ℝ) (hw : ∀ i,0<w i) :
    invSqrtDiagonal w * invSqrtDiagonal w = Matrix.diagonal (fun i=>(w i)⁻¹) := by
  simp only [invSqrtDiagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← _root_.mul_inv_rev,Real.mul_self_sqrt (hw i).le]

theorem weightedConjugate_posDef (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.PosDef)
    (w : Fin q → ℝ) (hw : ∀ i,0<w i) : (weightedConjugate K w).PosDef := by
  have hinj : Function.Injective (sqrtDiagonal w).mulVec := by
    intro x y h
    funext i
    have hi := congrFun h i
    simp only [sqrtDiagonal,Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hw i))) hi
  simpa [weightedConjugate,sqrtDiagonal,Matrix.diagonal_conjTranspose] using
    hK.conjTranspose_mul_mul_same hinj

/-- Pure noncommutative chain identity for any explicit inverse pair. -/
theorem sandwich_power_chain {C R : Type} [Fintype C] [DecidableEq C] [Semiring R]
    (S J K : Matrix C C R) (hSJ : S*J=1) (hJS : J*S=1) (n : ℕ) :
    J * (S*K*S)^(n+1) * J = K * ((S*S)*K)^n := by
  have hleft : (S*K*S)*J=S*K := by simp only [Matrix.mul_assoc,hSJ,Matrix.mul_one]
  have hright : J*((S*S)*K)=S*K := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hJS,Matrix.one_mul]
  induction n with
  | zero =>
    simp only [Nat.zero_add,pow_one,pow_zero,Matrix.mul_one]
    rw [Matrix.mul_assoc,hleft,← Matrix.mul_assoc,hJS,Matrix.one_mul]
  | succ n ih =>
    rw [pow_succ]
    calc
      _ = (J*(S*K*S)^(n+1))*((S*K*S)*J) := by simp only [Matrix.mul_assoc]
      _ = (J*(S*K*S)^(n+1))*(J*((S*S)*K)) := by rw [hleft,hright]
      _ = (J*(S*K*S)^(n+1)*J)*((S*S)*K) := by simp only [Matrix.mul_assoc]
      _ = (K*((S*S)*K)^n)*((S*S)*K) := by rw [ih]
      _ = _ := by rw [pow_succ,Matrix.mul_assoc]

theorem weightedChain_conjugation (K : Matrix (Fin q) (Fin q) ℝ)
    (w : Fin q → ℝ) (hw : ∀ i,0<w i) (n : ℕ) (hn : 0<n) :
    Complexity.MixedCode.weightedChain K w n =
      invSqrtDiagonal w * (weightedConjugate K w)^n * invSqrtDiagonal w := by
  cases n with
  | zero => omega
  | succ n =>
    symm
    simpa only [weightedConjugate,Complexity.MixedCode.weightedChain,Nat.succ_sub_one,sqrtDiagonal_sq w hw]
      using sandwich_power_chain (sqrtDiagonal w) (invSqrtDiagonal w) K
        (sqrt_mul_invSqrt w hw) (invSqrt_mul_sqrt w hw) n

def scaledProjector (K : Matrix (Fin q) (Fin q) ℝ) (w : Fin q → ℝ)
    (i : Fin (Nat.card (spectrum ℝ (weightedConjugate K w)))) : Matrix (Fin q) (Fin q) ℝ :=
  invSqrtDiagonal w * RealSpectralInterpolation.projector (weightedConjugate K w) i * invSqrtDiagonal w

theorem weightedChain_spectral (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.PosDef)
    (w : Fin q → ℝ) (hw : ∀ i,0<w i) (n : ℕ) (hn : 0<n) :
    Complexity.MixedCode.weightedChain K w n =
      ∑ i, RealSpectralInterpolation.scalar (weightedConjugate K w) i ^ n • scaledProjector K w i := by
  rw [weightedChain_conjugation K w hw n hn,
    RealSpectralInterpolation.matrix_pow_eq _ (weightedConjugate_posDef K hK w hw).1]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,scaledProjector]

theorem scaledProjector_sum (K : Matrix (Fin q) (Fin q) ℝ) (hK : K.PosDef)
    (w : Fin q → ℝ) (hw : ∀ i,0<w i) :
    (∑ i, scaledProjector K w i) = Matrix.diagonal (fun i=>(w i)⁻¹) := by
  have hp := RealSpectralInterpolation.matrix_pow_eq (weightedConjugate K w)
    (weightedConjugate_posDef K hK w hw).1 0
  simp only [pow_zero,one_smul] at hp
  simp only [scaledProjector]
  rw [← Matrix.sum_mul,← Matrix.mul_sum,← hp,Matrix.mul_one,invSqrt_sq w hw]

/-- The actual fixed weighted two-edge/parallel gadget from source3.6. -/
def gramCore (B : Matrix (Fin q) (Fin q) ℝ) (w : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => ((B * Matrix.diagonal w * B) i j) ^ max 1 (q-1)

theorem gramCore_posDef (B : Matrix (Fin q) (Fin q) ℝ)
    (hs : ∀ i j,B i j=B j i) (w : Fin q → ℝ) (hw : ∀ i,0<w i)
    (hnonzero : ∀ i,B i≠0) (hproj : ∀ i j,i≠j→∀t:ℝ,B i≠t • B j) :
    (gramCore B w).PosDef := by
  have ht : B.transpose=B := by ext i j; exact hs j i
  simpa only [ht,gramCore] using hadamard_weighted_gram_posDef B w hw hnonzero hproj

end PlanarHom.PositiveWeightRemoval
