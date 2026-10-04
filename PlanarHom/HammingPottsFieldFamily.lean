import PlanarHom.HammingPottsProductIdentities
import PlanarHom.UniformSquaredDistanceKernel

/-! NEW exact source-field polynomial presentation for size-selective Hamming
Potts isolation, with its explicit degree bound and literal kernel-square value. -/
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators Polynomial
namespace PlanarHom.HammingPottsFieldFamily
open Polynomial HammingPottsProductIdentities HammingKernelTensor CartesianGeometry
open Complexity EffectiveProductTransfer
variable {K : IntermediateField ℚ ℝ}

/-- Literal diagonal/off-diagonal clique-square polynomials in the original field. -/
def factor (K : IntermediateField ℚ ℝ) (k : ℕ) (same : Bool) : K[X] :=
  if same then 1+C ((k:K)-1)*X^2 else C 2*X+C ((k:K)-2)*X^2

def family {q d : ℕ} (sizes : Fin d→ℕ) (e : Fin q≃Color sizes) :
    Matrix (Fin q) (Fin q) K[X] := fun i j=>∏r, factor K (sizes r) (decide (e i r=e j r))

def targetK {q d : ℕ} (sizes : Fin d→ℕ) (s : ℕ) (e : Fin q≃Color sizes) :
    Matrix (Fin q) (Fin q) K := fun i j=>∏r, if sizes r=s ∧ e i r=e j r then 2 else 1

theorem factor_degree (k : ℕ) (same : Bool) : (factor K k same).natDegree ≤ 2 := by
  cases same
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · have h : (C (2:K)*X).natDegree ≤ 1 := by
        simpa only [pow_one] using natDegree_C_mul_X_pow_le (2:K) 1
      exact h.trans (by decide)
    · exact natDegree_C_mul_X_pow_le _ _
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact natDegree_C_mul_X_pow_le _ _

theorem family_degree {q d : ℕ} (sizes : Fin d→ℕ) (e : Fin q≃Color sizes) (i j : Fin q) :
    (family (K:=K) sizes e i j).natDegree ≤ 2*d := by
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _r : Fin d, 2 := Finset.sum_le_sum (fun r _=>factor_degree _ _)
    _ = _ := by simp [Nat.mul_comm]

@[simp] theorem factor_map (k : ℕ) (same : Bool) :
    (factor K k same).map K.val.toRingHom = CliqueSizePolynomials.entry k same := by
  have h2 : ((2:K):ℝ)=2 := map_ofNat K.val.toRingHom 2
  cases same <;> simp [factor,CliqueSizePolynomials.entry,CliqueSizePolynomials.diagonal,
    CliqueSizePolynomials.offDiagonal,h2]

theorem realFamily_eq {q d : ℕ} (sizes : Fin d→ℕ) (e : Fin q≃Color sizes)
    (t : ℝ) (i j : Fin q) :
    polynomialRealFamily (family (K:=K) sizes e) t i j = squareFamily sizes t (e i) (e j) := by
  rw [squareFamily_entry]
  simp only [polynomialRealFamily,family,Polynomial.map_prod,Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro r _
  rw [factor_map]

@[simp] theorem targetK_real {q d : ℕ} (sizes : Fin d→ℕ) (s : ℕ) (e : Fin q≃Color sizes)
    (i j : Fin q) : (targetK (K:=K) sizes s e i j : ℝ) = target sizes s (e i) (e j) := by
  change K.val.toRingHom (∏r, if sizes r=s ∧ e i r=e j r then 2 else 1) = _
  simp only [target,map_prod]
  apply Finset.prod_congr rfl
  intro r _
  split_ifs
  · exact map_ofNat K.val.toRingHom 2
  · exact map_one K.val.toRingHom

theorem square_distanceKernel_real {q d : ℕ} (sizes : Fin d→ℕ) (G : SimpleGraph (Fin q))
    (e : G ≃g hammingGraph (fun r=>Fin (sizes r))) (t : ℚ) (i j : Fin q) :
    ((DistanceKernelEvaluationMachines.matrix (K:=K) G t ^ 2) i j : ℝ) =
      squareFamily sizes (t:ℝ) (e i) (e j) := by
  have hd (a b : Fin q) : G.dist a b =
      (hammingGraph (fun r=>Fin (sizes r))).dist (e a) (e b) := by
    unfold SimpleGraph.dist
    rw [Boolean.graphIso_edist_eq e]
  change K.val.toRingHom ((DistanceKernelEvaluationMachines.matrix G t ^ 2) i j) = _
  simp only [pow_two,Matrix.mul_apply,map_sum,map_mul]
  change (∑k, (DistanceKernelEvaluationMachines.matrix (K:=K) G t i k:ℝ)*
    (DistanceKernelEvaluationMachines.matrix (K:=K) G t k j:ℝ)) = _
  simp_rw [DistanceKernelEvaluationMachines.matrix_real]
  unfold squareFamily
  rw [Matrix.mul_apply]
  simp only [EntropyCompletion.distanceKernel]
  simp_rw [hd]
  exact Fintype.sum_equiv e.toEquiv _ _ (fun _=>rfl)

theorem family_nat_value {q d : ℕ} (sizes : Fin d→ℕ) (G : SimpleGraph (Fin q))
    (e : G ≃g hammingGraph (fun r=>Fin (sizes r))) (n : ℕ) :
    polynomialFamily (family (K:=K) sizes e.toEquiv) n =
      DistanceKernelEvaluationMachines.matrix G (n:ℚ)^2 := by
  funext i j
  apply K.val.injective
  change (polynomialFamily (family (K:=K) sizes e.toEquiv) n i j:ℝ) =
    ((DistanceKernelEvaluationMachines.matrix (K:=K) G (n:ℚ)^2) i j:ℝ)
  rw [polynomialFamily_coe,realFamily_eq,square_distanceKernel_real]
  norm_cast

end PlanarHom.HammingPottsFieldFamily
