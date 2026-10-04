import PlanarHom.EndpointLoopAvailability
import PlanarHom.BooleanPDNormalization
import PlanarHom.CubeGraphMetric

/-! Exact endpoint-loop algebra in equations5.1–5.2. A source loop counts both
endpoint decorations, and the known scalar is a genuine matrix scalar. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanLoopNormalization
open EndpointLoopMachines BooleanPDNormalization

variable {ι : Type} [Fintype ι]

theorem decorated_eq_diagonal_congruence {C R : Type} [Fintype C] [DecidableEq C] [CommSemiring R]
    (A : Matrix C C R) (k : ℕ) :
    decorated A k=(Matrix.diagonal (fun i=>A i i))^k*A*(Matrix.diagonal (fun i=>A i i))^k := by
  rw [Matrix.diagonal_pow]
  ext i j
  simp [decorated,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem decorated_tensor (γ : ℝ) (F : ι→Matrix Bool Bool ℝ) (k : ℕ) :
    decorated (γ • CubeTensorExponential.tensor F) k =
      γ^(2*k+1) • CubeTensorExponential.tensor (fun r=>decorated (F r) k) := by
  ext z z'
  simp only [decorated,Matrix.smul_apply,smul_eq_mul,CubeTensorExponential.tensor,mul_pow,
    Finset.prod_pow,Finset.prod_mul_distrib]
  rw [show 2*k+1=k+1+k by omega,pow_add,pow_add,pow_one]
  ring

theorem decorated_normalForm (θ w : ℝ) (hθ : θ≠0) (k : ℕ) :
    decorated (normalForm θ w) k=normalForm (θ^(2*k+1)) w := by
  have hk : θ^k≠0 := pow_ne_zero _ hθ
  ext i j
  cases i <;> cases j <;> simp only [decorated,normalForm,Bool.false_eq_true,Bool.true_eq_false,
    ↓reduceIte]
  · rw [show 2*k+1=k+1+k by omega,pow_add,pow_add,pow_one]
  · rw [inv_pow]
    field_simp
  · rw [inv_pow]
    field_simp
  · rw [show 2*k+1=k+1+k by omega,pow_add,pow_add,pow_one]
    simp only [mul_inv_rev,inv_pow]
    ring

theorem normalForm_schur_W (θ w x : ℝ) :
    (fun i j=>normalForm θ w i j*Boolean.W x i j)=normalForm θ (w*x) := by
  ext i j
  by_cases h:i=j <;> simp [normalForm,Boolean.W,h]

/-- The exact tensor parameter family after source endpoint loops and the
cube distance kernel, in the original fixed cube coordinates. -/
theorem source_family {d : ℕ} (γ : ℝ) (hγ : γ≠0) (θ w : Fin d→ℝ)
    (hθ : ∀r,θ r≠0) (k : ℕ) (x : ℝ) :
    (fun z z'=>((γ^(2*k+1))⁻¹ • decorated
      (γ • CubeTensorExponential.tensor (fun r=>normalForm (θ r) (w r))) k) z z' *
        EntropyCompletion.distanceKernel (Boolean.cubeGraph d) x z z') =
      CubeTensorExponential.tensor (fun r=>normalForm ((θ r)^(2*k+1)) (w r*x)) := by
  rw [decorated_tensor]
  have hg : (γ^(2*k+1))⁻¹ * γ^(2*k+1)=1 := inv_mul_cancel₀ (pow_ne_zero _ hγ)
  simp only [smul_smul,hg,one_smul]
  rw [Boolean.cubeGraph_distanceKernel_eq_tensor]
  ext z z'
  simp only [CubeTensorExponential.tensor,Boolean.tensor,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _
  rw [decorated_normalForm (θ r) (w r) (hθ r)]
  exact congrFun (congrFun (normalForm_schur_W ((θ r)^(2*k+1)) (w r) x) (z r)) (z' r)

end PlanarHom.BooleanLoopNormalization
