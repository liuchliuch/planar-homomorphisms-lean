import PlanarHom.BooleanTensorFPClosure
import PlanarHom.BooleanTensorSpectral
import PlanarHom.AlgebraicProductOverfield
import PlanarHom.BooleanPDNormalization

/-! NEW equal-factor source assembly using a separately identified zero-field
Ising foundation. All finite tensor, scalar and field-descent machines are
constructed; no tractability of the target tensor is supplied. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorEasyAssembly
open Complexity Complexity.MixedCode BooleanTensorFPClosure AlgebraicProductInterpolation

def isingMatrix {K : Type} [One K] (ρ : K) : Matrix Bool Bool K := fun i j=>if i=j then 1 else ρ

def PositiveIsingFoundation : Prop :=
  ∀ (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] (dimension : ℕ)
    (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K),0<(ρ:ℝ)→
    (evaluationProblem basis (fun _:Fin 1=>isingMatrix ρ) emptyUnaries (fun _=>1)).InFP

theorem equal_factor_inFP (hf:PositiveIsingFoundation)
    {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K] {dimension:ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (A : Matrix Bool Bool K)
    (hs:A true false=A false true) (hd:A false false=A true true)
    (hdiag:0<(A false false:ℝ)) (hoff:0<(A false true:ℝ)) :
    (evaluationProblem basis (fun _:Fin 1=>A) emptyUnaries (fun _=>1)).InFP := by
  have hn:A false false≠0:=by
    intro h
    simpa [h] using hdiag
  have hr:0<((A false true/A false false:K):ℝ):=by
    change 0<K.val.toRingHom (A false true/A false false)
    rw [map_div₀]
    exact div_pos hoff hdiag
  have hm:A=A false false • isingMatrix (A false true/A false false):=by
    funext i j
    cases i <;> cases j <;> simp [isingMatrix,Matrix.smul_apply,smul_eq_mul,←hd,hs] <;> field_simp [hn]
  rw [hm]
  exact scalar_inFP basis _ _ (hf K dimension basis _ hr)

theorem scaled_equal_tensor_inFP (hf:PositiveIsingFoundation)
    {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K] {dimension d : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) {C : Type} [Fintype C]
    (e : C≃(Fin d→Bool)) (γ : K) (A : Fin d→Matrix Bool Bool K)
    (hs:∀i,A i true false=A i false true) (hd:∀i,A i false false=A i true true)
    (hdiag:∀i,0<(A i false false:ℝ)) (hoff:∀i,0<(A i false true:ℝ)) :
    (evaluationProblem basis (fun _:Fin 1=>fun i j=>γ*BooleanTensorSpectral.tensor A (e i) (e j))
      emptyUnaries (fun _=>1)).InFP :=
  color_inFP basis e (γ • BooleanTensorSpectral.tensor A)
    (scalar_inFP basis γ _ (tensor_inFP basis A
      (fun i=>equal_factor_inFP hf basis (A i) (hs i) (hd i) (hdiag i) (hoff i))))

def sourceConstants {d:ℕ} (γ:ℝ) (F:Fin d→Matrix Bool Bool ℝ) : Option (Fin d×Bool×Bool)→ℝ :=
  fun p=>p.elim γ (fun p=>F p.1 p.2.1 p.2.2)

theorem sourceConstants_algebraic {d:ℕ} (γ:ℝ) (F:Fin d→Matrix Bool Bool ℝ)
    (hγ:IsAlgebraic ℚ γ) (hF:∀i j k,IsAlgebraic ℚ (F i j k)) :
    ∀p,IsAlgebraic ℚ (sourceConstants γ F p) := by
  rintro (_|⟨i,j,k⟩)
  · exact hγ
  · exact hF i j k

theorem source_scaled_equal_tensor_inFP (hf:PositiveIsingFoundation)
    (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀] {dimension d:ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K₀) {C:Type} [Fintype C]
    (M : Matrix C C K₀) (e:C≃Boolean.Cube d) (γ:ℝ) (hγalg:IsAlgebraic ℚ γ)
    (F:Fin d→Matrix Bool Bool ℝ) (halg:∀i j k,IsAlgebraic ℚ (F i j k))
    (hs:∀i,F i true false=F i false true) (hd:∀i,F i false false=F i true true)
    (hdiag:∀i,0<F i false false) (hoff:∀i,0<F i false true)
    (hsource:Matrix.reindex e e (fun i j=>(M i j:ℝ))=γ • CubeTensorExponential.tensor F) :
    (evaluationProblem basis (fun _:Fin 1=>M) emptyUnaries (fun _=>1)).InFP := by
  let constants:=sourceConstants γ F
  let E:=extensionField K₀ constants
  letI:FiniteDimensional ℚ E:=extension_finiteDimensional K₀ constants
    (sourceConstants_algebraic γ F hγalg halg)
  let φ:=sourceInclusion K₀ constants
  let bE:=extensionBasis K₀ constants (sourceConstants_algebraic γ F hγalg halg)
  let γE:E:=targetValue K₀ constants none
  let FE:Fin d→Matrix Bool Bool E:=fun i j k=>targetValue K₀ constants (some (i,j,k))
  have hFE:=scaled_equal_tensor_inFP hf bE e γE FE
    (fun i=>Subtype.ext (hs i)) (fun i=>Subtype.ext (hd i)) hdiag hoff
  have hm:(fun i j=>φ (M i j))=fun i j=>γE*BooleanTensorSpectral.tensor FE (e i) (e j):=by
    funext i j
    apply Subtype.ext
    have h:=congrArg (fun A:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ=>A (e i) (e j)) hsource
    simpa [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.smul_apply,
      CubeTensorExponential.tensor,BooleanTensorSpectral.tensor,smul_eq_mul,
      γE,FE,constants,sourceConstants,map_prod] using h
  apply field_descent_inFP basis bE φ M
  have hfamily:(fun _:Fin 1=>fun i j=>φ (M i j))=
      fun _:Fin 1=>fun i j=>γE*BooleanTensorSpectral.tensor FE (e i) (e j):=funext (fun _=>hm)
  rw [hfamily]
  exact hFE

end PlanarHom.BooleanTensorEasyAssembly
