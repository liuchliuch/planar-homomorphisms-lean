import PlanarHom.RectangularNormalizedMomentPrograms
import PlanarHom.PositiveUnaryPowerJointAvailability
import PlanarHom.Normalization

/-! NEW actual diagonal-normalization and fixed-moment source programs. A loop
supplies the original diagonal unary, rational interpolation supplies its inverse
positive square root, and the endpoint/moment compiler retains every original
occurrence and companion. No target availability premise is accepted. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PositiveNormalizationSourcePrograms
open Complexity Complexity.MixedCode FiniteLanguageAliases PositiveUnaryRationalPowers
open EndpointUnarySource
variable {K₀ : IntermediateField ℚ ℝ} {q d bt ut : ℕ}

theorem exists_inverse_diagonal_sqrt (basis : Module.Basis (Fin d) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (w : Fin q → K₀) (old : Fin bt) (hpos : ∀i,0<(M old i i:ℝ)) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (v : Fin q → F),
      (∀i,(v i:ℝ)=(Real.sqrt (M old i i:ℝ))⁻¹) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun l i j=>IntermediateField.inclusion h₀ (M l i j))
          (appendOne (fun l i=>IntermediateField.inclusion h₀
            (appendOne U (fun i=>M old i i) l i)) v)
          (fun i=>IntermediateField.inclusion h₀ (w i)))
        (evaluationProblem basis M U w)) := by
  have initial := diagonalUnaryAppendReduction basis M U w old
  obtain ⟨F,h₀,e,bF,v,hv,hr⟩ := exists_joint_power_available basis M
    (appendOne U (fun i=>M old i i)) w (Fin.last ut)
    (by simpa only [appendOne_aux] using hpos) (-1/2) (evaluationProblem basis M U w) initial
  refine ⟨F,h₀,e,bF,v,?_,hr⟩
  intro i
  simp only [appendOne_aux] at hv
  rw [hv i]
  have he : ((-1/2:ℚ):ℝ)=-(1/(2:ℝ)) := by norm_num
  rw [he,Real.rpow_neg (hpos i).le,←Real.sqrt_eq_rpow]

theorem exists_normalized_moment_sources (basis : Module.Basis (Fin d) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀)
    (w : Fin q → K₀) (old : Fin bt) (hpos : ∀i,0<(M old i i:ℝ)) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (C : Matrix (Fin q) (Fin q) F),
      (∀i j,(C i j:ℝ)=diagonalNormalize (fun i j=>(M old i j:ℝ)) i j) ∧
      ∀m:ℕ, Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun _:Fin 1=>C) (fun u:Fin 0=>u.elim0)
          (fun i=>IntermediateField.inclusion h₀ (w i) *
            (IntermediateField.inclusion h₀ (M old i i))^m))
        (evaluationProblem basis M U w)) := by
  obtain ⟨F,h₀,e,bF,v,hv,⟨source⟩⟩ := exists_inverse_diagonal_sqrt basis M U w old hpos
  let MF : Fin bt → Matrix (Fin q) (Fin q) F :=
    fun l i j=>IntermediateField.inclusion h₀ (M l i j)
  let UF : Fin (ut+1+1) → Fin q → F := appendOne
    (fun l i=>IntermediateField.inclusion h₀ (appendOne U (fun i=>M old i i) l i)) v
  let wF : Fin q → F := fun i=>IntermediateField.inclusion h₀ (w i)
  let C := unaryGauge (MF old) v
  have hC : ∀i j,(C i j:ℝ)=diagonalNormalize (fun i j=>(M old i j:ℝ)) i j := by
    intro i j
    change (v i:ℝ)*(M old i j:ℝ)*(v j:ℝ)=_
    rw [hv i,hv j]
    simp only [diagonalNormalize,div_eq_mul_inv,mul_inv_rev]
    ring
  refine ⟨F,h₀,e,bF,C,hC,?_⟩
  intro m
  have hvU : UF (Fin.last (ut+1))=v := appendOne_aux _ _
  have hdU : UF (Fin.castAdd 1 (Fin.last ut)) =
      fun i=>IntermediateField.inclusion h₀ (M old i i) := by
    funext i
    simp only [UF,appendOne_old,appendOne_aux]
  have stage := (gaugeMomentOneQueryReduction bF MF UF wF old
    (Fin.last (ut+1)) (Fin.castAdd 1 (Fin.last ut)) m).trans source
  rw [hvU,hdU] at stage
  have selected := selectedMatrixReduction bF (appendOne MF C) UF
    (fun i=>wF i*(IntermediateField.inclusion h₀ (M old i i))^m) (Fin.last bt)
  simp only [appendOne_aux] at selected
  exact ⟨selected.trans stage⟩

end PlanarHom.PositiveNormalizationSourcePrograms
