import PlanarHom.TraceExponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The exponential gradient on a symmetric matrix subspace

The supported gradient maps a matrix `C` to the trace pairing against `exp C`,
restricted to the same subspace. It is analytic, globally injective, and has an
invertible derivative everywhere on every real symmetric matrix subspace.
-/

open scoped BigOperators Matrix.Norms.Operator
open Matrix
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace PlanarHom.ExponentialGradient

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of the continuous trace pairing to a matrix subspace. -/
def restrictedPairing (S : Submodule ℝ (Matrix ι ι ℝ)) :
    Matrix ι ι ℝ →L[ℝ] (S →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => (TraceExponential.tracePairing P).comp S.subtypeL
      map_add' := by intro A B; ext D; simp
      map_smul' := by intro r A; ext D; simp }

omit [DecidableEq ι] in
@[simp] theorem restrictedPairing_apply (S : Submodule ℝ (Matrix ι ι ℝ))
    (P : Matrix ι ι ℝ) (D : S) :
    restrictedPairing S P D = (P * (D : Matrix ι ι ℝ)).trace := rfl

/-- The exponential gradient on a matrix subspace, taking values in its continuous dual. -/
def gradient (S : Submodule ℝ (Matrix ι ι ℝ)) (C : S) : S →L[ℝ] ℝ :=
  restrictedPairing S (NormedSpace.exp ℝ (C : Matrix ι ι ℝ))

@[simp] theorem gradient_apply (S : Submodule ℝ (Matrix ι ι ℝ)) (C D : S) :
    gradient S C D = (NormedSpace.exp ℝ (C : Matrix ι ι ℝ) * (D : Matrix ι ι ℝ)).trace := rfl

/-- The exact derivative of the restricted gradient. -/
def gradientDerivative (S : Submodule ℝ (Matrix ι ι ℝ)) (C : S) : S →L[ℝ] (S →L[ℝ] ℝ) :=
  (restrictedPairing S).comp
    ((fderiv ℝ (NormedSpace.exp ℝ) (C : Matrix ι ι ℝ)).comp S.subtypeL)

@[simp] theorem gradientDerivative_apply (S : Submodule ℝ (Matrix ι ι ℝ)) (C D E : S) :
    gradientDerivative S C D E =
      (fderiv ℝ (NormedSpace.exp ℝ) (C : Matrix ι ι ℝ) (D : Matrix ι ι ℝ) *
        (E : Matrix ι ι ℝ)).trace := rfl

/-- The supported gradient is real analytic everywhere. -/
theorem analyticAt_gradient (S : Submodule ℝ (Matrix ι ι ℝ)) (C : S) :
    AnalyticAt ℝ (gradient S) C := by
  have hsub : AnalyticAt ℝ (fun D : S => (D : Matrix ι ι ℝ)) C :=
    S.subtypeL.analyticAt C
  have he : AnalyticAt ℝ (fun D : S => NormedSpace.exp ℝ (D : Matrix ι ι ℝ)) C :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (C : Matrix ι ι ℝ)).comp hsub
  have hp : AnalyticAt ℝ (restrictedPairing S) (NormedSpace.exp ℝ (C : Matrix ι ι ℝ)) :=
    ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Matrix ι ι ℝ) (F := S →L[ℝ] ℝ)
      (restrictedPairing S) _
  exact AnalyticAt.comp (𝕜 := ℝ) (E := S) (F := Matrix ι ι ℝ) (G := S →L[ℝ] ℝ) hp he

/-- The differentiated exponential defines the derivative of the supported gradient. -/
theorem hasFDerivAt_gradient (S : Submodule ℝ (Matrix ι ι ℝ)) (C : S) :
    HasFDerivAt (gradient S) (gradientDerivative S C) C := by
  have he : HasFDerivAt (fun D : S => NormedSpace.exp ℝ (D : Matrix ι ι ℝ))
      ((fderiv ℝ (NormedSpace.exp ℝ) (C : Matrix ι ι ℝ)).comp S.subtypeL) C :=
    (TraceExponential.hasFDerivAt_exp_series (C : Matrix ι ι ℝ)).differentiableAt.hasFDerivAt.comp C
      S.subtypeL.hasFDerivAt
  have hp : HasFDerivAt (restrictedPairing S) (restrictedPairing S)
      (NormedSpace.exp ℝ (C : Matrix ι ι ℝ)) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Matrix ι ι ℝ) (F := S →L[ℝ] ℝ)
      (restrictedPairing S)
  exact HasFDerivAt.comp (𝕜 := ℝ) (E := S) (F := Matrix ι ι ℝ) (G := S →L[ℝ] ℝ) C hp he

theorem fderiv_gradient (S : Submodule ℝ (Matrix ι ι ℝ)) (C : S) :
    fderiv ℝ (gradient S) C = gradientDerivative S C :=
  HasFDerivAt.fderiv (𝕜 := ℝ) (E := S) (F := S →L[ℝ] ℝ) (hasFDerivAt_gradient S C)

/-- Strict positivity of the restricted gradient derivative. -/
theorem gradientDerivative_pos (S : Submodule ℝ (Matrix ι ι ℝ))
    (hS : ∀ C ∈ S, C.IsHermitian) (C D : S) (hne : D ≠ 0) :
    0 < gradientDerivative S C D D := by
  apply TraceExponential.trace_fderiv_exp_mul_self_pos
    (hS C C.property) (hS D D.property)
  exact fun h => hne (Subtype.ext h)

/-- The restricted derivative is injective because its quadratic form is positive definite. -/
theorem gradientDerivative_injective (S : Submodule ℝ (Matrix ι ι ℝ))
    (hS : ∀ C ∈ S, C.IsHermitian) (C : S) :
    Function.Injective (gradientDerivative S C) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro D hD
  by_contra hne
  have hp := gradientDerivative_pos S hS C D hne
  have hz := congrArg (fun L : S →L[ℝ] ℝ => L D) hD
  simp only [ContinuousLinearMap.zero_apply] at hz
  linarith

omit [DecidableEq ι] in
/-- A finite-dimensional matrix subspace and its continuous dual have equal dimension. -/
theorem finrank_continuousDual (S : Submodule ℝ (Matrix ι ι ℝ)) :
    Module.finrank ℝ (S →L[ℝ] ℝ) = Module.finrank ℝ S := by
  rw [← (LinearMap.toContinuousLinearMap : (S →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (S →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- The derivative is bijective at every point of a symmetric matrix subspace. -/
theorem gradientDerivative_bijective (S : Submodule ℝ (Matrix ι ι ℝ))
    (hS : ∀ C ∈ S, C.IsHermitian) (C : S) :
    Function.Bijective (gradientDerivative S C) := by
  let e : S ≃ₗ[ℝ] (S →L[ℝ] ℝ) :=
    LinearEquiv.ofInjectiveOfFinrankEq (K := ℝ) (V := S) (V' := S →L[ℝ] ℝ)
      (gradientDerivative S C).toLinearMap
      (gradientDerivative_injective S hS C) (finrank_continuousDual S).symm
  exact e.bijective

/-- The derivative API needed by the analytic inverse function theorem. -/
theorem fderiv_gradient_bijective (S : Submodule ℝ (Matrix ι ι ℝ))
    (hS : ∀ C ∈ S, C.IsHermitian) (C : S) :
    Function.Bijective (fderiv ℝ (gradient S) C) := by
  rw [fderiv_gradient]
  exact gradientDerivative_bijective S hS C

/-- The supported exponential gradient is globally injective on a symmetric subspace. -/
theorem gradient_injective (S : Submodule ℝ (Matrix ι ι ℝ))
    (hS : ∀ C ∈ S, C.IsHermitian) : Function.Injective (gradient S) := by
  intro C D heq
  by_contra hne
  let V : S := D - C
  have hV : V ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let f : ℝ → ℝ := fun t => gradient S (C + t • V) V
  have hd (t : ℝ) : HasDerivAt f (gradientDerivative S (C + t • V) V V) t := by
    have hline : HasDerivAt (fun s : ℝ => C + s • V) V t := by
      simpa only [id_eq, one_smul] using (((hasDerivAt_id t).smul_const V).const_add C)
    have hg := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := S) (E := S →L[ℝ] ℝ)
      t (hasFDerivAt_gradient S (C + t • V)) hline
    have hev : HasFDerivAt (ContinuousLinearMap.apply ℝ ℝ V)
        (ContinuousLinearMap.apply ℝ ℝ V) (gradient S (C + t • V)) :=
      ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := S →L[ℝ] ℝ) (F := ℝ)
        (ContinuousLinearMap.apply ℝ ℝ V)
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := S →L[ℝ] ℝ) (E := ℝ) t hev hg
  have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hd
    (fun t => gradientDerivative_pos S hS (C + t • V) V hV)
  have hlt := hmono (show (0 : ℝ) < 1 by norm_num)
  have hend : C + V = D := by dsimp [V]; abel
  simp only [f, zero_smul, add_zero, one_smul, hend, heq, lt_self_iff_false] at hlt

end PlanarHom.ExponentialGradient
