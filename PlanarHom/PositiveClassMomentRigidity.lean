import PlanarHom.PositiveRealCoreGrams
import PlanarHom.PositiveDefiniteDichotomyAssembly
import PlanarHom.AvailableCommonCubeChart
import PlanarHom.PositiveUnitDiagonalRigidity

/-! The finite-matrix class-moment obstruction from §§8.1 and11.2.
The matrix used here is literally `diag(sqrt μ) * (C*C) * diag(sqrt μ)`.
Positive definiteness uses an explicit invertibility proof for C; distinct
rows alone are never treated as nonsingularity. Classification inputs are
recorded in the source-facing assembly rather than hidden in this core. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveClassMomentRigidity
open PositiveRealCore
variable {I : Type} [Fintype I] [DecidableEq I]

def momentSquare (C : Matrix I I ℝ) (μ : I → ℝ) : Matrix I I ℝ :=
  decorated (C*C) μ μ

theorem square_posDef (C : Matrix I I ℝ) (hs : C.IsHermitian) (hu : IsUnit C) :
    (C*C).PosDef := by
  simpa only [hs.eq] using
    Matrix.PosDef.conjTranspose_mul_self C (Matrix.mulVec_injective_iff_isUnit.mpr hu)

theorem momentSquare_posDef (C : Matrix I I ℝ) (hs : C.IsHermitian) (hu : IsUnit C)
    (μ : I → ℝ) (hμ : ∀ i,0<μ i) : (momentSquare C μ).PosDef := by
  have hd : (rootDiagonal μ).PosDef := Matrix.posDef_diagonal_iff.mpr
    (fun i=>Real.sqrt_pos.mpr (hμ i))
  have hp := (square_posDef C hs hu).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr hd.isUnit)
  simpa only [hd.1.eq,momentSquare,decorated] using hp

omit [DecidableEq I] in
theorem square_positive [Nonempty I] (C : Matrix I I ℝ) (hp : ∀ i j,0<C i j) :
    ∀ i j,0<(C*C) i j := by
  intro i j
  exact Finset.sum_pos (fun k _=>mul_pos (hp i k) (hp k j)) Finset.univ_nonempty

theorem momentSquare_positive [Nonempty I] (C : Matrix I I ℝ) (hp : ∀ i j,0<C i j)
    (μ : I → ℝ) (hμ : ∀ i,0<μ i) : ∀ i j,0<momentSquare C μ i j := by
  intro i j
  rw [momentSquare,decorated_entry]
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr (hμ i)) (square_positive C hp i j))
    (Real.sqrt_pos.mpr (hμ j))

theorem momentSquare_diagonal (C : Matrix I I ℝ) (μ : I → ℝ)
    (hμ : ∀ i,0≤μ i) (i : I) : momentSquare C μ i i=μ i*(C*C) i i := by
  rw [momentSquare,decorated_entry]
  calc
    _ = (Real.sqrt (μ i)*Real.sqrt (μ i))*(C*C) i i := by ring
    _ = _ := by rw [Real.mul_self_sqrt (hμ i)]

/-- Two literal constant diagonals force every class moment to coincide.
Only the nonzero common square diagonal is needed for cancellation. -/
theorem moment_constant_of_diagonals (C : Matrix I I ℝ) (μ : I → ℝ)
    (hμ : ∀ i,0≤μ i) (r z : ℝ) (hr : r≠0)
    (hC : ∀ i,(C*C) i i=r) (hM : ∀ i,momentSquare C μ i i=z) :
    ∀ i j,μ i=μ j := by
  intro i j
  apply mul_right_cancel₀ hr
  calc
    μ i*r = momentSquare C μ i i := by rw [momentSquare_diagonal C μ hμ,hC i]
    _ = z := hM i
    _ = momentSquare C μ j j := (hM j).symm
    _ = μ j*r := by rw [momentSquare_diagonal C μ hμ,hC j]

/-- A zero-field tensor form gives a constant diagonal independently of its
chosen color chart or the strict range of the tensor parameters. -/
theorem diagonal_constant_of_reindex_tensor {q d : ℕ}
    (N : Matrix (Fin q) (Fin q) ℝ) (e : Fin q ≃ Boolean.Cube d)
    (γ : ℝ) (ρ : Fin d → ℝ)
    (hf : Matrix.reindex e e N=γ • Boolean.tensor ρ) : ∀ i,N i i=γ := by
  intro i
  have h := congrArg (fun A : Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ=>A (e i) (e i)) hf
  simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,e.symm_apply_apply,
    Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Boolean.tensor_diag,mul_one] using h

theorem diagonal_constant_of_positiveDefiniteTensorForm {q : ℕ}
    (N : Matrix (Fin q) (Fin q) ℝ)
    (hf : AlgebraicProductInterpolation.RealLanguage.PositiveDefiniteTensorForm N) :
    ∃ γ : ℝ,0<γ ∧ ∀ i,N i i=γ := by
  obtain ⟨d,e,γ,ρ,hγ,_,hform⟩ := hf
  exact ⟨γ,hγ,diagonal_constant_of_reindex_tensor N e γ ρ hform⟩

/-- Classification may use different charts for this numerical obstruction;
the same-chart source theorem below is strictly stronger than is needed here. -/
theorem moment_constant_of_tensor_forms {q : ℕ}
    (C : Matrix (Fin q) (Fin q) ℝ) (μ : Fin q → ℝ) (hμ : ∀ i,0≤μ i)
    (hC : AlgebraicProductInterpolation.RealLanguage.PositiveDefiniteTensorForm (C*C))
    (hM : AlgebraicProductInterpolation.RealLanguage.PositiveDefiniteTensorForm (momentSquare C μ)) :
    ∀ i j,μ i=μ j := by
  obtain ⟨r,hr,hCr⟩ := diagonal_constant_of_positiveDefiniteTensorForm (C*C) hC
  obtain ⟨z,_,hMz⟩ := diagonal_constant_of_positiveDefiniteTensorForm (momentSquare C μ) hM
  exact moment_constant_of_diagonals C μ hμ r z (ne_of_gt hr) hCr hMz

/-- Both classified matrices use the same available common chart and the same
original oracle. This statement does not introduce independent chart choices. -/
theorem moment_constant_in_common_chart {q : ℕ} [Nonempty (Fin q)]
    {S : Set (Matrix (Fin q) (Fin q) ℝ)} (W : ClosedMatrixFamily.CommonCubeChart S)
    (hA : ClosedMatrixFamily.AlgebraicSourceClosed S)
    (htransfer : ClosedMatrixFamily.EffectiveSpectralClosed S)
    (hgadget : ClosedMatrixFamily.MixedPlanarGadgetClosed S)
    (P : Complexity.PromiseProblem)
    (havail : ∀ N,∀ hN : N∈S,Nonempty (Complexity.PromisePolyTimeTuringReduction
      (AlgebraicProductInterpolation.RealLanguage.unitLanguage (fun _:Fin 1=>N)
        (fun _=>hA.algebraic N hN)).problem P))
    (hnot : ¬Complexity.PromisedSharpPHard P)
    (C : Matrix (Fin q) (Fin q) ℝ) (hs : C.IsHermitian) (hu : IsUnit C)
    (hpos : ∀ i j,0<C i j) (μ : Fin q→ℝ) (hμ : ∀ i,0<μ i)
    (hC : C*C∈S) (hM : momentSquare C μ∈S) : ∀ i j,μ i=μ j := by
  have hQpd := square_posDef C hs hu
  have hQpos := square_positive C hpos
  have hMpd := momentSquare_posDef C hs hu μ hμ
  have hMpos := momentSquare_positive C hpos μ hμ
  have hQconn := ClosedMatrixFamily.support_connected_of_positive_entries (C*C) hQpd.1 hQpos
  have hMconn := ClosedMatrixFamily.support_connected_of_positive_entries (momentSquare C μ) hMpd.1 hMpos
  obtain ⟨r,ρ,hr,_,_,hf⟩ := W.connected_tensor hA htransfer hgadget P havail hnot
    (C*C) ⟨hC,fun i j=>(hQpos i j).le,hQpd,hQconn⟩
  obtain ⟨z,σ,_,_,_,hg⟩ := W.connected_tensor hA htransfer hgadget P havail hnot
    (momentSquare C μ) ⟨hM,fun i j=>(hMpos i j).le,hMpd,hMconn⟩
  exact moment_constant_of_diagonals C μ (fun i=>(hμ i).le) r z (ne_of_gt hr)
    (diagonal_constant_of_reindex_tensor _ W.graphIso.toEquiv r ρ hf)
    (diagonal_constant_of_reindex_tensor _ W.graphIso.toEquiv z σ hg)

end PlanarHom.PositiveClassMomentRigidity
