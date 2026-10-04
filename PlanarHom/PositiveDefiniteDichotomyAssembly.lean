import PlanarHom.OrdinaryClosedFamilySource

/-! NEW source necessity for connected nonnegative positive-definite matrices.
The closed family has an actual ordinary-source compiler. Only the independent
all-size Potts hardness foundation remains; biased Boolean hardness is proved. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity ClosedMatrixFamily LogarithmicSupport Boolean
variable {q : ℕ}

def PositiveDefiniteTensorForm (M : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  ∃ d : ℕ, ∃ e : Fin q ≃ Cube d, ∃ γ : ℝ, ∃ ρ : Fin d → ℝ,
    0 < γ ∧ (∀ i, 0 < ρ i ∧ ρ i < 1) ∧ Matrix.reindex e e M = γ • tensor ρ

theorem positiveDefiniteTensorForm_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hpd : (L.matrices 0).PosDef) (hnn : ∀i j,0≤L.matrices 0 i j)
    (hconn : (offDiagonalSupport (L.matrices 0) hpd.1).Connected)
    (hnot : ¬PromisedSharpPHard L.problem) : PositiveDefiniteTensorForm (L.matrices 0) := by
  have hadm : Admissible L.ordinaryFamily (L.matrices 0) :=
    ⟨L.ordinaryFamily_generator hpd.1,hnn,hpd,hconn⟩
  obtain ⟨W⟩ := L.ordinaryFamily_common_chart hPotts hunit ⟨_,hadm⟩ hnot
  obtain ⟨γ,ρ,hγ,hγalg,hρ,he⟩ := W.connected_tensor L.ordinaryFamily_algebraic
    L.ordinaryFamily_effective L.ordinaryFamily_gadgets L.problem
    (fun N hN=>⟨L.ordinaryFamily_source hunit N hN⟩) hnot _ hadm
  exact ⟨W.dimension,W.graphIso.toEquiv,γ,ρ,hγ,fun i=>⟨(hρ i).1,(hρ i).2.1⟩,he⟩

theorem positiveDefinite_diagonal_constant_of_not_hard (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hpd : (L.matrices 0).PosDef) (hnn : ∀i j,0≤L.matrices 0 i j)
    (hconn : (offDiagonalSupport (L.matrices 0) hpd.1).Connected)
    (hnot : ¬PromisedSharpPHard L.problem) : ∀i j,L.matrices 0 i i=L.matrices 0 j j := by
  obtain ⟨d,e,γ,ρ,hγ,hρ,he⟩ := L.positiveDefiniteTensorForm_of_not_hard
    hPotts hunit hpd hnn hconn hnot
  have hd (i : Fin q) : L.matrices 0 i i=γ := by
    have h := congrFun (congrFun he (e i)) (e i)
    simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
      Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,tensor_diag,mul_one] using h
  exact fun i j => (hd i).trans (hd j).symm

theorem positive_nonconstant_diagonal_hard_of_potts (hPotts : PositivePottsFoundation)
    (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hpd : (L.matrices 0).PosDef) (hpos : ∀i j,0<L.matrices 0 i j)
    (hnon : ∃i j,L.matrices 0 i i≠L.matrices 0 j j) : PromisedSharpPHard L.problem := by
  letI : Nonempty (Fin q) := ⟨hnon.choose⟩
  by_contra hnot
  obtain ⟨i,j,hij⟩ := hnon
  exact hij (L.positiveDefinite_diagonal_constant_of_not_hard hPotts hunit hpd
    (fun i j=>(hpos i j).le) (support_connected_of_positive_entries _ hpd.1 hpos) hnot i j)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
