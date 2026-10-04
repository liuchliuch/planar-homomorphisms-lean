import PlanarHom.IsingCoefficientRecovery
import PlanarHom.FKTIsingCorrectness
import PlanarHom.SurfaceFKTCorrectness

/-! NEW exact positive rational samples of the actual planar and supplied-row
FKT programs, followed by literal coefficient reconstruction. Runtime claims
are made separately from these identities. -/
noncomputable section
open Classical
namespace PlanarHom.IsingRationalInterpolation
open Complexity PlanarityLRRealization

def rationalBasis:Module.Basis (Fin 1) ℚ ℚ:=Module.Basis.singleton (Fin 1) ℚ

def planarTable (g:MixedCode) : List (ℚ×ℚ) :=
  table g.edges.length (fun j=>FKTIsingMachines.value (node j) g)

def planarCoefficients (g:MixedCode) : List ℚ :=
  coefficients g.edges.length (planarTable g)

def surfaceTable (ambient:ℕ) (g:MixedCode) (rows:PlanarityRowFaceCode.Rows) : List (ℚ×ℚ) :=
  table g.edges.length (fun j=>SurfaceFKT.value ambient (node j) g rows)

def surfaceCoefficients (ambient:ℕ) (g:MixedCode) (rows:PlanarityRowFaceCode.Rows) : List ℚ :=
  coefficients g.edges.length (surfaceTable ambient g rows)

variable (g:MixedCode) {bt ut:ℕ}

theorem planar_sample (hp:g.PlanarValid bt ut) (j:ℕ) :
    FKTIsingMachines.value (node j) g=(g.toMultiGraph hp.1).isingPartitionPolynomial.eval (node j) := by
  have hpnode:1+(algebraMap ℚ ℝ) (node j)≠0:=by
    have hn:0<(algebraMap ℚ ℝ) (node j):=by
      change 0<(node j:ℝ)
      exact_mod_cast node_pos j
    exact (add_pos zero_lt_one hn).ne'
  have h:=FKTIsingMachines.value_eq_partition rationalBasis (algebraMap ℚ ℝ) hp (node j) hpnode
  exact h.trans ((g.toMultiGraph hp.1).isingPartitionPolynomial_eval (node j)).symm

theorem planar_polynomial (hp:g.PlanarValid bt ut) :
    CoefficientListAlgebra.polynomial (planarCoefficients g)=(g.toMultiGraph hp.1).isingPartitionPolynomial := by
  apply polynomial_coefficients
  · simpa only [Fintype.card_fin] using (g.toMultiGraph hp.1).isingPartitionPolynomial_natDegree
  · intro j
    exact planar_sample g hp j.val

theorem planar_coefficients (hp:g.PlanarValid bt ut) :
    planarCoefficients g=(List.range (g.edges.length+1)).map
      (g.toMultiGraph hp.1).isingPartitionPolynomial.coeff := by
  apply coefficients_eq
  · simpa only [Fintype.card_fin] using (g.toMultiGraph hp.1).isingPartitionPolynomial_natDegree
  · intro j
    exact planar_sample g hp j.val

theorem surface_sample (ambient:ℕ) (hg:g.Valid bt ut) (rows:PlanarityRowFaceCode.Rows)
    (R:RotationRows (g.toMultiGraph hg)) (hr:PlanarityRowFaceCode.Realizes g hg rows R)
    (hbound:Module.finrank (ZMod 2) R.Homology≤2*ambient) (j:ℕ) :
    SurfaceFKT.value ambient (node j) g rows=(g.toMultiGraph hg).isingPartitionPolynomial.eval (node j) := by
  have hpnode:1+(algebraMap ℚ ℝ) (node j)≠0:=by
    have hn:0<(algebraMap ℚ ℝ) (node j):=by
      change 0<(node j:ℝ)
      exact_mod_cast node_pos j
    exact (add_pos zero_lt_one hn).ne'
  have h:=SurfaceFKT.value_eq_partition rationalBasis ambient g hg rows R hr hbound
    (algebraMap ℚ ℝ) (node j) hpnode
  exact h.trans ((g.toMultiGraph hg).isingPartitionPolynomial_eval (node j)).symm

theorem surface_polynomial (ambient:ℕ) (hg:g.Valid bt ut) (rows:PlanarityRowFaceCode.Rows)
    (R:RotationRows (g.toMultiGraph hg)) (hr:PlanarityRowFaceCode.Realizes g hg rows R)
    (hbound:Module.finrank (ZMod 2) R.Homology≤2*ambient) :
    CoefficientListAlgebra.polynomial (surfaceCoefficients ambient g rows)=
      (g.toMultiGraph hg).isingPartitionPolynomial := by
  apply polynomial_coefficients
  · simpa only [Fintype.card_fin] using (g.toMultiGraph hg).isingPartitionPolynomial_natDegree
  · intro j
    exact surface_sample g ambient hg rows R hr hbound j.val

end PlanarHom.IsingRationalInterpolation
