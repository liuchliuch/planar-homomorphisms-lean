import PlanarHom.IsingPartitionPolynomial
import PlanarHom.MaterializedPolynomialCoefficientMachines
import PlanarHom.CoefficientListAlgebra

/-! NEW positive rational sample grid and literal coefficient reconstruction.
The construction is total even on malformed sample tables; correctness uses
only the proved sample values and the degree bound, not a runtime oracle. -/
namespace PlanarHom.IsingRationalInterpolation
open scoped Polynomial

def node (j:ℕ) : ℚ := (j:ℚ)+1

def table (D:ℕ) (values:ℕ→ℚ) : List (ℚ×ℚ) :=
  (List.range (D+1)).map (fun j=>(node j,values j))

def coefficients (D:ℕ) (samples:List (ℚ×ℚ)) : List ℚ :=
  (List.range (D+1)).map (fun k=>MaterializedPolynomialCoefficientMachines.recover (k,samples))

theorem node_pos (j:ℕ) : 0<node j := by unfold node; positivity

theorem node_injective : Function.Injective node := by
  intro i j h
  have hh:(i:ℚ)=(j:ℚ):=add_right_cancel h
  exact_mod_cast hh

theorem table_eq_ofFn (D:ℕ) (values:ℕ→ℚ) :
    table D values=List.ofFn (fun j:Fin (D+1)=>(node j.val,values j.val)) := by
  rw [List.ofFn_eq_map]
  rw [table,←List.map_coe_finRange (D+1),List.map_map]
  rfl

theorem recover_coeff (D k:ℕ) (values:ℕ→ℚ) (P:Polynomial ℚ) (hP:P.natDegree≤D)
    (hvalues:∀j:Fin (D+1),values j.val=P.eval (node j.val)) :
    MaterializedPolynomialCoefficientMachines.recover (k,table D values)=P.coeff k := by
  rw [table_eq_ofFn]
  apply MaterializedPolynomialCoefficientMachines.recover_ofFn_eq_coeff k
    (fun j:Fin (D+1)=>node j.val) _ (node_injective.comp Fin.val_injective) P
  · exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hP)
  · exact hvalues

theorem coefficients_eq (D:ℕ) (values:ℕ→ℚ) (P:Polynomial ℚ) (hP:P.natDegree≤D)
    (hvalues:∀j:Fin (D+1),values j.val=P.eval (node j.val)) :
    coefficients D (table D values)=(List.range (D+1)).map P.coeff := by
  unfold coefficients
  apply List.map_congr_left
  intro k hk
  exact recover_coeff D k values P hP hvalues

theorem coefficients_length (D:ℕ) (samples:List (ℚ×ℚ)) :
    (coefficients D samples).length=D+1 := by simp [coefficients]

theorem polynomial_coeff (cs:List ℚ) (k:ℕ) :
    (CoefficientListAlgebra.polynomial cs).coeff k=cs[k]?.getD 0 := by
  induction cs generalizing k with
  | nil=>simp [CoefficientListAlgebra.polynomial]
  | cons c cs ih=>cases k <;> simp [CoefficientListAlgebra.polynomial,Polynomial.coeff_add,ih]

theorem polynomial_coefficients (D:ℕ) (values:ℕ→ℚ) (P:Polynomial ℚ) (hP:P.natDegree≤D)
    (hvalues:∀j:Fin (D+1),values j.val=P.eval (node j.val)) :
    CoefficientListAlgebra.polynomial (coefficients D (table D values))=P := by
  rw [coefficients_eq D values P hP hvalues]
  apply Polynomial.ext
  intro k
  rw [polynomial_coeff]
  by_cases hk:k<D+1
  · simp [List.getElem?_map,List.getElem?_range hk]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk),Option.getD_none]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

end PlanarHom.IsingRationalInterpolation
