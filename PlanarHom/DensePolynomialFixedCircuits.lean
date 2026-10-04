import PlanarHom.DenseRationalFunctionPresentation
import PlanarHom.FixedVectorMachines

/-! Fixed finite sums/products of dense polynomials compile from actual
primitive machines. The term count here is fixed problem data, never a hidden
dynamic iteration bound. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial
open Complexity

def one : (n:ℕ)→Code n
  | 0 => 1
  | n+1 => [one n]

@[simp] theorem interpret_one (n:ℕ) : interpret n (one n)=1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CoefficientListAlgebra.polynomial [interpret n (one n)]=(1:Polynomial (Poly n))
    simp [CoefficientListAlgebra.polynomial,ih]

def fixedProduct (n:ℕ) : (m:ℕ)→(Fin m→Code n)→Code n
  | 0,_ => one n
  | m+1,f => mul n (fixedProduct n m (fun i=>f i.castSucc)) (f (Fin.last m))

theorem interpret_fixedProduct (n m:ℕ) (f:Fin m→Code n) :
    interpret n (fixedProduct n m f)=∏i,interpret n (f i) := by
  induction m with
  | zero => simp [fixedProduct]
  | succ m ih => rw [fixedProduct,interpret_mul,ih,Fin.prod_univ_castSucc]

def fixedSum (n m:ℕ) (f:Fin m→Code n) : Code n := sum n (List.ofFn f)

theorem interpret_fixedSum (n m:ℕ) (f:Fin m→Code n) :
    interpret n (fixedSum n m f)=∑i,interpret n (f i) := by
  rw [fixedSum,interpret_sum,List.map_ofFn,List.sum_ofFn]
  rfl

theorem fp_fixedProduct {A:Type} (ea:BitEncoding A) (n m:ℕ) (f:A→Fin m→Code n)
    (hf:∀i,FP ea (encoding n) (fun a=>f a i)) :
    FP ea (encoding n) (fun a=>fixedProduct n m (f a)) := by
  induction m with
  | zero => exact fp_const ea (encoding n) (one n)
  | succ m ih => exact ((ih _ (fun i=>hf i.castSucc)).pair (hf (Fin.last m))).comp (fp_mul n)

theorem fp_fixedSum {A:Type} (ea:BitEncoding A) (n m:ℕ) (f:A→Fin m→Code n)
    (hf:∀i,FP ea (encoding n) (fun a=>f a i)) :
    FP ea (encoding n) (fun a=>fixedSum n m (f a)) := by
  have hv:=FixedVectorMachines.fp_assemble ea (encoding n) m f hf
  have hl:FP ea (encoding n).list (fun a=>List.ofFn (f a)):=hv.transportOutput (fun _=>rfl)
  exact hl.comp (fp_sum n)

end PlanarHom.DensePolynomial
