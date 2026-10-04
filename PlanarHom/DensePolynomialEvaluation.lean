import PlanarHom.DenseRationalFunctionSemantics
import PlanarHom.DensePolynomialArithmeticMachines
import PlanarHom.RuntimePolynomialEvaluationMachines

/-! NEW exact rational scalar maps and rational-point evaluation of the fixed
variable dense polynomial representation. All operations retain concrete codes. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity

def qHom : (n:ℕ)→ℚ→+*Poly n
  | 0=>RingHom.id ℚ
  | n+1=>Polynomial.C.comp (qHom n)

def scalar : (n:ℕ)→ℚ→Code n→Code n
  | 0,q,p=>q*p
  | n+1,q,p=>p.map (scalar n q)

def evalHom : (n:ℕ)→List ℚ→(Poly n→+*ℚ)
  | 0,_=>RingHom.id ℚ
  | n+1,point=>Polynomial.eval₂RingHom (evalHom n point.tail) (point.headD 0)

def evaluate : (n:ℕ)→Code n→List ℚ→ℚ
  | 0,p,_=>p
  | n+1,p,point=>CoefficientListAlgebra.evaluate (point.headD 0)
      (p.map (fun a=>evaluate n a point.tail))

 theorem polynomial_map_mul {R:Type} [CommRing R] (c:R) (xs:List R) :
    CoefficientListAlgebra.polynomial (xs.map (fun x=>c*x))=
      Polynomial.C c*CoefficientListAlgebra.polynomial xs := by
  induction xs with
  | nil=>simp [CoefficientListAlgebra.polynomial]
  | cons a xs ih=>
    simp only [List.map_cons,CoefficientListAlgebra.polynomial,ih,Polynomial.C_mul]
    ring

 theorem interpret_scalar (n:ℕ) (q:ℚ) (p:Code n) :
    interpret n (scalar n q p)=qHom n q*interpret n p := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [scalar,interpret,List.map_map,Function.comp_def,ih]
    simpa only [List.map_map,Function.comp_def,qHom,RingHom.comp_apply] using
      polynomial_map_mul (qHom n q) (p.map (interpret n))

 theorem evaluate_semantics (n:ℕ) (p:Code n) (point:List ℚ) :
    evaluate n p point=evalHom n point (interpret n p) := by
  induction n generalizing point with
  | zero=>rfl
  | succ n ih=>
    induction p with
    | nil=>simp [evaluate,interpret,CoefficientListAlgebra.polynomial,evalHom]
    | cons a p hp=>
      have ht : CoefficientListAlgebra.evaluate (point.headD 0)
          (p.map (fun a=>evaluate n a point.tail))=
          (Polynomial.eval₂RingHom (evalHom n point.tail) (point.headD 0))
            (CoefficientListAlgebra.polynomial (p.map (interpret n))) := hp
      simp only [evaluate,List.map_cons,CoefficientListAlgebra.evaluate_cons,interpret,
        CoefficientListAlgebra.polynomial,evalHom,map_add,map_mul]
      rw [ht,ih a point.tail]
      change _ = Polynomial.eval₂ (evalHom n point.tail) (point.headD 0) (Polynomial.C (interpret n a)) +
        Polynomial.eval₂ (evalHom n point.tail) (point.headD 0) Polynomial.X * _
      rw [Polynomial.eval₂_C,Polynomial.eval₂_X]
      rfl

 theorem evalHom_qHom (n:ℕ) (point:List ℚ) (q:ℚ) : evalHom n point (qHom n q)=q := by
  induction n generalizing point with
  | zero=>rfl
  | succ n ih=>
    change Polynomial.eval₂ (evalHom n point.tail) (point.headD 0) (Polynomial.C (qHom n q))=q
    rw [Polynomial.eval₂_C]
    exact ih point.tail

end PlanarHom.DensePolynomial
