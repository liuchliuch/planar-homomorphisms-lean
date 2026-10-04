import PlanarHom.DensePolynomialFixedCircuits

/-! Fixed-dimensional algebraic-extension coordinates with one shared dense
polynomial denominator. Multiplication does not multiply one denominator per
summand: it emits D_left D_right D_structure exactly once. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial

abbrev Code (n e:ℕ) := (Fin e→DensePolynomial.Code n)×DensePolynomial.Code n

def encoding (n e:ℕ) : Complexity.BitEncoding (Code n e) :=
  ((DensePolynomial.encoding n).vector e).prod (DensePolynomial.encoding n)

def Valid (n:ℕ) {e:ℕ} (a:Code n e) : Prop := interpret n a.2≠0

def coordinates (n:ℕ) {e:ℕ} (a:Code n e) : Fin e→RationalFunction n :=
  fun i=>fractionValue n (a.1 i,a.2)

structure MultiplicationTable (n e:ℕ) where
  denominator : DensePolynomial.Code n
  numerator : Fin e→Fin e→Fin e→DensePolynomial.Code n
  valid : interpret n denominator≠0

def MultiplicationTable.value {n e:ℕ} (T:MultiplicationTable n e) (i j k:Fin e) : RationalFunction n :=
  fractionValue n (T.numerator i j k,T.denominator)

def add (n:ℕ) {e:ℕ} (a b:Code n e) : Code n e :=
  (fun i=>DensePolynomial.add n (mul n (a.1 i) b.2) (mul n (b.1 i) a.2),mul n a.2 b.2)

def neg (n:ℕ) {e:ℕ} (a:Code n e) : Code n e :=
  (fun i=>DensePolynomial.neg n (a.1 i),a.2)

def mul {n e:ℕ} (T:MultiplicationTable n e) (a b:Code n e) : Code n e :=
  (fun k=>fixedSum n e (fun i=>fixedSum n e (fun j=>
    DensePolynomial.mul n (DensePolynomial.mul n (a.1 i) (b.1 j)) (T.numerator i j k))),
    DensePolynomial.mul n (DensePolynomial.mul n a.2 b.2) T.denominator)

end PlanarHom.FixedRealExtension
