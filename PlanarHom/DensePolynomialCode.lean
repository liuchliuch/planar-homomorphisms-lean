import PlanarHom.DensePolynomialWidthMachines
import PlanarHom.CoefficientConvolutionMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.FixedFieldArithmeticMachines

/-! Fixed-variable dense polynomial codes. Every axis is a dynamic coefficient
list, with explicit trailing zeros permitted. The variable count is fixed,
while degrees and rational coefficient bit lengths are genuine input data. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity

abbrev Code : ℕ→Type
  | 0 => ℚ
  | n+1 => List (Code n)

def zero : (n:ℕ)→Code n
  | 0 => 0
  | n+1 => []

def rationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ

def encoding : (n:ℕ)→BitEncoding (Code n)
  | 0 => numberFieldEncoding rationalBasis
  | n+1 => (encoding n).list

def gather {A : Type} (z : A) (k : ℕ) (xs : List (List A)) : List A :=
  xs.map (fun p=>p[k]?.getD z)

def sum : (n:ℕ)→List (Code n)→Code n
  | 0,xs => xs.sum
  | n+1,xs => (List.range (width xs)).map (fun k=>sum n (gather (zero n) k xs))

def mul : (n:ℕ)→Code n→Code n→Code n
  | 0,a,b => a*b
  | n+1,a,b => CoefficientConvolutionMachines.convolution (zero n)
      (fun _ : ℕ=>mul n) (fun _ : ℕ=>sum n) (0,(a,b))

def neg : (n:ℕ)→Code n→Code n
  | 0,a => -a
  | n+1,a => a.map (neg n)

def add (n:ℕ) (a b:Code n) : Code n := sum n [a,b]

def isZero : (n:ℕ)→Code n→Bool
  | 0,a => decide (a=0)
  | n+1,a => !(a.any (fun p=>!(isZero n p)))

/-- Exact rational-function codes do not require gcd normalization for field
operations and equality: cross products are compared by polynomial identity. -/
def FractionCode (n:ℕ) := Code n×Code n

def fractionEncoding (n:ℕ) : BitEncoding (FractionCode n) := (encoding n).prod (encoding n)

def fractionMul (n:ℕ) (a b:FractionCode n) : FractionCode n :=
  (mul n a.1 b.1,mul n a.2 b.2)

def fractionAdd (n:ℕ) (a b:FractionCode n) : FractionCode n :=
  (add n (mul n a.1 b.2) (mul n b.1 a.2),mul n a.2 b.2)

def fractionNeg (n:ℕ) (a:FractionCode n) : FractionCode n := (neg n a.1,a.2)
def fractionInv (n:ℕ) (a:FractionCode n) : FractionCode n := (a.2,a.1)

def fractionEq (n:ℕ) (a b:FractionCode n) : Bool :=
  isZero n (add n (mul n a.1 b.2) (neg n (mul n b.1 a.2)))

end PlanarHom.DensePolynomial
