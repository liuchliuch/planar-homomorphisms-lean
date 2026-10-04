import PlanarHom.RectangularWalshCoordinates

/-! NEW exact double Fourier convolution for the physical parallel-square
gadget. All sums range over actual Boolean colors and preserve multiplicity. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {a b:ℕ}

abbrev DoubleIndex (a b:ℕ):=Cube a×Cube b

def pairXor (p q:DoubleIndex a b):DoubleIndex a b:=(xor p.1 q.1,xor p.2 q.2)

def pairXorEquiv (p:DoubleIndex a b):DoubleIndex a b≃DoubleIndex a b where
  toFun:=fun q=>pairXor q p
  invFun:=fun q=>pairXor q p
  left_inv:=by
    intro q
    apply Prod.ext <;> funext i <;> simp [pairXor,Boolean.xor,Bool.xor_assoc]
  right_inv:=by
    intro q
    apply Prod.ext <;> funext i <;> simp [pairXor,Boolean.xor,Bool.xor_assoc]

def doubleCharacter (p:DoubleIndex a b) (x:Cube a) (y:Cube b):ℝ:=character p.1 x*character p.2 y

theorem doubleCharacter_xor (p q:DoubleIndex a b) (x:Cube a) (y:Cube b):
    doubleCharacter (pairXor p q) x y=doubleCharacter p x y*doubleCharacter q x y:=by
  simp only [doubleCharacter,pairXor,←character_mul]
  ring

theorem doubleCharacter_square (p:DoubleIndex a b) (x:Cube a) (y:Cube b):
    doubleCharacter p x y*doubleCharacter p x y=1:=by
  unfold doubleCharacter
  calc
    _=(character p.1 x*character p.1 x)*(character p.2 y*character p.2 y):=by ring
    _=1:=by rw [character_mul_self,character_mul_self];ring

theorem physicalValues_pair_sum (C:Matrix (Cube a) (Cube b) ℝ) (x:Cube a) (y:Cube b):
    physicalValues C x y=∑p:DoubleIndex a b,C p.1 p.2*doubleCharacter p x y:=by
  rw [physicalValues_apply]
  simp only [Fintype.sum_prod_type,doubleCharacter,mul_assoc]

def coefficientConvolution (C D:Matrix (Cube a) (Cube b) ℝ):Matrix (Cube a) (Cube b) ℝ:=
  fun S T=>∑p:DoubleIndex a b,C p.1 p.2*D (xor S p.1) (xor T p.2)

theorem translated_character_sum (D:Matrix (Cube a) (Cube b) ℝ)
    (p:DoubleIndex a b) (x:Cube a) (y:Cube b):
    (∑r:DoubleIndex a b,D (xor r.1 p.1) (xor r.2 p.2)*doubleCharacter r x y)=
      doubleCharacter p x y*(∑r:DoubleIndex a b,D r.1 r.2*doubleCharacter r x y):=by
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (pairXorEquiv p)
  intro r
  change D (pairXor r p).1 (pairXor r p).2*doubleCharacter r x y=
    doubleCharacter p x y*(D (pairXor r p).1 (pairXor r p).2*doubleCharacter (pairXor r p) x y)
  rw [doubleCharacter_xor]
  calc
    _=D (pairXor r p).1 (pairXor r p).2*doubleCharacter r x y*
      (doubleCharacter p x y*doubleCharacter p x y):=by rw [doubleCharacter_square,mul_one]
    _=_:=by ring

theorem physical_convolution (C D:Matrix (Cube a) (Cube b) ℝ):
    physicalValues (coefficientConvolution C D)=fun x y=>physicalValues C x y*physicalValues D x y:=by
  funext x y
  simp only [physicalValues_pair_sum,coefficientConvolution,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑p:DoubleIndex a b,C p.1 p.2*(∑r:DoubleIndex a b,
        D (xor r.1 p.1) (xor r.2 p.2)*doubleCharacter r x y):=by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _:=by
      simp only [translated_character_sum,←mul_assoc,←Finset.sum_mul]

theorem coefficients_physical_product (C D:Matrix (Cube a) (Cube b) ℝ):
    sourceCoefficients (fun x y=>physicalValues C x y*physicalValues D x y)=coefficientConvolution C D:=by
  rw [←physical_convolution,coefficients_inversion]

def noisyCoefficients (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ):Matrix (Cube a) (Cube b) ℝ:=
  noiseDiagonal t*C

theorem noisy_physical (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ):
    physicalValues (noisyCoefficients C t)=noiseValues C t:=by
  simp only [physicalValues,noisyCoefficients,noiseValues,Matrix.mul_assoc]

theorem squaredNoise_coefficients (C:Matrix (Cube a) (Cube b) ℝ) (t:ℝ):
    sourceCoefficients (squaredNoise C t)=
      coefficientConvolution (noisyCoefficients C t) (noisyCoefficients C t):=by
  rw [←coefficients_physical_product]
  simp only [noisy_physical]
  rfl

end PlanarHom.RectangularWalshConvolution
