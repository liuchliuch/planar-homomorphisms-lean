import PlanarHom.BooleanTensorSpectral
import PlanarHom.BooleanFieldCollision
import PlanarHom.BooleanFieldTowerReconstruction

/-! The actual tensor spectral decomposition in the fixed-dimensional radical
algebra. The inverse of a generator is obtained from its nonzero base radicand;
no field structure or independence assumption on the radical algebra occurs. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTowerSpectral
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanTensorSpectral
variable {K : Type} [Field K] {b d : ℕ}

def radical (D : ℕ→K) (i : Fin b) : Carrier D b:=linear b i 0 1

def inverseRadical (D : ℕ→K) (i : Fin b) : Carrier D b:=linear b i 0 (D i.val)⁻¹

theorem radical_sq (D : ℕ→K) (i : Fin b) : (radical D i)^2=algebraMap K (Carrier D b) (D i.val) := by
  rw [pow_two,mul_eq]
  simp [radical,mul_linear]

theorem radical_mul_inverse (D : ℕ→K) (i : Fin b) (hi:D i.val≠0) :
    radical D i*inverseRadical D i=1 := by
  rw [mul_eq]
  simp [radical,inverseRadical,mul_linear,hi]

theorem branch_eq_linear (D : ℕ→K) (c : K) (i : Fin b) (ε : Bool) :
    branch (algebraMap K (Carrier D b) c) (radical D i) ε=
      linear b i c (if ε then -1 else 1) := by
  cases ε
  · simp only [branch,Bool.false_eq_true,↓reduceIte,algebraMap_eq,radical,add_eq]
    rw [←linear_zero_im b i c,BooleanFieldCollision.add_linear]
    simp
  · simp only [branch,↓reduceIte,algebraMap_eq,radical,sub_eq,sub]
    rw [←linear_zero_im b i c,BooleanFieldCollision.neg_linear,BooleanFieldCollision.add_linear]
    simp

/-- The exact algebra matrix underlying the power queries, with one radical
per parameter class and arbitrary repetition of classes among coordinates. -/
theorem tensor_power_expansion (D : ℕ→K) (cls : Fin d→Fin b) (c a u : Fin b→K)
    (hD:∀g,D g.val=a g^2+u g^2) (hD0:∀g : Fin b,D g.val≠0) (hhalf:(2:K)≠0) (n:ℕ) :
    (tensor (fun i=>block (algebraMap K (Carrier D b) (c (cls i)))
      (algebraMap K (Carrier D b) (a (cls i)))
      (algebraMap K (Carrier D b) (u (cls i)))))^n=
    ∑ε : Fin d→Bool,
      (∏i,linear b (cls i) (c (cls i)) (if ε i then -1 else 1) : Carrier D b)^n •
        eigenprojector (fun i=>algebraMap K (Carrier D b) (a (cls i)))
          (fun i=>algebraMap K (Carrier D b) (u (cls i)))
          (fun _=>algebraMap K (Carrier D b) (1/2:K))
          (fun i=>inverseRadical D (cls i)) ε := by
  have hh:(1/2:K)+(1/2:K)=1 := by field_simp; ring
  have h:=BooleanTensorSpectral.tensor_power_expansion
    (fun i=>algebraMap K (Carrier D b) (c (cls i)))
    (fun i=>algebraMap K (Carrier D b) (a (cls i)))
    (fun i=>algebraMap K (Carrier D b) (u (cls i)))
    (fun _=>algebraMap K (Carrier D b) (1/2:K))
    (fun i=>inverseRadical D (cls i)) (fun i=>radical D (cls i))
    (fun _=>by rw [←_root_.map_add,hh,_root_.map_one])
    (fun i=>radical_mul_inverse D (cls i) (hD0 _))
    (fun i=>by rw [radical_sq,hD,_root_.map_add,_root_.map_pow,_root_.map_pow]) n
  simpa only [eigenvalue,branch_eq_linear] using h

end PlanarHom.BooleanTowerSpectral
