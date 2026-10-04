import PlanarHom.FixedRealExtensionCode
import Mathlib.LinearAlgebra.Basis.Bilinear

/-! Shared-denominator code arithmetic has the exact semantics of a genuine
finite extension of the rational-function field. The basis and its multiplication
table are fixed mathematical presentation data, not unit-cost algorithm oracles. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealExtension
open DensePolynomial
variable {n e:ℕ}

theorem add_valid (a b:Code n e) (ha:Valid n a) (hb:Valid n b) : Valid n (add n a b) := by
  change interpret n (DensePolynomial.mul n a.2 b.2)≠0
  rw [interpret_mul]
  exact mul_ne_zero ha hb

theorem neg_valid (a:Code n e) (ha:Valid n a) : Valid n (neg n a) := ha

theorem mul_valid (T:MultiplicationTable n e) (a b:Code n e) (ha:Valid n a) (hb:Valid n b) :
    Valid n (mul T a b) := by
  change interpret n (DensePolynomial.mul n (DensePolynomial.mul n a.2 b.2) T.denominator)≠0
  rw [interpret_mul,interpret_mul]
  exact mul_ne_zero (mul_ne_zero ha hb) T.valid

theorem coordinates_add (a b:Code n e) (ha:Valid n a) (hb:Valid n b) :
    coordinates n (add n a b)=coordinates n a+coordinates n b := by
  funext i
  exact fractionValue_add n (a.1 i,a.2) (b.1 i,b.2) ha hb

theorem coordinates_neg (a:Code n e) : coordinates n (neg n a)= -coordinates n a := by
  funext i
  exact fractionValue_neg n (a.1 i,a.2)

theorem coordinates_mul (T:MultiplicationTable n e) (a b:Code n e) (k:Fin e) :
    coordinates n (mul T a b) k=
      ∑i,∑j,coordinates n a i*coordinates n b j*T.value i j k := by
  simp only [coordinates,mul,MultiplicationTable.value,fractionValue,
    interpret_fixedSum,interpret_mul,map_sum,map_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

variable {K:Type} [Field K] [Algebra (RationalFunction n) K]

def value (basis:Module.Basis (Fin e) (RationalFunction n) K) (a:Code n e) : K :=
  basis.equivFun.symm (coordinates n a)

def MultiplicationTable.Realizes (T:MultiplicationTable n e)
    (basis:Module.Basis (Fin e) (RationalFunction n) K) : Prop :=
  ∀i j k,T.value i j k=basis.equivFun (basis i*basis j) k

theorem basis_multiplication_coordinates (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (x y:K) (k:Fin e) :
    basis.equivFun (x*y) k=
      ∑i,∑j,basis.equivFun x i*basis.equivFun y j*basis.equivFun (basis i*basis j) k := by
  conv_lhs => rw [←basis.sum_equivFun x,←basis.sum_equivFun y]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    smul_smul,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem value_add (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (a b:Code n e) (ha:Valid n a) (hb:Valid n b) :
    value basis (add n a b)=value basis a+value basis b := by
  rw [value,coordinates_add a b ha hb,map_add]
  rfl

theorem value_neg (basis:Module.Basis (Fin e) (RationalFunction n) K) (a:Code n e) :
    value basis (neg n a)= -value basis a := by
  rw [value,coordinates_neg,map_neg]
  rfl

theorem value_mul (T:MultiplicationTable n e)
    (basis:Module.Basis (Fin e) (RationalFunction n) K) (hT:T.Realizes basis) (a b:Code n e) :
    value basis (mul T a b)=value basis a*value basis b := by
  apply basis.equivFun.injective
  change basis.equivFun (basis.equivFun.symm (coordinates n (mul T a b)))=_
  rw [basis.equivFun.apply_symm_apply]
  funext k
  rw [coordinates_mul,basis_multiplication_coordinates]
  change ∀i j k,T.value i j k=basis.equivFun (basis i*basis j) k at hT
  simp only [value,basis.equivFun.apply_symm_apply,hT]

end PlanarHom.FixedRealExtension
