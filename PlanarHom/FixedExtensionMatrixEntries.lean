import PlanarHom.FixedRealExtensionPresentation
import PlanarHom.DenseDenominatorClearing
import PlanarHom.ExtensionCoordinateSystem

/-! Exact code materialization of the fixed-extension block entries. The
extension degree is fixed; matrix order remains dynamic in the next layer. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines
variable {n e:ℕ}

def zeroCode (n e:ℕ) : Code n e := (fun _=>DensePolynomial.zero n,DensePolynomial.one n)

theorem zeroCode_valid (n e:ℕ) : Valid n (zeroCode n e) := by
  change interpret n (DensePolynomial.one n)≠0
  rw [interpret_one]
  exact one_ne_zero

theorem zeroCode_value {K:Type} [Field K] [Algebra (RationalFunction n) K]
    (basis:Module.Basis (Fin e) (RationalFunction n) K) : value basis (zeroCode n e)=0 := by
  apply basis.equivFun.injective
  simp only [value,LinearEquiv.apply_symm_apply,map_zero]
  funext i
  simp [coordinates,zeroCode,fractionValue]

def blockEntry (T:MultiplicationTable n e) (a:Code n e) (k l:Fin e) : FractionCode n :=
  (fixedSum n e (fun j=>DensePolynomial.mul n (a.1 j) (T.numerator j l k)),
    DensePolynomial.mul n a.2 T.denominator)

theorem blockEntry_valid (T:MultiplicationTable n e) (a:Code n e) (ha:Valid n a) (k l:Fin e) :
    FractionValid n (blockEntry T a k l) := by
  change interpret n (DensePolynomial.mul n a.2 T.denominator)≠0
  rw [interpret_mul]
  exact mul_ne_zero ha T.valid

theorem blockEntry_coordinates (T:MultiplicationTable n e) (a:Code n e) (k l:Fin e) :
    fractionValue n (blockEntry T a k l)=∑j,coordinates n a j*T.value j l k := by
  simp only [blockEntry,fractionValue,interpret_fixedSum,interpret_mul,map_sum,map_mul,
    Finset.sum_div,coordinates,MultiplicationTable.value]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem blockEntry_value {K:Type} [Field K] [Algebra (RationalFunction n) K]
    (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (T:MultiplicationTable n e) (hT:T.Realizes basis) (a:Code n e) (k l:Fin e) :
    fractionValue n (blockEntry T a k l)=basis.equivFun (value basis a*basis l) k := by
  rw [blockEntry_coordinates,basis_multiplication_coordinates]
  change ∀i j k,T.value i j k=basis.equivFun (basis i*basis j) k at hT
  simp only [value,LinearEquiv.apply_symm_apply,hT,Module.Basis.equivFun_self]
  simp

theorem fp_blockEntry (T:MultiplicationTable n e) (k l:Fin e) :
    FP (encoding n e) (fractionEncoding n) (fun a=>blockEntry T a k l) := by
  let ep:=DensePolynomial.encoding n
  let ec:=encoding n e
  have hn:FP ec ep (fun a=>fixedSum n e (fun j=>DensePolynomial.mul n (a.1 j) (T.numerator j l k))) := by
    apply fp_fixedSum
    intro j
    have ha:=(fp_fst (ep.vector e) ep).comp (FixedVectorMachines.fp_coordinate ep e j)
    exact (ha.pair (fp_const ec ep (T.numerator j l k))).comp (DensePolynomial.fp_mul n)
  have hd:=((fp_snd (ep.vector e) ep).pair (fp_const ec ep T.denominator)).comp (DensePolynomial.fp_mul n)
  exact hn.pair hd

def packFractions (n e:ℕ) (a:Fin e→FractionCode n) : Code n e :=
  (fun k=>clearNumerator n (List.ofFn a) k.val,commonDenominator n (List.ofFn a))

theorem packFractions_valid (a:Fin e→FractionCode n) (ha:∀i,FractionValid n (a i)) :
    Valid n (packFractions n e a) := by
  apply commonDenominator_valid
  intro x hx
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
  exact ha i

theorem packFractions_coordinates (a:Fin e→FractionCode n) (ha:∀i,FractionValid n (a i)) :
    coordinates n (packFractions n e a)=fun k=>fractionValue n (a k) := by
  funext k
  change algebraMap (Poly n) (RationalFunction n) (interpret n (clearNumerator n (List.ofFn a) k.val)) /
    algebraMap (Poly n) (RationalFunction n) (interpret n (commonDenominator n (List.ofFn a)))=_
  rw [clearNumerator_value n a k (ha k)]
  have hd:algebraMap (Poly n) (RationalFunction n) (interpret n (commonDenominator n (List.ofFn a)))≠0 :=
    fun h=>(packFractions_valid a ha) ((IsFractionRing.to_map_eq_zero_iff).mp h)
  exact mul_div_cancel_left₀ _ hd

theorem fp_packFractions (n e:ℕ) :
    FP ((fractionEncoding n).vector e) (encoding n e) (packFractions n e) := by
  let ef:=fractionEncoding n
  have hl:FP (ef.vector e) ef.list List.ofFn:=fp_code_view _ _ _ (fun _=>rfl)
  have hn:FP (ef.vector e) ((DensePolynomial.encoding n).vector e) (fun a k=>clearNumerator n (List.ofFn a) k.val) := by
    apply FixedVectorMachines.fp_assemble
    intro k
    exact ((fp_const (ef.vector e) BitEncoding.nat k.val).pair hl).comp (fp_clearNumerator n)
  exact hn.pair (hl.comp (fp_commonDenominator n))

end PlanarHom.FixedRealExtension
