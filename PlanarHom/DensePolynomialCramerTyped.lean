import PlanarHom.DensePolynomialCramer

/-! NEW dimension-stable semantics for canonical rectangular polynomial data.
This is the exact row-major interface consumed by denominator clearing. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open scoped BigOperators

 theorem replaceColumn_typed (n m:ℕ) (A:Fin m→Fin m→Code n) (b:Fin m→Code n) (k:Fin m) :
    replaceColumn n (List.ofFn (fun i=>List.ofFn (A i))) (List.ofFn b) k.val=
      List.ofFn (fun i=>List.ofFn (fun j=>if j=k then b i else A i j)) := by
  simp only [replaceColumn,List.length_ofFn,VariableDeterminant.range_map_eq_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  simp [matrixEntry,Fin.ext_iff]

 theorem solvePolynomial_typed_value (n m:ℕ) (A:Fin m→Fin m→Code n) (b:Fin m→Code n) (k:Fin m) :
    fractionValue n ((solvePolynomial n (List.ofFn (fun i=>List.ofFn (A i)),List.ofFn b))[k.val]?.getD (fractionZero n))=
      (show Matrix (Fin m) (Fin m) (RationalFunction n) from fun i j=>algebraMap (Poly n) (RationalFunction n) (interpret n (A i j))).cramer
        (fun i=>algebraMap (Poly n) (RationalFunction n) (interpret n (b i))) k /
      (show Matrix (Fin m) (Fin m) (RationalFunction n) from fun i j=>algebraMap (Poly n) (RationalFunction n) (interpret n (A i j))).det := by
  have hk:k.val<(List.ofFn (fun i=>List.ofFn (A i))).length:=by simpa using k.isLt
  rw [solvePolynomial_get n _ _ ⟨k.val,hk⟩,fractionValue,replaceColumn_typed n m A b k,
    determinantGrid_ofFn,determinantGrid_ofFn,RingHom.map_det,RingHom.map_det,Matrix.cramer_apply]
  congr 2
  ext i j
  by_cases h:j=k <;> simp [h,Matrix.map_apply]

 theorem cramer_div_correct {K I:Type*} [Field K] [Fintype I] [DecidableEq I]
    (A:Matrix I I K) (b:I→K) (h:A.det≠0) : A.mulVec (fun k=>A.cramer b k/A.det)=b := by
  have he:(fun k=>A.cramer b k/A.det)=A.det⁻¹ • A.cramer b:=by
    funext k
    simp [div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ h,one_smul]

 theorem solvePolynomial_typed_correct (n m:ℕ) (A:Fin m→Fin m→Code n) (b:Fin m→Code n)
    (h:(show Matrix (Fin m) (Fin m) (Poly n) from fun i j=>interpret n (A i j)).det≠0) :
    (show Matrix (Fin m) (Fin m) (RationalFunction n) from fun i j=>algebraMap (Poly n) (RationalFunction n) (interpret n (A i j))).mulVec
      (fun k:Fin m=>fractionValue n ((solvePolynomial n (List.ofFn (fun i=>List.ofFn (A i)),List.ofFn b))[k.val]?.getD (fractionZero n)))=
        fun i=>algebraMap (Poly n) (RationalFunction n) (interpret n (b i)) := by
  simp only [solvePolynomial_typed_value]
  apply cramer_div_correct
  have hm:=RingHom.map_det (algebraMap (Poly n) (RationalFunction n))
    (show Matrix (Fin m) (Fin m) (Poly n) from fun i j=>interpret n (A i j))
  intro hz
  exact h ((IsFractionRing.to_map_eq_zero_iff).mp (hm.trans hz))

end PlanarHom.DensePolynomial
