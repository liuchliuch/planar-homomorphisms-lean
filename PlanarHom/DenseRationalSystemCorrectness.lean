import PlanarHom.DenseRationalSystemProgram
import PlanarHom.DensePolynomialCramerTyped

/-! NEW exact correctness of the concrete denominator-cleared variable-order
solver. The only algebraic promise is valid input representatives and a
nonsingular original matrix; loops over all coordinates are actual programs. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial

 def SystemValid (n:ℕ) (p:System n) : Prop :=
    (∀row∈p.1,∀a∈row,FractionValid n a) ∧ ∀b∈p.2,FractionValid n b
 def systemMatrix (n:ℕ) (p:System n) : Matrix (Fin p.1.length) (Fin p.1.length) (RationalFunction n) :=
    fun i j=>fractionValue n (systemEntry n p i.val j.val)
 def systemVector (n:ℕ) (p:System n) : Fin p.1.length→RationalFunction n :=
    fun i=>fractionValue n (systemRhs n p i.val)
 def clearedMatrix (n:ℕ) (p:System n) : Fin p.1.length→Fin p.1.length→Code n :=
    fun i j=>clearNumerator n (rowFractions n p i.val) j.val
 def clearedVector (n:ℕ) (p:System n) : Fin p.1.length→Code n :=
    fun i=>clearNumerator n (rowFractions n p i.val) p.1.length
 def rowScale (n:ℕ) (p:System n) (i:Fin p.1.length) : RationalFunction n :=
    algebraMap (Poly n) (RationalFunction n) (interpret n (commonDenominator n (rowFractions n p i.val)))

 theorem fractionLookup_valid (n:ℕ) (xs:List (FractionCode n)) (k:ℕ)
    (h:∀a∈xs,FractionValid n a) : FractionValid n (xs[k]?.getD (fractionZero n)) := by
  cases he:xs[k]? with
  | none=>simpa [he] using fractionZero_valid n
  | some a=>exact h a (List.mem_of_getElem? he)

 theorem systemEntry_valid (n:ℕ) (p:System n) (h:SystemValid n p) (i j:ℕ) :
    FractionValid n (systemEntry n p i j) := by
  apply fractionLookup_valid
  intro a ha
  cases he:p.1[i]? with
  | none=>simp [he] at ha
  | some row=>exact h.1 row (List.mem_of_getElem? he) a (by simpa [he] using ha)

 theorem systemRhs_valid (n:ℕ) (p:System n) (h:SystemValid n p) (i:ℕ) :
    FractionValid n (systemRhs n p i) := fractionLookup_valid n p.2 i h.2

 theorem rowFractions_valid (n:ℕ) (p:System n) (h:SystemValid n p) (i:ℕ) :
    ∀a∈rowFractions n p i,FractionValid n a := by
  intro a ha
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
  split_ifs
  · exact systemRhs_valid n p h i
  · exact systemEntry_valid n p h i j

 theorem rowFractions_ofFn (n:ℕ) (p:System n) (i:ℕ) :
    rowFractions n p i=List.ofFn (fun j:Fin (p.1.length+1)=>
      if j.val=p.1.length then systemRhs n p i else systemEntry n p i j.val) :=
    VariableDeterminant.range_map_eq_ofFn _ _

 theorem rowScale_ne_zero (n:ℕ) (p:System n) (h:SystemValid n p) (i:Fin p.1.length) :
    rowScale n p i≠0 := by
  exact fun hz=>commonDenominator_valid n _ (rowFractions_valid n p h i.val)
    ((IsFractionRing.to_map_eq_zero_iff).mp hz)

 theorem clearedMatrix_value (n:ℕ) (p:System n) (h:SystemValid n p) (i j:Fin p.1.length) :
    algebraMap (Poly n) (RationalFunction n) (interpret n (clearedMatrix n p i j))=
      rowScale n p i*systemMatrix n p i j := by
  let xs:=fun k:Fin (p.1.length+1)=>
    if k.val=p.1.length then systemRhs n p i.val else systemEntry n p i.val k.val
  have hk:¬j.val=p.1.length:=Nat.ne_of_lt j.isLt
  have hv:FractionValid n (xs j.castSucc):=by
    simpa only [xs,Fin.coe_castSucc,if_neg hk] using systemEntry_valid n p h i.val j.val
  have hh:=clearNumerator_value n xs j.castSucc hv
  simpa only [xs,Fin.coe_castSucc,if_neg hk,←rowFractions_ofFn,
    clearedMatrix,rowScale,systemMatrix] using hh

 theorem clearedVector_value (n:ℕ) (p:System n) (h:SystemValid n p) (i:Fin p.1.length) :
    algebraMap (Poly n) (RationalFunction n) (interpret n (clearedVector n p i))=
      rowScale n p i*systemVector n p i := by
  let xs:=fun k:Fin (p.1.length+1)=>
    if k.val=p.1.length then systemRhs n p i.val else systemEntry n p i.val k.val
  have hv:FractionValid n (xs (Fin.last p.1.length)):=by
    simpa only [xs,Fin.val_last,ite_true] using systemRhs_valid n p h i.val
  have hh:=clearNumerator_value n xs (Fin.last p.1.length) hv
  simpa only [xs,Fin.val_last,ite_true,←rowFractions_ofFn,
    clearedVector,rowScale,systemVector] using hh

 theorem clearedSystem_ofFn (n:ℕ) (p:System n) : clearedSystem n p=
    (List.ofFn (fun i=>List.ofFn (clearedMatrix n p i)),List.ofFn (clearedVector n p)) := by
  simp only [clearedSystem,VariableDeterminant.range_map_eq_ofFn]
  rfl

 theorem cleared_determinant_ne_zero (n:ℕ) (p:System n) (hv:SystemValid n p)
    (h:(systemMatrix n p).det≠0) :
    (show Matrix (Fin p.1.length) (Fin p.1.length) (Poly n) from fun i j=>interpret n (clearedMatrix n p i j)).det≠0 := by
  let A:Matrix (Fin p.1.length) (Fin p.1.length) (Poly n):=fun i j=>interpret n (clearedMatrix n p i j)
  have hm:((algebraMap (Poly n) (RationalFunction n)).mapMatrix A)=
      Matrix.of (fun i j=>rowScale n p i*systemMatrix n p i j) := by
    ext i j
    exact clearedMatrix_value n p hv i j
  have hd:=RingHom.map_det (algebraMap (Poly n) (RationalFunction n)) A
  rw [hm,Matrix.det_mul_column] at hd
  have hn:(∏i,rowScale n p i)*(systemMatrix n p).det≠0:=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _=>rowScale_ne_zero n p hv i)) h
  intro hz
  change A.det=0 at hz
  exact hn (hd.symm.trans ((congrArg (algebraMap (Poly n) (RationalFunction n)) hz).trans (map_zero _)))

 theorem solve_length (n:ℕ) (p:System n) : (solve n p).length=p.1.length := by
  simp [solve,solvePolynomial_length,clearedSystem]

 theorem solve_correct (n:ℕ) (p:System n) (hv:SystemValid n p)
    (h:(systemMatrix n p).det≠0) :
    (systemMatrix n p).mulVec (fun k=>fractionValue n ((solve n p)[k.val]?.getD (fractionZero n)))=
      systemVector n p := by
  have hs:=solvePolynomial_typed_correct n p.1.length (clearedMatrix n p) (clearedVector n p)
    (cleared_determinant_ne_zero n p hv h)
  rw [←clearedSystem_ofFn] at hs
  change (show Matrix (Fin p.1.length) (Fin p.1.length) (RationalFunction n) from
    fun i j=>algebraMap (Poly n) (RationalFunction n) (interpret n (clearedMatrix n p i j))).mulVec
      (fun k=>fractionValue n ((solve n p)[k.val]?.getD (fractionZero n)))=_ at hs
  funext i
  have hi:=congrFun hs i
  simp only [Matrix.mulVec,dotProduct,clearedMatrix_value n p hv,clearedVector_value n p hv,
    mul_assoc,←Finset.mul_sum] at hi
  exact mul_left_cancel₀ (rowScale_ne_zero n p hv i) hi

 theorem solve_output_valid (n:ℕ) (p:System n) (hv:SystemValid n p)
    (h:(systemMatrix n p).det≠0) (k:Fin p.1.length) :
    FractionValid n ((solve n p)[k.val]?.getD (fractionZero n)) := by
  rw [solve,clearedSystem_ofFn]
  have hk:k.val<(List.ofFn (fun i=>List.ofFn (clearedMatrix n p i))).length:=by simpa using k.isLt
  rw [solvePolynomial_get n _ _ ⟨k.val,hk⟩]
  change interpret n (determinantGrid n (List.ofFn (fun i=>List.ofFn (clearedMatrix n p i))))≠0
  rw [determinantGrid_ofFn]
  exact cleared_determinant_ne_zero n p hv h

end PlanarHom.DensePolynomial
