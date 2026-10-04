import PlanarHom.FixedRealListProductProgram
import PlanarHom.BidiagonalProductSystem

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealListProduct
open DensePolynomial Complexity FixedRealExtension
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def orderEquiv (xs:List (Code n e)) : Fin (program basis xs).1.length ≃ Fin (xs.length+1) :=
  finCongr (program_order basis xs)

theorem program_entry (xs:List (Code n e)) (i j:ℕ) (hi:i<xs.length+1) (hj:j<xs.length+1) :
    FixedRealExtension.systemEntry n e (program basis xs) i j=entry basis xs i j := by
  simp [FixedRealExtension.systemEntry,program,List.getElem?_map,List.getElem?_range,hi,hj]

theorem program_rhs (xs:List (Code n e)) (i:ℕ) (hi:i<xs.length+1) :
    FixedRealExtension.systemRhs n e (program basis xs) i=if i=0 then one basis else zeroCode n e := by
  simp [FixedRealExtension.systemRhs,program,List.getElem?_map,List.getElem?_range,hi]

theorem matrix_reindex (xs:List (Code n e)) :
    Matrix.reindex (orderEquiv basis xs) (orderEquiv basis xs) (systemMatrix basis (program basis xs))=
      BidiagonalProductSystem.matrix (fun j=>value basis (xs[j]?.getD (zeroCode n e))) xs.length := by
  ext i j
  change value basis (FixedRealExtension.systemEntry n e (program basis xs) i.val j.val)=_
  rw [program_entry basis xs i.val j.val i.isLt j.isLt]
  by_cases h:i=j
  · subst j
    simp only [entry,ite_true,BidiagonalProductSystem.matrix,one_value]
  · have hv:i.val≠j.val:=fun he=>h (Fin.ext he)
    by_cases hs:i.val=j.val+1
    · simp only [entry,if_neg hv,if_pos hs,negative_value,BidiagonalProductSystem.matrix,if_neg h]
    · simp only [entry,if_neg hv,if_neg hs,zeroCode_value,BidiagonalProductSystem.matrix,if_neg h]

theorem determinant_one (xs:List (Code n e)) : (systemMatrix basis (program basis xs)).det=1 := by
  rw [←Matrix.det_reindex_self (orderEquiv basis xs),matrix_reindex,BidiagonalProductSystem.matrix_det]

theorem product_valid (xs:List (Code n e)) (h:∀x∈xs,Valid n x) : Valid n (product basis xs) := by
  have hv:=program_valid basis xs h
  have hn:(systemMatrix basis (program basis xs)).det≠0:=by rw [determinant_one]; exact one_ne_zero
  exact solve_output_valid basis _ (multiplicationTable_realizes basis) _ hv hn
    ((orderEquiv basis xs).symm (Fin.last xs.length))

theorem product_value (xs:List (Code n e)) (h:∀x∈xs,Valid n x) :
    value basis (product basis xs)=(xs.map (value basis)).prod := by
  have hv:=program_valid basis xs h
  have hn:(systemMatrix basis (program basis xs)).det≠0:=by rw [determinant_one]; exact one_ne_zero
  have hs:=solve_correct basis _ (multiplicationTable_realizes basis) _ hv hn
  let z:Fin (xs.length+1)→K:=fun i=>value basis
    ((solve (multiplicationTable basis) (program basis xs))[i.val]?.getD (zeroCode n e))
  have hx:(BidiagonalProductSystem.matrix (fun j=>value basis (xs[j]?.getD (zeroCode n e))) xs.length).mulVec z=
      BidiagonalProductSystem.vector xs.length := by
    funext i
    have hh:=congrFun hs ((orderEquiv basis xs).symm i)
    simp only [Matrix.mulVec,dotProduct] at hh
    rw [←(orderEquiv basis xs).symm.sum_comp] at hh
    have hm:=congrFun (congrFun (matrix_reindex basis xs) i)
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply] at hm
    simp only [hm] at hh
    change (∑j,BidiagonalProductSystem.matrix _ _ i j*z j)=_
    have hz:∀j:Fin (xs.length+1),value basis
        ((solve (multiplicationTable basis) (program basis xs))[((orderEquiv basis xs).symm j).val]?.getD (zeroCode n e))=z j:=fun _=>rfl
    simp only [hz] at hh
    rw [hh]
    change value basis (FixedRealExtension.systemRhs n e (program basis xs) i.val)=_
    rw [program_rhs basis xs i.val i.isLt]
    change value basis (if i.val=0 then one basis else zeroCode n e)=if i.val=0 then 1 else 0
    by_cases hi:i.val=0
    · rw [if_pos hi,if_pos hi,one_value]
    · rw [if_neg hi,if_neg hi,zeroCode_value]
  have hl:=BidiagonalProductSystem.solution_last _ _ z hx
  change value basis (product basis xs)=_ at hl
  refine hl.trans ?_
  apply congrArg List.prod
  rw [RepresentedInterpolationMatrices.range_map_ofFn]
  have hcode:(List.ofFn (fun i:Fin xs.length=>value basis (xs[i.val]?.getD (zeroCode n e))))=
      xs.map (value basis) := by
    calc
      _=List.ofFn (fun i:Fin xs.length=>value basis xs[i.val]):=by
        apply congrArg List.ofFn
        funext i
        rw [List.getElem?_eq_getElem i.isLt]
        rfl
      _=xs.map (value basis):=List.ofFn_getElem_eq_map xs (value basis)
  exact hcode

/-- Arbitrary lexical representatives are normalized by an actual machine; all
valid code lists, including empty lists and zero factors, are accepted. -/
def productProblem : RepresentedBit.Problem :=
  (presentation basis).problem (encoding n e).list (fun xs=>∀x∈xs,Valid n x)
    (fun xs=>(xs.map (value basis)).prod)

theorem product_inFP : (productProblem basis).InFP :=
  (presentation basis).problem_inFP _ (BitEncoding.listNormalizer (normalizer n e)) _ _
    (product basis) (fp_product basis) (product_valid basis) (product_value basis)

end PlanarHom.FixedRealListProduct
