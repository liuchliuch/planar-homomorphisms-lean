import PlanarHom.FixedExtensionSolutionProgram
import PlanarHom.FixedExtensionSystemSemantics
import PlanarHom.RationalSystemTypedAdapter

/-! Exact variable-order solution over the fixed extension. Original
nonsingularity is the only matrix promise, and every returned coordinate code
has a nonzero materialized denominator. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealExtension
open DensePolynomial
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)
variable (T:MultiplicationTable n e) (hT:T.Realizes basis)

def rationalSolution (p:System n e) (z:Fin (p.1.length*e)) : RationalFunction n :=
  fractionValue n ((DensePolynomial.solve n (expand T p))[z.val]?.getD (fractionZero n))

include hT

theorem rationalSolution_valid (p:System n e) (hv:SystemValid n e p)
    (hn:(systemMatrix basis p).det≠0) (z:Fin (p.1.length*e)) :
    FractionValid n ((DensePolynomial.solve n (expand T p))[z.val]?.getD (fractionZero n)) := by
  rw [expand_ofFn]
  exact solve_typed_valid n (p.1.length*e) (expandedMatrixCode T p) (expandedVectorCode p)
    (expandedMatrixCode_valid T p hv) (expandedVectorCode_valid p hv)
    (expandedMatrixCode_nonsingular basis T hT p hn) z

theorem rationalSolution_correct (p:System n e) (hv:SystemValid n e p)
    (hn:(systemMatrix basis p).det≠0) :
    (ExtensionCoordinateSystem.block basis (systemMatrix basis p)).mulVec
      (fun ik=>rationalSolution T p (finProdFinEquiv ik))=
        ExtensionCoordinateSystem.coordinates basis (systemVector basis p) := by
  have hs:=solve_typed_correct n (p.1.length*e) (expandedMatrixCode T p) (expandedVectorCode p)
    (expandedMatrixCode_valid T p hv) (expandedVectorCode_valid p hv)
    (expandedMatrixCode_nonsingular basis T hT p hn)
  rw [typedSystem,←expand_ofFn] at hs
  change Matrix.mulVec (fun i j=>fractionValue n (expandedMatrixCode T p i j))
    (fun k=>fractionValue n ((DensePolynomial.solve n (expand T p))[k.val]?.getD (fractionZero n)))=_ at hs
  rw [expandedMatrixCode_value basis T hT] at hs
  funext ik
  have hh:=congrFun hs (finProdFinEquiv ik)
  simp only [Matrix.mulVec,dotProduct,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_apply_apply,expandedVectorCode_value basis,Equiv.symm_apply_apply] at hh
  rw [←finProdFinEquiv.sum_comp] at hh
  simpa only [Equiv.symm_apply_apply,rationalSolution,Matrix.mulVec,dotProduct] using hh

omit hT in
theorem solve_get (p:System n e) (i:Fin p.1.length) :
    (solve T p)[i.val]?.getD (zeroCode n e)=
      packFractions n e (solutionCoordinate n e (DensePolynomial.solve n (expand T p)) i.val) := by
  rw [solve,restore,VariableDeterminant.range_map_eq_ofFn]
  simp only [List.getElem?_ofFn,i.isLt,dif_pos,Option.getD_some,Fin.eta]

theorem solve_output_valid (p:System n e) (hv:SystemValid n e p)
    (hn:(systemMatrix basis p).det≠0) (i:Fin p.1.length) :
    Valid n ((solve T p)[i.val]?.getD (zeroCode n e)) := by
  rw [solve_get]
  apply packFractions_valid
  intro k
  exact rationalSolution_valid basis T hT p hv hn (finProdFinEquiv (i,k))

theorem solve_coordinates (p:System n e) (hv:SystemValid n e p)
    (hn:(systemMatrix basis p).det≠0) (i:Fin p.1.length) (k:Fin e) :
    coordinates n ((solve T p)[i.val]?.getD (zeroCode n e)) k=
      rationalSolution T p (finProdFinEquiv (i,k)) := by
  rw [solve_get,packFractions_coordinates]
  · rfl
  · intro l
    exact rationalSolution_valid basis T hT p hv hn (finProdFinEquiv (i,l))

theorem solve_correct (p:System n e) (hv:SystemValid n e p)
    (hn:(systemMatrix basis p).det≠0) :
    (systemMatrix basis p).mulVec (fun i=>value basis ((solve T p)[i.val]?.getD (zeroCode n e)))=
      systemVector basis p := by
  apply (ExtensionCoordinateSystem.coordinates basis).injective
  rw [←ExtensionCoordinateSystem.block_mulVec]
  have hvect:ExtensionCoordinateSystem.coordinates basis
      (fun i:Fin p.1.length=>value basis ((solve T p)[i.val]?.getD (zeroCode n e)))=
      fun ik=>rationalSolution T p (finProdFinEquiv ik) := by
    funext ik
    change basis.equivFun (basis.equivFun.symm _) ik.2=_
    rw [LinearEquiv.apply_symm_apply]
    exact solve_coordinates basis T hT p hv hn ik.1 ik.2
  rw [hvect]
  exact rationalSolution_correct basis T hT p hv hn

end PlanarHom.FixedRealExtension
