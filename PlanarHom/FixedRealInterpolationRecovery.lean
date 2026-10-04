import PlanarHom.FixedRealRootRestriction
import PlanarHom.FixedRealInterpolationProducts
import PlanarHom.RepresentedInterpolationMatrixSemantics
import PlanarHom.FixedExtensionSystemRepresented

/-! Actual represented interpolation recovery via the concrete fixed-extension
linear solver. Every oracle reply is allowed its own valid representative. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealInterpolationRecovery
open DensePolynomial Complexity RepresentedBit RepresentedPowerTable FixedRealExtension
open RepresentedInterpolationMatrices RepresentedInterpolation PairProjectionMachines
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K) (A:Fin t→K)

abbrev Rows := List (Row (presentation basis) t)
def inputEncoding : BitEncoding (Rows basis (t:=t)×List (Code n e)) :=
  (RepresentedPowerTable.encoding (presentation basis) t).list.prod (encoding n e).list

def preparedSystem (p:Rows basis (t:=t)×List (Code n e)) : System n e :=
  system (presentation basis) (FixedRealRootRestriction.arithmetic basis)
    (FixedRealInterpolationProducts.wordProductMachine basis A) p

def recover (p:Rows basis (t:=t)×List (Code n e)) : Code n e :=
  (solve (multiplicationTable basis) (preparedSystem basis A p))[p.1.length]?.getD (zeroCode n e)

theorem fp_preparedSystem : FP (inputEncoding basis (t:=t)) (systemEncoding n e) (preparedSystem basis A) :=
  fp_system _ _ _

theorem fp_recover : FP (inputEncoding basis (t:=t)) (encoding n e) (recover basis A) := by
  have hn:=(fp_fst (RepresentedPowerTable.encoding (presentation basis) t).list (encoding n e).list).comp
    (ListCodecMachines.fp_length (RepresentedPowerTable.encoding (presentation basis) t))
  exact (hn.pair ((fp_preparedSystem basis A).comp (fp_solve (multiplicationTable basis)))).comp
    (fp_codeLookup (encoding n e) (zeroCode n e))

theorem preparedSystem_order (p:Rows basis (t:=t)×List (Code n e)) :
    (preparedSystem basis A p).1.length=p.1.length+1 := matrix_length _ _ _ _

def orderEquiv (p:Rows basis (t:=t)×List (Code n e)) :
    Fin (preparedSystem basis A p).1.length ≃ Fin (p.1.length+1) :=
  finCongr (preparedSystem_order basis A p)

theorem preparedSystem_valid (p:Rows basis (t:=t)×List (Code n e)) (hy:∀c∈p.2,Valid n c) :
    SystemValid n e (preparedSystem basis A p) := by
  refine ⟨?_,?_⟩
  · exact matrix_valid (presentation basis) (FixedRealRootRestriction.arithmetic basis)
      (FixedRealInterpolationProducts.wordProductMachine basis A) p.1
  · intro c hc
    change c∈p.2++([RepresentedInterpolationMatrices.zero (presentation basis)] : List (Code n e)) at hc
    rcases List.mem_append.mp hc with hc|hc
    · exact hy c hc
    · have he:=List.mem_singleton.mp hc
      subst c
      exact (presentation basis).constant_valid 0

theorem preparedMatrix_reindex (p:Rows basis (t:=t)×List (Code n e))
    (hw:∀r∈p.1,(r.2.2.val.map (RepresentedExponentWords.symbol A)).prod=source (presentation basis) r) :
    Matrix.reindex (orderEquiv basis A p) (orderEquiv basis A p) (systemMatrix basis (preparedSystem basis A p))=
      listMatrix (p.1.length+1) (scalarRows (sourceNode (presentation basis) p.1) (targetNode (presentation basis) p.1)) := by
  ext i j
  change value basis (((preparedSystem basis A p).1[i.val]?.getD [])[j.val]?.getD (zeroCode n e))=_
  rw [value_row_lookup (value basis) _ (zeroCode_value basis)]
  change (((matrix (presentation basis) (FixedRealRootRestriction.arithmetic basis)
    (FixedRealInterpolationProducts.wordProductMachine basis A) p.1).map (List.map (presentation basis).value))[i.val]?.getD [])[j.val]?.getD 0=_
  rw [matrix_values_scalar _ _ _ _ hw]
  rfl

theorem preparedSystem_nonsingular (p:Rows basis (t:=t)×List (Code n e))
    (hw:∀r∈p.1,(r.2.2.val.map (RepresentedExponentWords.symbol A)).prod=source (presentation basis) r)
    (hi:Function.Injective (sourceNode (presentation basis) p.1))
    (hz:∀i,sourceNode (presentation basis) p.1 i≠0) :
    (systemMatrix basis (preparedSystem basis A p)).det≠0 := by
  rw [←Matrix.det_reindex_self (orderEquiv basis A p),preparedMatrix_reindex basis A p hw]
  exact scalarMatrix_det_ne_zero _ _ hi hz

theorem recover_correct (p:Rows basis (t:=t)×List (Code n e))
    (hw:∀r∈p.1,(r.2.2.val.map (RepresentedExponentWords.symbol A)).prod=source (presentation basis) r)
    (hi:Function.Injective (sourceNode (presentation basis) p.1))
    (hz:∀i,sourceNode (presentation basis) p.1 i≠0)
    (hy:∀c∈p.2,Valid n c) (y:Fin p.1.length→K)
    (hys:p.2.map (value basis)=List.ofFn y) :
    Valid n (recover basis A p) ∧ value basis (recover basis A p)=
      LagrangeRecovery.evaluateReplacement (sourceNode (presentation basis) p.1) (targetNode (presentation basis) p.1) y := by
  have hv:=preparedSystem_valid basis A p hy
  have hn:=preparedSystem_nonsingular basis A p hw hi hz
  have hT:=multiplicationTable_realizes basis
  have hs:=solve_correct basis _ hT _ hv hn
  let z:Fin (p.1.length+1)→K:=fun i=>value basis
    ((solve (multiplicationTable basis) (preparedSystem basis A p))[i.val]?.getD (zeroCode n e))
  have hx:(listMatrix (p.1.length+1) (scalarRows (sourceNode (presentation basis) p.1)
      (targetNode (presentation basis) p.1))).mulVec z=listVector (p.1.length+1) (scalarRhs y) := by
    funext i
    have hh:=congrFun hs ((orderEquiv basis A p).symm i)
    simp only [Matrix.mulVec,dotProduct] at hh
    rw [←(orderEquiv basis A p).symm.sum_comp] at hh
    have hm:=congrFun (congrFun (preparedMatrix_reindex basis A p hw) i)
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply] at hm
    simp only [hm] at hh
    change (∑j,listMatrix _ _ i j*z j)=_
    have hz' : (fun j:Fin (p.1.length+1)=>value basis
        ((solve (multiplicationTable basis) (preparedSystem basis A p))[((orderEquiv basis A p).symm j).val]?.getD (zeroCode n e)))=z:=rfl
    simp only [congrFun hz'] at hh
    rw [hh]
    change value basis ((preparedSystem basis A p).2[i.val]?.getD (zeroCode n e))=_
    rw [value_lookup (value basis) _ (zeroCode_value basis)]
    change ((p.2++([RepresentedInterpolationMatrices.zero (presentation basis)] : List (Code n e))).map (value basis))[i.val]?.getD 0=_
    have hc:value basis ((presentation basis).constant 0)=0:=(presentation basis).constant_value 0
    simp only [List.map_append,List.map_singleton,RepresentedInterpolationMatrices.zero,hc,hys]
    rfl
  refine ⟨?_,scalar_solution _ _ y hi hz z hx⟩
  exact solve_output_valid basis _ hT _ hv hn
    ((orderEquiv basis A p).symm (Fin.last p.1.length))

end PlanarHom.FixedRealInterpolationRecovery
