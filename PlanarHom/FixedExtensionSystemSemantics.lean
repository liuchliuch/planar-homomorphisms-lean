import PlanarHom.FixedExtensionSystemProgram
import PlanarHom.DenseRationalSystemCorrectness

/-! The literal expanded matrix agrees with the scalar-restriction block
matrix, including order zero and ragged input defaults. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

def SystemValid (n e:ℕ) (p:System n e) : Prop :=
  (∀row∈p.1,∀a∈row,Valid n a) ∧ ∀b∈p.2,Valid n b

def systemMatrix (basis:Module.Basis (Fin e) (RationalFunction n) K) (p:System n e) :
    Matrix (Fin p.1.length) (Fin p.1.length) K :=
  fun i j=>value basis (systemEntry n e p i.val j.val)

def systemVector (basis:Module.Basis (Fin e) (RationalFunction n) K) (p:System n e) : Fin p.1.length→K :=
  fun i=>value basis (systemRhs n e p i.val)

def expandedMatrixCode (T:MultiplicationTable n e) (p:System n e) :
    Matrix (Fin (p.1.length*e)) (Fin (p.1.length*e)) (FractionCode n) :=
  fun z w=>blockEntry T (systemEntry n e p (finProdFinEquiv.symm z).1.val (finProdFinEquiv.symm w).1.val)
    (finProdFinEquiv.symm z).2 (finProdFinEquiv.symm w).2

def expandedVectorCode (p:System n e) : Fin (p.1.length*e)→FractionCode n :=
  fun z=>((systemRhs n e p (finProdFinEquiv.symm z).1.val).1 (finProdFinEquiv.symm z).2,
    (systemRhs n e p (finProdFinEquiv.symm z).1.val).2)

theorem expand_ofFn (T:MultiplicationTable n e) (p:System n e) :
    expand T p=(List.ofFn (fun i=>List.ofFn (expandedMatrixCode T p i)),List.ofFn (expandedVectorCode p)) := by
  simp only [expand,blockList_ofFn,expandedRow]
  rfl

theorem codeLookup_valid (xs:List (Code n e)) (i:ℕ) (h:∀a∈xs,Valid n a) :
    Valid n (xs[i]?.getD (zeroCode n e)) := by
  cases he:xs[i]? with
  | none=>simpa [he] using zeroCode_valid n e
  | some a=>exact h a (List.mem_of_getElem? he)

theorem systemEntry_valid (p:System n e) (h:SystemValid n e p) (i j:ℕ) :
    Valid n (systemEntry n e p i j) := by
  apply codeLookup_valid
  intro a ha
  cases he:p.1[i]? with
  | none=>simp [he] at ha
  | some row=>exact h.1 row (List.mem_of_getElem? he) a (by simpa [he] using ha)

theorem systemRhs_valid (p:System n e) (h:SystemValid n e p) (i:ℕ) :
    Valid n (systemRhs n e p i) := codeLookup_valid p.2 i h.2

theorem expandedMatrixCode_valid (T:MultiplicationTable n e) (p:System n e) (h:SystemValid n e p)
    (i j:Fin (p.1.length*e)) : FractionValid n (expandedMatrixCode T p i j) :=
  blockEntry_valid T _ (systemEntry_valid p h _ _) _ _

theorem expandedVectorCode_valid (p:System n e) (h:SystemValid n e p)
    (i:Fin (p.1.length*e)) : FractionValid n (expandedVectorCode p i) := systemRhs_valid p h _

theorem expandedMatrixCode_value (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (T:MultiplicationTable n e) (hT:T.Realizes basis) (p:System n e) :
    (fun i j=>fractionValue n (expandedMatrixCode T p i j))=
      Matrix.reindex finProdFinEquiv finProdFinEquiv (ExtensionCoordinateSystem.block basis (systemMatrix basis p)) := by
  ext i j
  exact blockEntry_value basis T hT _ _ _

theorem expandedVectorCode_value (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (p:System n e) (i:Fin (p.1.length*e)) :
    fractionValue n (expandedVectorCode p i)=
      ExtensionCoordinateSystem.coordinates basis (systemVector basis p) (finProdFinEquiv.symm i) := by
  change _=basis.equivFun (basis.equivFun.symm (coordinates n (systemRhs n e p _))) _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem expandedMatrixCode_nonsingular (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (T:MultiplicationTable n e) (hT:T.Realizes basis) (p:System n e)
    (h:(systemMatrix basis p).det≠0) :
    (show Matrix (Fin (p.1.length*e)) (Fin (p.1.length*e)) (RationalFunction n) from
      fun i j=>fractionValue n (expandedMatrixCode T p i j)).det≠0 := by
  rw [expandedMatrixCode_value basis T hT,Matrix.det_reindex_self]
  exact (ExtensionCoordinateSystem.det_ne_zero_iff basis _).mpr h

end PlanarHom.FixedRealExtension
