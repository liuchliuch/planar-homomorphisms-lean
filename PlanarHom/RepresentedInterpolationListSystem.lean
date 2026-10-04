import PlanarHom.RepresentedInterpolationSystem
import Mathlib.Data.List.OfFn

/-! Exact finite matrix semantics of the emitted list system, including its
last interpolation-output coordinate and the zero-node case. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedInterpolation
variable {K:Type} [Field K] {n:ℕ}

def lastEquiv (n:ℕ) : (Fin n⊕Unit)≃Fin (n+1) where
  toFun:=Sum.elim Fin.castSucc (fun _=>Fin.last n)
  invFun:=Fin.lastCases (.inr ()) Sum.inl
  left_inv:=by
    rintro (i|u)
    · simp
    · cases u; simp
  right_inv:=by intro i; refine Fin.lastCases ?_ (fun j=>?_) i <;> simp

@[simp] theorem lastEquiv_left (i:Fin n) : lastEquiv n (.inl i)=i.castSucc := rfl
@[simp] theorem lastEquiv_right : lastEquiv n (.inr ())=Fin.last n := rfl

def scalarRows (μ θ:Fin n→K) : List (List K) :=
  (List.ofFn (fun i:Fin n=>List.ofFn (fun j:Fin n=>μ j^(i.val+1))++[0]))++
    [List.ofFn (fun j=> -θ j)++[1]]

def scalarRhs (y:Fin n→K) : List K := List.ofFn y++[0]

def listMatrix (n:ℕ) (rs:List (List K)) : Matrix (Fin n) (Fin n) K :=
  fun i j=>((rs[i.val]?.getD [])[j.val]?).getD 0

def listVector (n:ℕ) (ys:List K) : Fin n→K := fun i=>ys[i.val]?.getD 0

theorem ofFn_append_get {B:Type} (f:Fin n→B) (b d:B) (i:Fin (n+1)) :
    ((List.ofFn f++[b])[i.val]?).getD d=Fin.lastCases b f i := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp [List.getElem?_append_right]
  · rw [List.getElem?_append_left (by simpa using j.isLt)]
    simp

theorem scalarMatrix_reindex (μ θ:Fin n→K) :
    Matrix.reindex (lastEquiv n).symm (lastEquiv n).symm (listMatrix (n+1) (scalarRows μ θ))=
      augmented μ θ := by
  ext i j
  change ((scalarRows μ θ)[(lastEquiv n i).val]?.getD [])[((lastEquiv n) j).val]?.getD 0=_
  rw [scalarRows,ofFn_append_get]
  cases i with
  | inl i=>
    simp only [lastEquiv_left,Fin.lastCases_castSucc]
    rw [ofFn_append_get]
    cases j <;> simp [augmented,Matrix.fromBlocks,Interpolation.shiftedVandermonde,pow_succ,lastEquiv]
  | inr u=>
    cases u
    simp only [lastEquiv_right,Fin.lastCases_last]
    rw [ofFn_append_get]
    cases j <;> simp [augmented,Matrix.fromBlocks,lastEquiv]

theorem scalarMatrix_det_ne_zero (μ θ:Fin n→K) (hμ:Function.Injective μ) (hz:∀i,μ i≠0) :
    (listMatrix (n+1) (scalarRows μ θ)).det≠0 := by
  have h:=augmented_det_ne_zero μ θ hμ hz
  rw [←scalarMatrix_reindex,Matrix.det_reindex_self] at h
  exact h

theorem scalar_solution (μ θ y:Fin n→K) (hμ:Function.Injective μ) (hz:∀i,μ i≠0)
    (x:Fin (n+1)→K)
    (hx:(listMatrix (n+1) (scalarRows μ θ)).mulVec x=listVector (n+1) (scalarRhs y)) :
    x (Fin.last n)=LagrangeRecovery.evaluateReplacement μ θ y := by
  apply augmented_solution μ θ y hμ hz (fun i=>x (lastEquiv n i))
  funext i
  have hh:=congrFun hx (lastEquiv n i)
  change (∑j,(listMatrix (n+1) (scalarRows μ θ)) (lastEquiv n i) j*x j)=_ at hh
  rw [←(lastEquiv n).sum_comp] at hh
  have hm:=congrFun (congrFun (scalarMatrix_reindex μ θ) i)
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm] at hm
  simp only [hm] at hh
  change (∑j,augmented μ θ i j*x (lastEquiv n j))=rhs y i
  rw [hh]
  change ((scalarRhs y)[(lastEquiv n i).val]?).getD 0=rhs y i
  rw [scalarRhs,ofFn_append_get]
  cases i <;> simp [rhs,lastEquiv]

end PlanarHom.RepresentedInterpolation
