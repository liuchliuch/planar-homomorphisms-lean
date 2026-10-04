import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange

/-! A unit-lower-bidiagonal solve computes prefix products of an arbitrary
input list. Its determinant is exactly one, including order one. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BidiagonalProductSystem
variable {K:Type} [Field K]

def matrix (a:ℕ→K) (N:ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) K :=
  fun i j=>if i=j then 1 else if i.val=j.val+1 then -a j.val else 0

def vector (N:ℕ) : Fin (N+1)→K := fun i=>if i.val=0 then 1 else 0

@[simp] theorem matrix_det (a:ℕ→K) (N:ℕ) : (matrix a N).det=1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [matrix]
  · intro i j hij
    have h:i.val<j.val:=hij
    have hn:i≠j:=by intro he; subst j; omega
    have hs:i.val≠j.val+1:=by omega
    simp [matrix,hn,hs]

theorem row_zero (a:ℕ→K) (N:ℕ) (j:Fin (N+1)) :
    matrix a N 0 j=if j=0 then 1 else 0 := by
  have hn:(0:ℕ)≠j.val+1:=by omega
  simp [matrix,eq_comm,hn]

theorem row_succ (a:ℕ→K) (N:ℕ) (i:Fin N) (j:Fin (N+1)) :
    matrix a N i.succ j=(if j=i.succ then 1 else 0)+(if j=i.castSucc then -a i.val else 0) := by
  by_cases h:j=i.succ
  · subst j
    have hn:i.succ≠i.castSucc:=by intro he; have := congrArg Fin.val he; simp at this
    simp [matrix,hn]
  · by_cases h':j=i.castSucc
    · subst j
      simp [matrix,h,Ne.symm h]
    · have hn:i.succ.val≠j.val+1:=by
        intro he
        apply h'
        apply Fin.ext
        change j.val=i.val
        change i.val+1=j.val+1 at he
        omega
      have hval:i.val≠j.val:=fun he=>h' (Fin.ext he.symm)
      simp [matrix,h,h',Ne.symm h,hval]

theorem solution_zero (a:ℕ→K) (N:ℕ) (x:Fin (N+1)→K) (hx:(matrix a N).mulVec x=vector N) : x 0=1 := by
  have h:=congrFun hx 0
  simpa [Matrix.mulVec,dotProduct,row_zero,vector] using h

theorem solution_succ (a:ℕ→K) (N:ℕ) (x:Fin (N+1)→K) (hx:(matrix a N).mulVec x=vector N)
    (i:Fin N) : x i.succ=a i.val*x i.castSucc := by
  have h:=congrFun hx i.succ
  simp only [Matrix.mulVec,dotProduct,row_succ,add_mul,Finset.sum_add_distrib] at h
  have h':x i.succ+(-a i.val)*x i.castSucc=0:=by simpa [vector] using h
  linear_combination h'

theorem solution_prefix (a:ℕ→K) (N:ℕ) (x:Fin (N+1)→K) (hx:(matrix a N).mulVec x=vector N)
    (k:ℕ) (hk:k≤N) : x ⟨k,by omega⟩=((List.range k).map a).prod := by
  induction k with
  | zero=>simpa using solution_zero a N x hx
  | succ k ih=>
    have hi:k<N:=by omega
    have hs:=solution_succ a N x hx ⟨k,hi⟩
    have hh:=ih (by omega)
    change x ⟨k+1,by omega⟩=a k*x ⟨k,by omega⟩ at hs
    rw [hs,hh,List.range_succ,List.map_append,List.prod_append]
    simp [mul_comm]

theorem solution_last (a:ℕ→K) (N:ℕ) (x:Fin (N+1)→K) (hx:(matrix a N).mulVec x=vector N) :
    x (Fin.last N)=((List.range N).map a).prod := solution_prefix a N x hx N le_rfl

end PlanarHom.BidiagonalProductSystem
