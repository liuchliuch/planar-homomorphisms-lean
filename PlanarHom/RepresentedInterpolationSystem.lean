import PlanarHom.Interpolation
import PlanarHom.LagrangeRecovery
import Mathlib.LinearAlgebra.Matrix.Block

/-! One augmented shifted-Vandermonde solve returns the replacement value
itself. This avoids asserting a polynomial bound for an arbitrary-length
unreduced representative dot-product after interpolation. Signed nodes and
zero target products are permitted; the empty table gives the 1×1 system. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedInterpolation
open Interpolation LagrangeRecovery
variable {K:Type} [Field K] {n:ℕ}

def augmented (μ θ:Fin n→K) : Matrix (Fin n⊕Unit) (Fin n⊕Unit) K :=
  Matrix.fromBlocks (shiftedVandermonde μ) 0 (fun _ j=> -θ j) 1

def rhs (y:Fin n→K) : (Fin n⊕Unit)→K := Sum.elim y (fun _=>0)

theorem augmented_det (μ θ:Fin n→K) : (augmented μ θ).det=(shiftedVandermonde μ).det := by
  rw [augmented,Matrix.det_fromBlocks_zero₁₂]
  simp

theorem augmented_det_ne_zero (μ θ:Fin n→K) (hμ:Function.Injective μ) (hzero:∀j,μ j≠0) :
    (augmented μ θ).det≠0 := by
  rw [augmented_det]
  exact shiftedVandermonde_det_ne_zero μ hμ hzero

theorem evaluateReplacement_eq_evaluateTarget (μ θ y:Fin n→K)
    (hμ:Function.Injective μ) (hzero:∀j,μ j≠0) :
    evaluateReplacement μ θ y=evaluateTarget μ θ y := by
  have hd:(shiftedVandermonde μ).det≠0:=shiftedVandermonde_det_ne_zero μ hμ hzero
  have hy:queryValues μ (recoverCoefficients μ y)=y := by
    rw [queryValues_eq_mulVec,recoverCoefficients,Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
  rw [←hy,evaluateReplacement_queryValues μ θ _ hμ hzero,
    evaluateTarget_queryValues μ θ _ hμ hzero]

theorem augmented_solution (μ θ y:Fin n→K) (hμ:Function.Injective μ) (hzero:∀j,μ j≠0)
    (x:(Fin n⊕Unit)→K) (hx:(augmented μ θ).mulVec x=rhs y) :
    x (.inr ())=evaluateReplacement μ θ y := by
  have htop:(shiftedVandermonde μ).mulVec (fun j=>x (.inl j))=y := by
    funext h
    have he:=congrFun hx (.inl h)
    simpa [augmented,rhs,Matrix.mulVec,dotProduct,Matrix.fromBlocks] using he
  have hbottom:x (.inr ())=∑j,θ j*x (.inl j) := by
    have he:=congrFun hx (.inr ())
    have he': -(∑j,θ j*x (.inl j))+x (.inr ())=0 := by
      simpa [augmented,rhs,Matrix.mulVec,dotProduct,Matrix.fromBlocks,Finset.sum_neg_distrib,neg_mul] using he
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg,add_comm] using he')
  have hcoeff:recoverCoefficients μ y=(fun j=>x (.inl j)) := by
    rw [←htop,recoverCoefficients,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (shiftedVandermonde_det_ne_zero μ hμ hzero)),Matrix.one_mulVec]
  rw [evaluateReplacement_eq_evaluateTarget μ θ y hμ hzero,evaluateTarget,hcoeff]
  exact hbottom

end PlanarHom.RepresentedInterpolation
