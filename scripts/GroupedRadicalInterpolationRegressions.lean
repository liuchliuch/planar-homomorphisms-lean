import PlanarHom.GroupedShiftedInterpolation
import PlanarHom.BooleanFieldTowerInverseMachines
import PlanarHom.BooleanRetainedTensor

noncomputable section
open Classical
open PlanarHom
open PlanarHom.GroupedProductInterpolation

private def grp (i : Fin 3) : Fin 2:=if i.val=2 then 1 else 0
private def nodes (i : Fin 3) : ℚ×ℚ:=if i.val=2 then (2,5) else (1,3)
private def values (c : Fin 2) : ℚ×ℚ:=if c.val=0 then (7,11) else (13,17)
private theorem nodes_unit : ∀i,IsUnit (nodes i) := by
  intro i
  fin_cases i <;> norm_num [nodes,Prod.isUnit_iff,isUnit_iff_ne_zero]
private theorem cross_unit : ∀i j,grp i≠grp j→IsUnit (nodes i-nodes j) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [grp,nodes,Prod.isUnit_iff,isUnit_iff_ne_zero,Fin.ext_iff] at *

-- Repeated nodes inside one target group, in a ring with zero divisors.
example : nodes 0=nodes 1 := rfl
example (i : Fin 3) : (shiftedInterpolant grp nodes values).eval (nodes i)=values (grp i) :=
  shiftedInterpolant_eval grp nodes values nodes_unit cross_unit i
example : (shiftedInterpolant grp nodes values).coeff 0=0 :=
  shiftedInterpolant_zero grp nodes values nodes_unit cross_unit
example : (shiftedInterpolant grp nodes values).natDegree≤20 := by
  simpa using shiftedInterpolant_degree grp nodes values
example : ((1,0) : ℚ×ℚ)*((0,1) : ℚ×ℚ)=0 := by ext <;> norm_num

-- A square radicand gives zero divisors. Principal evaluation alone is not injective.
private def p : BooleanFieldTower.Tower ℚ 1 := (1,1)
example : BooleanFieldTower.norm (fun _ : ℕ=>(1 : ℚ)) 1 p=0 := by
  norm_num [BooleanFieldTower.norm,BooleanFieldTower.sub,BooleanFieldTower.add,
    BooleanFieldTower.neg,BooleanFieldTower.mul,BooleanFieldTower.embed,p]
example : BooleanFieldTowerEvaluation.eval (algebraMap ℚ ℝ) (fun _=>1) 1 p (fun _=>false)=2 := by
  norm_num [BooleanFieldTowerEvaluation.eval,p]
example : BooleanFieldTowerEvaluation.eval (algebraMap ℚ ℝ) (fun _=>1) 1 p (fun _=>true)=0 := by
  norm_num [BooleanFieldTowerEvaluation.eval,p]
private def dependent : BooleanFieldTower.Tower ℚ 2 := ((0,1),(-1,0))
example : dependent≠BooleanFieldTower.zero 2 := by decide
example : BooleanFieldTowerEvaluation.eval (algebraMap ℚ ℝ) (fun _=>1) 2 dependent (fun _=>false)=0 := by
  norm_num [BooleanFieldTowerEvaluation.eval,dependent]
example : BooleanFieldTowerEvaluation.eval (algebraMap ℚ ℝ) (fun _=>1) 2 dependent
    (fun i=>decide (i=1))=2 := by
  norm_num [BooleanFieldTowerEvaluation.eval,dependent,show (Fin.last 1 : Fin 2)=1 from rfl]

#print axioms recover_positive_moments
#print axioms BooleanFieldTowerEvaluation.allSign_injective
#print axioms BooleanFieldTowerReconstruction.reconstruction
#print axioms BooleanFieldTowerInverseMachines.fp_inverse
#print axioms BooleanRetainedTensor.partition_retained
#print axioms BooleanRetainedTensor.unique_positive_root
