import PlanarHom.DensePolynomialEvaluationMachines
import PlanarHom.MaterializedGridWeightsSemantics

/-! NEW executable rational Lagrange weights on the literal integer grid.
Weights act on arbitrary polynomial coefficient rings through qHom. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def selector (d k:ℕ) : List ℚ := (List.range (d+1)).map (fun i=>if i=k then 1 else 0)

def gridWeight (d k j:ℕ) : ℚ :=
  MaterializedGridWeightsMachines.weight
    ((MaterializedGridWeightsMachines.grid d,selector d k),(j:ℚ))

 theorem selector_ofFn (d k:ℕ) :
    selector d k=List.ofFn (fun i:Fin (d+1)=>if i.val=k then (1:ℚ) else 0) := by
  apply List.ext_getElem (by simp [selector])
  intro i hi hj
  simp only [selector,List.getElem_map,List.getElem_range,List.getElem_ofFn]

 theorem gridWeight_eq (d:ℕ) (k j:Fin (d+1)) :
    gridWeight d k.val j.val=
      (Lagrange.basis Finset.univ (fun i:Fin (d+1)=>(i.val:ℚ)) j).coeff k.val := by
  rw [gridWeight,selector_ofFn,MaterializedGridWeightsMachines.grid_eq_ofFn,
    MaterializedGridWeightsMachines.weight_ofFn _ _ AlgebraPolynomialInterpolation.integer_nodes_injective]
  simp only [mul_ite,mul_one,mul_zero]
  simp only [←Fin.ext_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

 theorem grid_coefficient (n d:ℕ) (P:Polynomial (Poly n)) (hP:P.natDegree≤d)
    (k:Fin (d+1)) :
    (∑j:Fin (d+1),qHom n (gridWeight d k.val j.val)*P.eval (qHom n (j.val:ℚ)))=P.coeff k.val := by
  letI : Algebra ℚ (Poly n):=(qHom n).toAlgebra
  have h:=AlgebraPolynomialInterpolation.integer_coefficient_interpolation (K:=ℚ) P hP k.val
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [gridWeight_eq d k j]
  exact mul_comm _ _

 theorem fp_selector : FP (BitEncoding.unaryNat.prod BitEncoding.nat) rationalCode.list
    (fun p=>selector p.1 p.2) := by
  let ei:=BitEncoding.unaryNat.prod BitEncoding.nat
  have hd:=fp_fst BitEncoding.unaryNat BitEncoding.nat
  have hk:=fp_snd BitEncoding.unaryNat BitEncoding.nat
  have hr:=(hd.comp UnaryArithmeticMachines.fp_succ).comp UnaryArithmeticMachines.fp_range
  have he:=NatListSumMachines.fp_equal
  have hb:FP (BitEncoding.nat.prod BitEncoding.nat) rationalCode
      (fun p:ℕ×ℕ=>if p.2=p.1 then (1:ℚ) else 0) :=
    (FP.ite he (fp_const _ rationalCode 1) (fp_const _ rationalCode 0)).congr
      (fun p=>by simp [eq_comm])
  exact ((hk.pair hr).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat rationalCode _ hb))

 theorem fp_gridWeight : FP ((BitEncoding.unaryNat.prod BitEncoding.nat).prod BitEncoding.nat)
    rationalCode (fun p=>gridWeight p.1.1 p.1.2 p.2) := by
  let ei:=BitEncoding.unaryNat.prod BitEncoding.nat
  have hd:=(fp_fst ei BitEncoding.nat).comp (fp_fst BitEncoding.unaryNat BitEncoding.nat)
  have hs:=(fp_fst ei BitEncoding.nat).comp fp_selector
  have hj:=(fp_snd ei BitEncoding.nat).comp (FixedFieldPolynomialMachines.fp_natCast rationalBasis)
  have hg:=hd.comp (MaterializedGridWeightsMachines.fp_grid rationalBasis)
  exact (((hg.pair hs).pair hj).comp (MaterializedGridWeightsMachines.fp_weight rationalBasis))

end PlanarHom.DensePolynomial
