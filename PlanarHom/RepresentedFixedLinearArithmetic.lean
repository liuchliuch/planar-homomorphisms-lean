import PlanarHom.RepresentedFieldEncoding
import PlanarHom.ListDecompositionMachines
import PlanarHom.ArithmeticCircuitPrimitives

/-! Fixed-dimensional linear combinations need only actual represented
addition and multiplication. Recursion has a fixed source-dependent depth;
no unproved polynomial-loop growth bound is used. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedBit
open Complexity ArithmeticCircuitPrimitives
variable {K:Type} [CommSemiring K]

structure AddMulMachines (P:Presentation K) where
  add : P.Code×P.Code→P.Code
  mul : P.Code×P.Code→P.Code
  fp_add : FP (P.encoding.prod P.encoding) P.encoding add
  fp_mul : FP (P.encoding.prod P.encoding) P.encoding mul
  add_valid : ∀a b,P.valid a→P.valid b→P.valid (add (a,b))
  add_value : ∀a b,P.valid a→P.valid b→P.value (add (a,b))=P.value a+P.value b
  mul_valid : ∀a b,P.valid a→P.valid b→P.valid (mul (a,b))
  mul_value : ∀a b,P.valid a→P.valid b→P.value (mul (a,b))=P.value a*P.value b

def Presentation.constant (P:Presentation K) (x:K) : P.Code := Classical.choose (P.complete x)
theorem Presentation.constant_valid (P:Presentation K) (x:K) : P.valid (P.constant x) :=
  (Classical.choose_spec (P.complete x)).1
@[simp] theorem Presentation.constant_value (P:Presentation K) (x:K) : P.value (P.constant x)=x :=
  (Classical.choose_spec (P.complete x)).2

def AddMulMachines.dot {P:Presentation K} (M:AddMulMachines P) :
    (k:ℕ)→(Fin k→P.Code)→List P.Code→P.Code
  | 0,_,_=>P.constant 0
  | k+1,c,xs=>M.add (M.mul (c 0,xs.headD (P.constant 0)),M.dot k (fun r=>c r.succ) xs.tail)

theorem AddMulMachines.fp_dot {P:Presentation K} (M:AddMulMachines P) (k:ℕ) (c:Fin k→P.Code) :
    FP P.encoding.list P.encoding (M.dot k c) := by
  induction k with
  | zero=>exact fp_const _ _ _
  | succ k ih=>
    have hhead:=ListDecompositionMachines.fp_headD P.encoding (P.constant 0)
    have hmul:=((fp_const _ P.encoding (c 0)).pair hhead).comp M.fp_mul
    have htail:=ListDecompositionMachines.fp_tail P.encoding (P.constant 0)
    exact (hmul.pair (htail.comp (ih (fun r=>c r.succ)))).comp M.fp_add

theorem AddMulMachines.dot_ofFn {P:Presentation K} (M:AddMulMachines P) (k:ℕ)
    (c y:Fin k→P.Code) (hc:∀r,P.valid (c r)) (hy:∀r,P.valid (y r)) :
    P.valid (M.dot k c (List.ofFn y)) ∧
      P.value (M.dot k c (List.ofFn y))=∑r,P.value (c r)*P.value (y r) := by
  induction k with
  | zero=>
    constructor
    · exact P.constant_valid 0
    · simp [dot]
  | succ k ih=>
    have ht:=ih (fun r=>c r.succ) (fun r=>y r.succ) (fun r=>hc r.succ) (fun r=>hy r.succ)
    rw [List.ofFn_succ]
    simp only [dot,List.headD_cons,List.tail_cons]
    have hm:=M.mul_valid (c 0) (y 0) (hc 0) (hy 0)
    refine ⟨M.add_valid _ _ hm ht.1,?_⟩
    rw [M.add_value _ _ hm ht.1,M.mul_value _ _ (hc 0) (hy 0),ht.2,Fin.sum_univ_succ]

end PlanarHom.RepresentedBit
