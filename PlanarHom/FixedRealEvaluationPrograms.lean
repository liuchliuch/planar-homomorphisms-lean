import PlanarHom.FixedRealCoefficientEvaluation
import PlanarHom.FixedRealListProductCorrectness

/-! NEW closure of concrete represented-field computers. Every operation
constructs its actual code program and charges its existing TM2 witness. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealEvaluation
open Complexity DensePolynomial FixedRealExtension
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

structure Program {A:Type} (ea:BitEncoding A) (H:A→Prop) (f:A→K) where
  run:A→Code n e
  fp:FP ea (encoding n e) run
  valid:∀a,H a→Valid n (run a)
  value:∀a,H a→FixedRealExtension.value basis (run a)=f a

namespace Program
variable {basis} {A B I:Type} {ea:BitEncoding A} {eb:BitEncoding B} {H:A→Prop} {J:B→Prop}
variable {f g:A→K}

def congr (P:Program basis ea H f) (g:A→K) (h:∀a,H a→f a=g a) : Program basis ea H g where
  run:=P.run
  fp:=P.fp
  valid:=P.valid
  value a ha:=(P.value a ha).trans (h a ha)

def pullback {f:B→K} (P:Program basis eb J f) (ea:BitEncoding A) (H:A→Prop)
    (q:A→B) (hq:FP ea eb q) (h:∀a,H a→J (q a)) : Program basis ea H (fun a=>f (q a)) where
  run a:=P.run (q a)
  fp:=hq.comp P.fp
  valid a ha:=P.valid _ (h a ha)
  value a ha:=P.value _ (h a ha)

def constant (basis:Module.Basis (Fin e) (RationalFunction n) K)
    (ea:BitEncoding A) (H:A→Prop) (x:K) : Program basis ea H (fun _=>x) where
  run _:=FixedRealCoefficientEvaluation.power basis x 1
  fp:=fp_const _ _ _
  valid _ _:=FixedRealCoefficientEvaluation.power_valid basis x 1
  value _ _:=by simpa using FixedRealCoefficientEvaluation.power_value basis x 1

def add (P:Program basis ea H f) (Q:Program basis ea H g) : Program basis ea H (fun a=>f a+g a) where
  run a:=FixedRealExtension.add n (P.run a) (Q.run a)
  fp:=(P.fp.pair Q.fp).comp (FixedRealExtension.fp_add n e)
  valid a ha:=add_valid _ _ (P.valid a ha) (Q.valid a ha)
  value a ha:=by rw [value_add basis _ _ (P.valid a ha) (Q.valid a ha),P.value a ha,Q.value a ha]

def mul (P:Program basis ea H f) (Q:Program basis ea H g) : Program basis ea H (fun a=>f a*g a) where
  run a:=FixedRealExtension.mul (multiplicationTable basis) (P.run a) (Q.run a)
  fp:=(P.fp.pair Q.fp).comp (FixedRealExtension.fp_mul n e (multiplicationTable basis))
  valid a ha:=mul_valid _ _ _ (P.valid a ha) (Q.valid a ha)
  value a ha:=by rw [value_mul _ basis (multiplicationTable_realizes basis),P.value a ha,Q.value a ha]

def ite (p:A→Bool) (hp:FP ea BitEncoding.bool p)
    (P:Program basis ea H f) (Q:Program basis ea H g) :
    Program basis ea H (fun a=>if p a then f a else g a) where
  run a:=if p a then P.run a else Q.run a
  fp:=(hp.congr (fun a=>show p a=decide (p a=true) from by simp)).ite P.fp Q.fp
  valid a ha:=by cases h:p a <;> simp only [h,Bool.false_eq_true,if_false,if_true];exact Q.valid a ha;exact P.valid a ha
  value a ha:=by cases h:p a <;> simp only [h,Bool.false_eq_true,if_false,if_true];exact Q.value a ha;exact P.value a ha

def sum [DecidableEq I] (s:Finset I) (f:I→A→K) (P:∀i,Program basis ea H (f i)) :
    Program basis ea H (fun a=>∑i∈s,f i a) := by
  apply Classical.choice
  induction s using Finset.induction_on with
  | empty=>exact ⟨(constant basis ea H 0).congr _ (fun _ _=>by simp)⟩
  | @insert i s hi ih=>
    obtain ⟨ih⟩:=ih
    exact ⟨((P i).add ih).congr _ (fun _ _=>by simp [hi])⟩

def prod [DecidableEq I] (s:Finset I) (f:I→A→K) (P:∀i,Program basis ea H (f i)) :
    Program basis ea H (fun a=>∏i∈s,f i a) := by
  apply Classical.choice
  induction s using Finset.induction_on with
  | empty=>exact ⟨(constant basis ea H 1).congr _ (fun _ _=>by simp)⟩
  | @insert i s hi ih=>
    obtain ⟨ih⟩:=ih
    exact ⟨((P i).mul ih).congr _ (fun _ _=>by simp [hi])⟩

def productMap (P:Program basis ea H f) :
    Program basis ea.list (fun xs=>∀a∈xs,H a) (fun xs=>(xs.map f).prod) where
  run xs:=FixedRealListProduct.product basis (xs.map P.run)
  fp:=(ListMapMachines.fp_map _ _ _ P.fp).comp (FixedRealListProduct.fp_product basis)
  valid xs hx:=FixedRealListProduct.product_valid basis _ (by
    intro a ha
    obtain ⟨x,hx',rfl⟩:=List.mem_map.mp ha
    exact P.valid x (hx x hx'))
  value xs hx:=by
    rw [FixedRealListProduct.product_value basis _ (by
      intro a ha
      obtain ⟨x,hx',rfl⟩:=List.mem_map.mp ha
      exact P.valid x (hx x hx')),List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact P.value a (hx a ha)

theorem inFP (P:Program basis ea H f) (normalizer:BitEncoding.Normalizer ea) :
    ((presentation basis).problem ea H f).InFP :=
  RepresentedBit.Presentation.problem_inFP _ _ normalizer _ _ P.run P.fp P.valid P.value

end Program
end PlanarHom.FixedRealEvaluation
