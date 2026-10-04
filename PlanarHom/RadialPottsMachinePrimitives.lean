import PlanarHom.RadialPottsNumericProgram
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.UnaryNatConversionMachine
import PlanarHom.ListReverseMachines
import PlanarHom.ListContextMachines
import PlanarHom.ListFlattenMachines
import PlanarHom.ListDropMachines
import PlanarHom.NatListSumMachines
import PlanarHom.ConditionalMachines
import PlanarHom.BinaryDivisionMachine

/-! Real arithmetic and list-building compiler primitives for the radial
serializer. Range counters are serialized in unary; lookups use capped binary
indexing, so all definitions remain polynomial on arbitrary encoded inputs. -/
namespace PlanarHom.RadialPotts.Numeric
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
variable {A B : Type} {ea : BitEncoding A} {eb : BitEncoding B}

 theorem fp_add {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.nat (fun x => f x+g x) := (hf.pair hg).comp BinaryArithmetic.fp_addition
 theorem fp_mul {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.nat (fun x => f x*g x) := (hf.pair hg).comp BinaryArithmetic.fp_multiplication
 theorem fp_sub {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.nat (fun x => f x-g x) := (hf.pair hg).comp BinaryArithmetic.fp_subtraction
 theorem fp_div {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.nat (fun x => f x/g x) :=
  ((hf.pair hg).comp BinaryArithmetic.fp_division).comp (fp_fst BitEncoding.nat BitEncoding.nat)
 theorem fp_mod {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.nat (fun x => f x%g x) :=
  ((hf.pair hg).comp BinaryArithmetic.fp_division).comp (fp_snd BitEncoding.nat BitEncoding.nat)
 theorem fp_lt {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.bool (fun x => decide (f x<g x)) := (hf.pair hg).comp BinaryArithmetic.fp_comparison
 theorem fp_eq {f g : A → ℕ} (hf : FP ea BitEncoding.nat f) (hg : FP ea BitEncoding.nat g) :
    FP ea BitEncoding.bool (fun x => decide (f x=g x)) := (hf.pair hg).comp NatListSumMachines.fp_equal
 theorem fp_and {p q : A → Prop} [DecidablePred p] [DecidablePred q]
    (hp : FP ea BitEncoding.bool (fun x => decide (p x)))
    (hq : FP ea BitEncoding.bool (fun x => decide (q x))) :
    FP ea BitEncoding.bool (fun x => decide (p x ∧ q x)) :=
  ((hp.pair hq).comp (fp_bool_gate (fun p => p.1 && p.2))).congr (fun x => by simp)

 theorem fp_natGetD {xs : A → List ℕ} {i : A → ℕ}
    (hx : FP ea BitEncoding.nat.list xs) (hi : FP ea BitEncoding.nat i) :
    FP ea BitEncoding.nat (fun x => (xs x).getD (i x) 0) :=
  (((hi.pair hx).comp (ListDropMachines.fp_drop BitEncoding.nat 0)).comp
    (ListDecompositionMachines.fp_headD BitEncoding.nat 0)).congr (fun x => by
      simp [List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])

 theorem fp_unaryRange : FP BitEncoding.unaryNat BitEncoding.unaryNat.list List.range := by
  have hr : FP BitEncoding.unaryNat BitEncoding.nat.list List.range :=
    (UnaryRangeMachines.fp_range.comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
      (fun n => by simp)
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat BitEncoding.nat BitEncoding.unaryNat
    (fun p : ℕ×ℕ => min p.1 p.2) (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
      BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  apply (((fp_id BitEncoding.unaryNat).pair hr).comp hm).congr
  intro n
  calc
    _ = (List.range n).map id := List.map_congr_left (fun i hi => min_eq_right (Nat.le_of_lt (List.mem_range.mp hi)))
    _ = _ := by simp

 theorem fp_rangeMap {n : A → ℕ} (hn : FP ea BitEncoding.unaryNat n)
    (f : A×ℕ → B) (hf : FP (ea.prod BitEncoding.unaryNat) eb f) :
    FP ea eb.list (fun a => (List.range (n a)).map (fun i => f (a,i))) :=
  ((fp_id ea).pair (hn.comp fp_unaryRange)).comp
    (ListContextMachines.fp_mapWithContext ea BitEncoding.unaryNat eb f hf)

 theorem fp_rangeFlatMap {n : A → ℕ} (hn : FP ea BitEncoding.unaryNat n)
    (f : A×ℕ → List B) (hf : FP (ea.prod BitEncoding.unaryNat) eb.list f) :
    FP ea eb.list (fun a => (List.range (n a)).flatMap (fun i => f (a,i))) :=
  (fp_rangeMap hn f hf).comp (ListFlattenMachines.fp_flatten eb)
end PlanarHom.RadialPotts.Numeric
