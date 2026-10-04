import PlanarHom.BoundedPolynomialEvaluationMachines
import PlanarHom.ListContextMachines

/-! # Concrete compilation of the discrete sign-partition searches -/

noncomputable section
namespace PlanarHom.DiscreteSignPartitionMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BinaryArithmetic RationalCircuits DiscreteSignPartition

def intervalEncoding : BitEncoding Interval := BitEncoding.nat.prod BitEncoding.nat

theorem fp_singleton {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (f : α → β) (hf : FP ea eb f) : FP ea eb.list (fun a => [f a]) :=
  (hf.pair (fp_const ea eb.list [])).comp (ListMutationMachines.fp_cons eb)

theorem fp_three {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (f g h : α → β) (hf : FP ea eb f) (hg : FP ea eb g) (hh : FP ea eb h) :
    FP ea eb.list (fun a => [f a,g a,h a]) :=
  (hf.pair ((hg.pair (fp_singleton ea eb h hh)).comp (ListMutationMachines.fp_cons eb))).comp
    (ListMutationMachines.fp_cons eb)

theorem fp_threshold {α : Type} (ea : BitEncoding α) (test : α → ℕ → Bool)
    (ht : FP (ea.prod BitEncoding.nat) BitEncoding.bool (fun p => test p.1 p.2)) :
    FP (ea.prod intervalEncoding) BitEncoding.nat
      (fun p => threshold (test p.1) p.2.1 p.2.2) := by
  let ec := ea.prod BitEncoding.nat
  have hs := fp_fst ec BitEncoding.nat
  have hctx := hs.comp (fp_fst ea BitEncoding.nat)
  have hlo := hs.comp (fp_snd ea BitEncoding.nat)
  have hoff := fp_snd ec BitEncoding.nat
  have hindex := (hlo.pair hoff).comp fp_addition
  have htest := (hctx.pair hindex).comp ht
  have hx := fp_fst ea intervalEncoding
  have hi := fp_snd ea intervalEncoding
  have hl := hi.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hh := hi.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hN := (((hh.pair hl).comp fp_subtraction).pair
    (fp_const (ea.prod intervalEncoding) BitEncoding.nat 1)).comp fp_subtraction
  have hc := ((hx.pair hl).pair hN).comp
    (IntervalBisection.fp_cut ec (fun p t => test p.1 (p.2+t)) htest)
  exact ((hl.pair hc).comp fp_addition).congr (fun p => by
    dsimp only [Function.comp_apply]
    unfold threshold
    apply congrArg (fun k => p.2.1+k)
    exact IntervalBisection.cut_congr _ _ _ _ _ (fun _ => rfl))

theorem fp_splitIncreasing {α : Type} (ea : BitEncoding α) (f : α → ℕ → ℚ)
    (hf : FP (ea.prod BitEncoding.nat) BitEncoding.rat (fun p => f p.1 p.2)) :
    FP (ea.prod intervalEncoding) intervalEncoding.list
      (fun p => splitIncreasing (f p.1) p.2.1 p.2.2) := by
  have hi := fp_snd ea intervalEncoding
  have hl := hi.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hh := hi.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hg := (hl.pair hh).comp fp_comparison
  have ha := fp_threshold ea (fun a t => decide (0 ≤ f a t))
    (hf.comp RationalOrderMachines.fp_nonnegative)
  have hb := fp_threshold ea (fun a t => decide (0 < f a t))
    (hf.comp RationalOrderMachines.fp_positive)
  have hyes := fp_three _ intervalEncoding _ _ _ (hl.pair ha) (ha.pair hb) (hb.pair hh)
  have hno := fp_singleton _ intervalEncoding _ hi
  exact ((hg.pair (hyes.pair hno)).comp (ConditionalMachines.fp_select intervalEncoding.list)).congr
    (fun p => by simp [splitIncreasing])

end PlanarHom.DiscreteSignPartitionMachines

namespace PlanarHom.PolynomialDiscretePartitionMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open BinaryArithmetic RationalCircuits PolynomialDiscretePartition
open DiscreteSignPartitionMachines BoundedPolynomialEvaluationMachines

theorem fp_oriented {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) :
    FP ((ea.prod BitEncoding.nat).prod BitEncoding.nat) BitEncoding.rat
      (fun a => oriented (p a.1.1) a.1.2 a.2) := by
  have hs := fp_fst (ea.prod BitEncoding.nat) BitEncoding.nat
  have hx := hs.comp (fp_fst ea BitEncoding.nat)
  have hi := fp_snd (ea.prod BitEncoding.nat) BitEncoding.nat
  have hv := (hx.pair hi).comp (fp_values ea p d hd hc)
  have hdiff := fp_values ea (fun a => difference (p a)) d
    (fun a => degree_difference_le (p a) d ((hd a).trans (Nat.le_succ _)))
    (fp_difference_coeff ea p d hd hc)
  have ht := (hs.comp hdiff).comp RationalOrderMachines.fp_nonnegative
  exact ((ht.pair (hv.pair (hv.comp fp_rational_negation))).comp
    (ConditionalMachines.fp_select BitEncoding.rat)).congr (fun a => by simp [oriented, ite_apply])

theorem fp_split {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) :
    FP (ea.prod intervalEncoding) intervalEncoding.list (fun a => split (p a.1) a.2) := by
  have hx := fp_fst ea intervalEncoding
  have hi := fp_snd ea intervalEncoding
  have hl := hi.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  exact ((hx.pair hl).pair hi).comp
    (fp_splitIncreasing (ea.prod BitEncoding.nat) (fun a t => oriented (p a.1) a.2 t)
      (fp_oriented ea p d hd hc))

/-- Degree is fixed program data. Every recursive search and list traversal is
compiled from the concrete predicate and list machines. -/
theorem fp_partition {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) :
    FP (ea.prod intervalEncoding) intervalEncoding.list
      (fun a => partition d (p a.1) a.2.1 a.2.2) := by
  induction d generalizing p with
  | zero => exact fp_singleton _ intervalEncoding _ (fp_snd ea intervalEncoding)
  | succ d ih =>
    have hp := ih (fun a => difference (p a))
      (fun a => degree_difference_le (p a) d (hd a))
      (fp_difference_coeff ea p (d+1) hd hc)
    have hm := ListContextMachines.fp_mapWithContext ea intervalEncoding intervalEncoding.list
      (fun a => split (p a.1) a.2) (fp_split ea p (d+1) hd hc)
    exact (((((fp_fst ea intervalEncoding).pair hp).comp hm).comp
      (ListFlattenMachines.fp_flatten intervalEncoding))).congr (fun a => by
        simp only [partition, List.flatMap, Function.comp_apply])

end PlanarHom.PolynomialDiscretePartitionMachines
