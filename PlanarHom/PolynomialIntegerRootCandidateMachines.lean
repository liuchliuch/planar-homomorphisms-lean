import PlanarHom.PolynomialIntegerRootCandidates
import PlanarHom.DiscreteSignPartitionMachines

/-! # Actual polynomial-time bounded integer-root candidate enumeration

The candidate list has a degree-dependent constant bound, even when the input
integer interval is exponentially large. All sign partitions and binary searches
are executed by the concrete machines compiled in the imported modules.
-/

noncomputable section
namespace PlanarHom.PolynomialIntegerRootCandidateMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives BinaryArithmetic
open DiscreteSignPartitionMachines PolynomialIntegerRootCandidates

theorem fp_intervalCandidates (d : ℕ) :
    FP intervalEncoding BitEncoding.nat.list
      (fun I => (List.range d).map (fun j => I.1+j)) := by
  have hc := (fp_fst BitEncoding.nat BitEncoding.nat).pair
    (fp_const intervalEncoding BitEncoding.nat.list (List.range d))
  exact hc.comp (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat
    BitEncoding.nat (fun p => p.1+p.2) fp_addition)

/-- Full concrete machine for a fixed-degree polynomial family whose rational
coefficients are computed by actual FP machines. -/
theorem fp_candidates {α : Type} (ea : BitEncoding α) (p : α → Polynomial ℚ) (d : ℕ)
    (hd : ∀ a, (p a).natDegree ≤ d)
    (hc : ∀ k, FP ea BitEncoding.rat (fun a => (p a).coeff k)) :
    FP (ea.prod intervalEncoding) BitEncoding.nat.list
      (fun a => candidates d (p a.1) a.2.1 a.2.2) := by
  have hp := PolynomialDiscretePartitionMachines.fp_partition ea p d hd hc
  have hm := ListMapMachines.fp_map intervalEncoding BitEncoding.nat.list
    (fun I => (List.range d).map (fun j => I.1+j)) (fp_intervalCandidates d)
  exact ((hp.comp hm).comp (ListFlattenMachines.fp_flatten BitEncoding.nat)).congr
    (fun a => by simp only [candidates, List.flatMap, Function.comp_apply])

end PlanarHom.PolynomialIntegerRootCandidateMachines
