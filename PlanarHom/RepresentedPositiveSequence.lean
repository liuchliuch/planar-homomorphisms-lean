import PlanarHom.GraphInterpolationQueries

/-! Actual generic batching at explicitly unary exponents 1,...,N. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity PairProjectionMachines

def positiveSequence {A B:Type} (f:ℕ→A→B) (p:ℕ×A) : List B :=
  (List.range p.1).map (fun i=>f (i+1) p.2)

theorem fp_positiveSequence {A B:Type} (ea:BitEncoding A) (eb:BitEncoding B)
    (f:ℕ→A→B) (hf:FP (BitEncoding.unaryNat.prod ea) eb (fun p=>f p.1 p.2)) :
    FP (BitEncoding.unaryNat.prod ea) eb.list (positiveSequence f) := by
  let input:=BitEncoding.unaryNat.prod ea
  have hc:=fp_fst input BitEncoding.nat
  have hi:=fp_snd input BitEncoding.nat
  have hn:=hc.comp (fp_fst BitEncoding.unaryNat ea)
  have ha:=hc.comp (fp_snd BitEncoding.unaryNat ea)
  have hs:=hi.comp BinaryArithmetic.fp_successor
  have he:=(hn.pair hs).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p=>min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  have body:=(he.pair ha).comp hf
  have hm:=ListContextMachines.fp_mapWithContext input BitEncoding.nat eb
    (fun p=>f (min p.1.1 (p.2+1)) p.1.2) body
  have hrange:= (UnaryRangeMachines.fp_range.comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)).congr (fun n=>List.reverse_reverse (List.range n))
  have hr:=(fp_fst BitEncoding.unaryNat ea).comp hrange
  apply (((fp_id input).pair hr).comp hm).congr
  intro p
  apply List.map_congr_left
  intro i hi
  change f (min p.1 (i+1)) p.2=f (i+1) p.2
  rw [min_eq_right (by have h:=List.mem_range.mp hi; omega)]

end PlanarHom.RepresentedBit
