import PlanarHom.ListContextFilterMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.ListContextMachines
import PlanarHom.ListFlattenMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.NatListSumMachines
import PlanarHom.RootedHomogeneousSemantics
import PlanarHom.RankOne

/-! Actual incidence degree extraction. Every edge contributes both ends,
so loops contribute twice and parallel occurrences remain distinct. -/
namespace PlanarHom.GraphDegreeMachines
open Complexity Complexity.MixedCode PairProjectionMachines

def endpoints (es : List (ℕ×ℕ×ℕ)) : List ℕ := es.flatMap (fun e=>[e.1,e.2.1])
def degree (g : MixedCode) (v : ℕ) : ℕ := ((endpoints g.edges).filter (fun x=>decide (x=v))).length
def degrees (g : MixedCode) : List ℕ := (List.range g.vertices).reverse.map (degree g)

theorem fp_endpoints : FP MixedCode.edgeEncoding BitEncoding.nat.list endpoints := by
  let edge := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
  have hs := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have ht := (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hone := (ht.pair (fp_const edge BitEncoding.nat.list [])).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have htwo := (hs.pair hone).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  exact ((ListMapMachines.fp_map edge BitEncoding.nat.list _ htwo).comp
    (ListFlattenMachines.fp_flatten BitEncoding.nat)).congr (fun es=>by
      induction es with
      | nil => rfl
      | cons e es ih => simpa [endpoints,List.flatMap_cons,Function.comp_def] using congrArg (fun xs=>e.1::e.2.1::xs) ih)

theorem fp_count : FP (BitEncoding.nat.list.prod BitEncoding.nat) BitEncoding.unaryNat
    (fun p : List ℕ×ℕ=>(p.1.filter (fun x=>decide (x=p.2))).length) := by
  have hp : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.bool
      (fun p : ℕ×ℕ=>decide (p.2=p.1)) := NatListSumMachines.fp_equal.congr (fun p=>by simp [eq_comm])
  have hc := ((fp_snd BitEncoding.nat.list BitEncoding.nat).pair
      (fp_fst BitEncoding.nat.list BitEncoding.nat)).comp
    (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat BitEncoding.nat _ hp)
  exact hc.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)

theorem fp_degrees : FP encoding BitEncoding.unaryNat.list degrees := by
  have he := MixedCode.fp_edges.comp fp_endpoints
  have hv := MixedCode.fp_vertices.comp UnaryRangeMachines.fp_range
  exact (he.pair hv).comp (ListContextMachines.fp_mapWithContext
    BitEncoding.nat.list BitEncoding.nat BitEncoding.unaryNat _ fp_count)

end PlanarHom.GraphDegreeMachines
