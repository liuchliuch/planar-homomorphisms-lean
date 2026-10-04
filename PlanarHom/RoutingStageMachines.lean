import PlanarHom.RoutingLayerMachines
import PlanarHom.RoutingScriptMachines
import PlanarHom.NatListSumMachines

/-! Actual typed machines for one routing-stage transition and accumulation of
its full materialized instruction list. -/
namespace PlanarHom.PositiveBlockProgram
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def stageInputEncoding : BitEncoding (Stage × (ℕ × List ℕ)) :=
  stageEncoding.prod (BitEncoding.unaryNat.prod BitEncoding.nat.list)

theorem fp_stageRender : FP stageInputEncoding layerEncoding (fun p => p.1.render p.2.1 p.2.2) := by
  have hs := fp_fst stageEncoding (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have hstate := fp_snd stageEncoding (BitEncoding.unaryNat.prod BitEncoding.nat.list)
  have hm := hstate.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat.list)
  have hr := hstate.comp (fp_snd BitEncoding.unaryNat BitEncoding.nat.list)
  have hc := hs.comp fp_stageCode
  have htag := hc.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi := hc.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hp := hm.pair (hi.pair hr)
  have ht0 := (htag.pair (fp_const _ BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have ht1 := (htag.pair (fp_const _ BitEncoding.nat 1)).comp NatListSumMachines.fp_equal
  have hrest := ht1.ite (hp.comp fp_copyLayer) (hp.comp fp_checkLayer)
  exact (ht0.ite (hp.comp fp_swapLayer) hrest).congr (fun p => by rcases p with ⟨s,m,rs⟩; cases s <;> rfl)

theorem fp_then : FP (layerEncoding.prod layerEncoding) layerEncoding (fun p => p.1.then p.2) := by
  have ha := fp_fst layerEncoding layerEncoding
  have hb := fp_snd layerEncoding layerEncoding
  have hm := hb.comp fp_layerCount
  have hr := hb.comp fp_layerRails
  have hc := ((ha.comp fp_layerInstructions).pair (hb.comp fp_layerInstructions)).comp
    (ListMutationMachines.fp_append instructionEncoding)
  exact (hm.pair (hr.pair hc)).comp fp_layerBuild

def advance (r : LayerResult) (s : Stage) : LayerResult := r.then (s.render r.variableCount r.rails)

theorem fp_advance : FP (layerEncoding.prod stageEncoding) layerEncoding (fun p => advance p.1 p.2) := by
  have hr := fp_fst layerEncoding stageEncoding
  have hs := fp_snd layerEncoding stageEncoding
  have hstate := (hr.comp fp_layerCount).pair (hr.comp fp_layerRails)
  have hnext := (hs.pair hstate).comp fp_stageRender
  exact (hr.pair hnext).comp fp_then

theorem fold_advance (ss : List Stage) (r : LayerResult) :
    ss.foldl advance r=r.then (stages r.variableCount r.rails ss) := by
  induction ss generalizing r with
  | nil => cases r; simp [LayerResult.then,stages,LayerResult.identity]
  | cons s ss ih =>
    rw [List.foldl_cons,ih]
    simp only [advance,stages,LayerResult.then_assoc]
    rfl

theorem fold_advance_initial (n : ℕ) (ss : List Stage) :
    ss.foldl advance (.identity n (List.range n))=stages n (List.range n) ss := by
  rw [fold_advance]
  simp [LayerResult.identity,LayerResult.then]

end PlanarHom.PositiveBlockProgram
