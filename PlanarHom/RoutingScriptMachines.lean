import PlanarHom.RoutingMachinePrimitives
import PlanarHom.ListFlattenMachines

/-! Real polynomial-time emission of the entire explicit move-copy-restore
stage script, on all typed inputs including invalid source references. -/
namespace PlanarHom.PositiveBlockProgram
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ParsimoniousNorOneInThree AdjacentRailRouting

def copyInputEncoding : BitEncoding (ℕ × ℕ) := BitEncoding.unaryNat.prod BitEncoding.nat

theorem moveScript_range (start steps : ℕ) : moveScript start steps=(List.range steps).map (fun i => start+i) := by
  induction steps generalizing start with
  | zero => rfl
  | succ steps ih =>
    rw [moveScript,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    omega

theorem fp_moveScript : FP copyInputEncoding BitEncoding.nat.list
    (fun p => moveScript p.2 (p.1-1-p.2)) := by
  have hn := fp_fst BitEncoding.unaryNat BitEncoding.nat
  have hi := fp_snd BitEncoding.unaryNat BitEncoding.nat
  have hnb := hn.comp UnaryNatConversionMachine.fp_conversion
  have hn1 := (hnb.pair (fp_const copyInputEncoding BitEncoding.nat 1)).comp BinaryArithmetic.fp_subtraction
  have hd := (hn1.pair hi).comp BinaryArithmetic.fp_subtraction
  have hbound : FP copyInputEncoding BitEncoding.unaryNat (fun p : ℕ × ℕ => p.1-1-p.2) :=
    ((hn.pair hd).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p : ℕ × ℕ => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)).congr
        (fun p => by change min p.1 (p.1-1-p.2)=_; omega)
  have hr := hbound.comp fp_range
  exact ((hi.pair hr).comp (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat BitEncoding.nat
    (fun p : ℕ × ℕ => p.1+p.2) BinaryArithmetic.fp_addition)).congr
      (fun p => (moveScript_range p.2 (p.1-1-p.2)).symm)

theorem fp_copyStages : FP copyInputEncoding stageEncoding.list (fun p => copyStages p.1 p.2) := by
  have hn := fp_fst BitEncoding.unaryNat BitEncoding.nat
  have hi := fp_snd BitEncoding.unaryNat BitEncoding.nat
  have hnb := hn.comp UnaryNatConversionMachine.fp_conversion
  have ht := (hi.pair hnb).comp BinaryArithmetic.fp_comparison
  have hn1 := (hnb.pair (fp_const copyInputEncoding BitEncoding.nat 1)).comp BinaryArithmetic.fp_subtraction
  have swaps := fp_moveScript.comp (ListMapMachines.fp_map BitEncoding.nat stageEncoding Stage.swap fp_swapStage)
  have copy := fp_singleton copyInputEncoding stageEncoding _ (hn1.comp fp_copyStage)
  have reverse := swaps.comp (ListReverseMachines.fp_reverse stageEncoding)
  have hfirst := (swaps.pair copy).comp (ListMutationMachines.fp_append stageEncoding)
  have hall := (hfirst.pair reverse).comp (ListMutationMachines.fp_append stageEncoding)
  exact (ht.ite hall (fp_const copyInputEncoding stageEncoding.list [])).congr (fun p => by
    change (if p.2<p.1 then _ else [])=copyStages p.1 p.2
    simp [copyStages,List.map_reverse])

def clauseInputEncoding : BitEncoding (ℕ × Clause ℕ) := BitEncoding.unaryNat.prod clauseEncoding

theorem fp_clauseStages : FP clauseInputEncoding stageEncoding.list (fun p => clauseStages p.1 p.2) := by
  have hn := fp_fst BitEncoding.unaryNat clauseEncoding
  have hc := fp_snd BitEncoding.unaryNat clauseEncoding
  have hx := hc.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hyz := hc.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hy := hyz.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hz := hyz.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hx' := (hn.pair hx).comp fp_copyStages
  have hy' := (hn.pair hy).comp fp_copyStages
  have hz' := (hn.pair hz).comp fp_copyStages
  have hxy := (hx'.pair hy').comp (ListMutationMachines.fp_append stageEncoding)
  have hxyz := (hxy.pair hz').comp (ListMutationMachines.fp_append stageEncoding)
  have hcheck := fp_singleton clauseInputEncoding stageEncoding _
    ((hn.comp UnaryNatConversionMachine.fp_conversion).comp fp_checkStage)
  exact ((hxyz.pair hcheck).comp (ListMutationMachines.fp_append stageEncoding)).congr
    (fun p => by simp [clauseStages,gatherStages,List.append_assoc])

/-- Every source clause's stage list is physically emitted and flattened. -/
theorem fp_formulaStages : FP formulaEncoding stageEncoding.list (fun f => formulaStages f.1 f.2) := by
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat clauseEncoding stageEncoding.list
    (fun p => clauseStages p.1 p.2) fp_clauseStages
  exact (hm.comp (ListFlattenMachines.fp_flatten stageEncoding)).congr
    (fun p => by
      change (p.2.map (clauseStages p.1)).flatten=p.2.flatMap (clauseStages p.1)
      rfl)

theorem fp_initialLayer : FP BitEncoding.unaryNat layerEncoding (fun n => LayerResult.identity n (List.range n)) :=
  ((fp_id BitEncoding.unaryNat).pair (fp_range.pair (fp_const BitEncoding.unaryNat instructionEncoding.list []))).comp fp_layerBuild

end PlanarHom.PositiveBlockProgram
