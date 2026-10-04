import PlanarHom.RoutingStageProgram
import PlanarHom.ListDropMachines
import PlanarHom.ListReverseMachines
import PlanarHom.ListContextMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.BinaryMultiplicationMachine

/-! Concrete binary codecs and actual elementary machines used by the whole
routing compiler. All widths are unary and all references are binary. -/
namespace PlanarHom.PositiveBlockProgram
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

def Kind.code : Kind → Bool × Bool
  | .wire => (false,false)
  | .cross => (false,true)
  | .fan => (true,false)
  | .test => (true,true)

def Kind.fromCode (p : Bool × Bool) : Kind :=
  if p.1 then if p.2 then .test else .fan else if p.2 then .cross else .wire

def kindEncoding : BitEncoding Kind :=
  (BitEncoding.bool.prod BitEncoding.bool).retract Kind.code Kind.fromCode (by intro k; cases k <;> rfl)

def referenceEncoding : BitEncoding (ℕ × ℕ × ℕ) := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
def instructionEncoding : BitEncoding Instruction := kindEncoding.prod referenceEncoding

def Stage.code : Stage → ℕ × ℕ
  | .swap i => (0,i)
  | .copy i => (1,i)
  | .check n => (2,n)

def Stage.fromCode (p : ℕ × ℕ) : Stage := if p.1=0 then .swap p.2 else if p.1=1 then .copy p.2 else .check p.2

def stageEncoding : BitEncoding Stage :=
  (BitEncoding.nat.prod BitEncoding.nat).retract Stage.code Stage.fromCode (by intro s; cases s <;> rfl)

def layerPartsEncoding : BitEncoding (ℕ × (List ℕ × List Instruction)) :=
  BitEncoding.unaryNat.prod (BitEncoding.nat.list.prod instructionEncoding.list)

def layerEncoding : BitEncoding LayerResult := layerPartsEncoding.retract
  (fun r => (r.variableCount,(r.rails,r.instructions)))
  (fun p => ⟨p.1,p.2.1,p.2.2⟩) (by intro r; cases r; rfl)

theorem fp_layerParts : FP layerEncoding layerPartsEncoding
    (fun r => (r.variableCount,(r.rails,r.instructions))) := fp_code_view _ _ _ (fun _ => rfl)

theorem fp_layerBuild : FP layerPartsEncoding layerEncoding (fun p => ⟨p.1,p.2.1,p.2.2⟩) :=
  fp_code_view _ _ _ (fun _ => rfl)

theorem fp_layerCount : FP layerEncoding BitEncoding.unaryNat LayerResult.variableCount :=
  fp_layerParts.comp (fp_fst _ _)

theorem fp_layerRails : FP layerEncoding BitEncoding.nat.list LayerResult.rails :=
  fp_layerParts.comp ((fp_snd _ _).comp (fp_fst _ _))

theorem fp_layerInstructions : FP layerEncoding instructionEncoding.list LayerResult.instructions :=
  fp_layerParts.comp ((fp_snd _ _).comp (fp_snd _ _))

theorem fp_singleton {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B) (f : A → B) (hf : FP ea eb f) :
    FP ea eb.list (fun x => [f x]) :=
  (hf.pair (fp_const ea eb.list [])).comp (ListMutationMachines.fp_cons eb)

theorem fp_kindCode : FP kindEncoding (BitEncoding.bool.prod BitEncoding.bool) Kind.code :=
  fp_code_view _ _ _ (fun _ => rfl)

theorem fp_stageCode : FP stageEncoding (BitEncoding.nat.prod BitEncoding.nat) Stage.code :=
  fp_code_view _ _ _ (fun _ => rfl)

theorem fp_swapStage : FP BitEncoding.nat stageEncoding Stage.swap :=
  ((fp_const BitEncoding.nat BitEncoding.nat 0).pair (fp_id BitEncoding.nat)).transportOutput (fun _ => rfl)

theorem fp_copyStage : FP BitEncoding.nat stageEncoding Stage.copy :=
  ((fp_const BitEncoding.nat BitEncoding.nat 1).pair (fp_id BitEncoding.nat)).transportOutput (fun _ => rfl)

theorem fp_checkStage : FP BitEncoding.nat stageEncoding Stage.check :=
  ((fp_const BitEncoding.nat BitEncoding.nat 2).pair (fp_id BitEncoding.nat)).transportOutput (fun _ => rfl)

theorem fp_wire : FP BitEncoding.nat instructionEncoding wire :=
  (fp_const BitEncoding.nat kindEncoding .wire).pair
    ((fp_id BitEncoding.nat).pair ((fp_const _ BitEncoding.nat 0).pair (fp_const _ BitEncoding.nat 0)))

theorem fp_fan : FP BitEncoding.nat instructionEncoding fan :=
  (fp_const BitEncoding.nat kindEncoding .fan).pair
    ((fp_id BitEncoding.nat).pair ((fp_const _ BitEncoding.nat 0).pair (fp_const _ BitEncoding.nat 0)))

theorem fp_crossing : FP (BitEncoding.nat.prod BitEncoding.nat) instructionEncoding
    (fun p => crossing p.1 p.2) :=
  (fp_const _ kindEncoding .cross).pair ((fp_snd _ _).pair ((fp_fst _ _).pair (fp_const _ BitEncoding.nat 0)))

theorem fp_test : FP referenceEncoding instructionEncoding (fun p => test p.1 p.2.1 p.2.2) :=
  (fp_const referenceEncoding kindEncoding .test).pair (fp_id referenceEncoding)

theorem fp_wireProgram : FP BitEncoding.nat.list instructionEncoding.list wireProgram :=
  ListMapMachines.fp_map BitEncoding.nat instructionEncoding wire fp_wire

/-- Dynamic binary prefix selection by genuine reverse/drop/reverse machines. -/
theorem fp_take {A : Type} (e : BitEncoding A) (d : A) :
    FP (BitEncoding.nat.prod e.list) e.list (fun p => p.2.take p.1) := by
  have hi := fp_fst BitEncoding.nat e.list
  have hs := fp_snd BitEncoding.nat e.list
  have hn := (hs.comp (ListUnaryLengthMachine.fp_length e)).comp UnaryNatConversionMachine.fp_conversion
  have hd := (hn.pair hi).comp BinaryArithmetic.fp_subtraction
  have hr := hs.comp (ListReverseMachines.fp_reverse e)
  have h := ((hd.pair hr).comp (ListDropMachines.fp_drop e d)).comp (ListReverseMachines.fp_reverse e)
  exact h.congr (fun p => by change (p.2.reverse.drop (p.2.length-p.1)).reverse=p.2.take p.1; rw [←List.reverse_take,List.reverse_reverse])

theorem fp_getRef : FP (BitEncoding.nat.list.prod BitEncoding.nat) BitEncoding.nat (fun p => getRef p.1 p.2) := by
  have hs := fp_fst BitEncoding.nat.list BitEncoding.nat
  have hi := fp_snd BitEncoding.nat.list BitEncoding.nat
  have h := ((hi.pair hs).comp (ListDropMachines.fp_drop BitEncoding.nat 0)).comp
    (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  exact h.congr (fun p => by
    change (p.1.drop p.2).headD 0=p.1[p.2]?.getD 0
    rw [List.headD_eq_head?_getD,List.head?_drop])

theorem fp_range : FP BitEncoding.unaryNat BitEncoding.nat.list List.range :=
  (UnaryRangeMachines.fp_range.comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
    (fun n => by simp)

theorem wireRails_range (m : ℕ) (rs : List ℕ) : wireRails m rs=(List.range rs.length).map (fun i => m+6*i) := by
  induction rs generalizing m with
  | nil => rfl
  | cons a rs ih =>
    rw [wireRails,ih,List.length_cons,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.mul_zero,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    omega

/-- Fresh wire addresses are generated by an honestly unary range plus binary
constant multiplication/addition, including their actual list framing. -/
theorem fp_wireRails : FP (BitEncoding.unaryNat.prod BitEncoding.nat.list) BitEncoding.nat.list
    (fun p => wireRails p.1 p.2) := by
  have hm := (fp_fst BitEncoding.unaryNat BitEncoding.nat.list).comp UnaryNatConversionMachine.fp_conversion
  have hs := fp_snd BitEncoding.unaryNat BitEncoding.nat.list
  have hi := (hs.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)).comp fp_range
  have body : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.nat (fun p : ℕ × ℕ => p.1+6*p.2) := by
    have hx := fp_fst BitEncoding.nat BitEncoding.nat
    have hj := fp_snd BitEncoding.nat BitEncoding.nat
    exact (hx.pair (((fp_const _ BitEncoding.nat 6).pair hj).comp BinaryArithmetic.fp_multiplication)).comp
      BinaryArithmetic.fp_addition
  exact ((hm.pair hi).comp (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat BitEncoding.nat
    (fun p => p.1+6*p.2) body)).congr (fun p => (wireRails_range p.1 p.2).symm)

/-- Full passive routing layer, with an actual unary header. -/
theorem fp_passive : FP (BitEncoding.unaryNat.prod BitEncoding.nat.list) layerEncoding (fun p => passive p.1 p.2) := by
  have hm := fp_fst BitEncoding.unaryNat BitEncoding.nat.list
  have hs := fp_snd BitEncoding.unaryNat BitEncoding.nat.list
  have hl := hs.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)
  have hsix := ((fp_const _ BitEncoding.unaryNat 6).pair hl).comp UnaryPolynomialMachines.fp_mul
  have hcount := (hm.pair hsix).comp UnaryPolynomialMachines.fp_add
  exact (hcount.pair (fp_wireRails.pair (hs.comp fp_wireProgram))).comp fp_layerBuild

end PlanarHom.PositiveBlockProgram
