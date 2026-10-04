import PlanarHom.RationalMultiplicationMachine
import PlanarHom.MachineCodeTransport
import PlanarHom.ConstantMachines
import PlanarHom.PairProjectionMachines

/-! # Actual finite Boolean gates and exact codec views for arithmetic circuits -/
namespace PlanarHom.Complexity
open Turing Turing.TM2

/-- Extensional replacement does not change the machine or its cost. -/
theorem FP.congr {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β} {f g : α→β}
    (hf : FP ea eb f) (h : ∀ a, f a=g a) : FP ea eb g := by
  have he : f=g := funext h
  rw [←he]
  exact hf

/-- Literal codeword identity is realized by the identity TM2. -/
theorem fp_code_view {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β)
    (view : α→β) (same : ∀ a, eb.encode (view a)=ea.encode a) : FP ea eb view := by
  simpa only [Function.id_comp] using FP.transportInput view same (fp_id eb)

end PlanarHom.Complexity

namespace PlanarHom.ArithmeticCircuitPrimitives
open Turing Turing.TM2 Complexity BinaryArithmetic

theorem update_unit (S : Unit→Bits) (w : Bits) : Function.update S () w = (fun _ => w) := by
  funext k; cases k; rfl

/-- A fixed truth table selects one of two statically compiled output words. -/
def unaryMachine {β : Type} (eb : BitEncoding β) (f : Bool→β) : FinTM2 where
  K := Unit
  Γ _ := Bool
  k₀ := ()
  k₁ := ()
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := .pop () (fun _ b => b) <| .branch (fun v => v.getD false)
    (.load (fun _ => none) (ConstantMachines.pushWord (eb.encode (f true)) .halt))
    (.load (fun _ => none) (ConstantMachines.pushWord (eb.encode (f false)) .halt))

theorem unary_step {β : Type} (eb : BitEncoding β) (f : Bool→β) (b : Bool) :
    (unaryMachine eb f).step (initList (unaryMachine eb f) [b]) =
      some (haltList (unaryMachine eb f) (eb.encode (f b))) := by
  cases b <;>
    simp [unaryMachine,initList,haltList,step,stepAux,update_unit,ConstantMachines.pushWord_correct]

noncomputable def unaryComputer {β : Type} (eb : BitEncoding β) (f : Bool→β) :
    TM2ComputableInPolyTime BitEncoding.bool.toFinEncoding eb.toFinEncoding f where
  tm := unaryMachine eb f
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun b := by
    simpa [BitEncoding.toFinEncoding,BitEncoding.bool,Equiv.refl] using
      oneStep (unaryMachine eb f).step (unary_step eb f b)

theorem fp_bool_unary {β : Type} (eb : BitEncoding β) (f : Bool→β) :
    FP BitEncoding.bool eb f := ⟨unaryComputer eb f⟩

/-- Four input symbols encode a Boolean pair; one finite transition consumes all. -/
def gateMachine (f : Bool×Bool→Bool) : FinTM2 where
  K := Unit
  Γ _ := Bool
  k₀ := ()
  k₁ := ()
  Λ := Unit
  main := ()
  σ := Bool×Bool
  initialState := (false,false)
  m _ := .pop () (fun v _ => v) <| .pop () (fun v b => (b.getD false,v.2)) <|
    .pop () (fun v _ => v) <| .pop () (fun v b => (v.1,b.getD false)) <|
    .push () f (.load (fun _ => (false,false)) .halt)

theorem gate_step (f : Bool×Bool→Bool) (a b : Bool) :
    (gateMachine f).step (initList (gateMachine f) [true,a,false,b]) =
      some (haltList (gateMachine f) [f (a,b)]) := by
  simp [gateMachine,initList,haltList,step,stepAux,update_unit]

noncomputable def gateComputer (f : Bool×Bool→Bool) :
    TM2ComputableInPolyTime (BitEncoding.bool.prod BitEncoding.bool).toFinEncoding
      BitEncoding.bool.toFinEncoding f where
  tm := gateMachine f
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun p := by
    simpa [BitEncoding.toFinEncoding,BitEncoding.prod,BitEncoding.bool,BitEncoding.frame,Equiv.refl] using
      oneStep (gateMachine f).step (gate_step f p.1 p.2)

theorem fp_bool_gate (f : Bool×Bool→Bool) :
    FP (BitEncoding.bool.prod BitEncoding.bool) BitEncoding.bool f := ⟨gateComputer f⟩

def intParts : ℤ→Bool×ℕ
  | .ofNat n => (false,n)
  | .negSucc n => (true,n)

theorem fp_int_parts : FP BitEncoding.int (BitEncoding.bool.prod BitEncoding.nat) intParts :=
  fp_code_view _ _ _ (by intro z; cases z <;> rfl)

theorem fp_parts_int : FP (BitEncoding.bool.prod BitEncoding.nat) BitEncoding.int
    (fun p => signedIndex p.1 p.2) :=
  fp_code_view _ _ _ (by rintro ⟨s,n⟩; cases s <;> rfl)

theorem fp_nat_int : FP BitEncoding.nat BitEncoding.int (fun n : ℕ => (n : ℤ)) := by
  exact ((fp_const BitEncoding.nat BitEncoding.bool false).pair (fp_id BitEncoding.nat)).comp fp_parts_int

theorem fp_rat_parts : FP BitEncoding.rat (BitEncoding.int.prod BitEncoding.nat)
    (fun q => (q.num,q.den)) := fp_code_view _ _ _ (by intro q; rfl)

theorem fp_rat_num : FP BitEncoding.rat BitEncoding.int Rat.num :=
  fp_rat_parts.comp (PairProjectionMachines.fp_fst _ _)

theorem fp_rat_den : FP BitEncoding.rat BitEncoding.nat Rat.den :=
  fp_rat_parts.comp (PairProjectionMachines.fp_snd _ _)

theorem fp_int_rat : FP BitEncoding.int BitEncoding.rat (fun z : ℤ => (z : ℚ)) := by
  exact (((fp_id BitEncoding.int).pair (fp_const BitEncoding.int BitEncoding.nat 1)).comp
    fp_rational_normalization).congr (fun z => Rat.mkRat_one z)

/-- Integral multiplication through the already verified canonical rational multiplier. -/
theorem fp_int_mul : FP (BitEncoding.int.prod BitEncoding.int) BitEncoding.int
    (fun p : ℤ×ℤ => p.1*p.2) := by
  exact (((fp_int_rat.prodMap fp_int_rat).comp fp_rational_multiplication).comp fp_rat_num).congr
    (fun p => by simp only [Function.comp_def,Prod.map,←Rat.intCast_mul,Rat.num_intCast])

theorem fp_int_natAbs : FP BitEncoding.int BitEncoding.nat Int.natAbs := by
  have hs := fp_int_parts.comp (PairProjectionMachines.fp_fst _ _)
  have hn := fp_int_parts.comp (PairProjectionMachines.fp_snd _ _)
  have hb := hs.comp (fp_bool_unary BitEncoding.nat (fun s => if s then 1 else 0))
  exact ((hn.pair hb).comp fp_addition).congr (fun z => by cases z <;> rfl)

end PlanarHom.ArithmeticCircuitPrimitives
