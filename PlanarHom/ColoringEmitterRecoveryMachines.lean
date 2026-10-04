import PlanarHom.ColoringEmitterMachines
import PlanarHom.GraphComponentMachines
import PlanarHom.BinaryDivisionMachine
import PlanarHom.RestrictedIterationMachine

/-! NEW actual single-query recovery: component extraction, fixed-base natural
powers, binary division and multiplication. Missing answers use zero explicitly. -/
noncomputable section
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram PairProjectionMachines ArithmeticCircuitPrimitives
open ParsimoniousNorOneInThree

theorem nat_mul_code_bound (m n : ℕ) :
    (BitEncoding.nat.encode (m*n)).length≤(BitEncoding.nat.encode m).length+(BitEncoding.nat.encode n).length := by
  change (Computability.encodeNat (m*n)).length≤(Computability.encodeNat m).length+(Computability.encodeNat n).length
  rw [←BinaryArithmetic.mulBits_encodeNat]
  exact BinaryArithmetic.mulBits_length_le _ _

theorem nat_pow_code_bound (c n : ℕ) :
    (BitEncoding.nat.encode (c^n)).length≤n*(BitEncoding.nat.encode c).length+1 := by
  induction n with
  | zero => simpa using (Complexity.encodeNat_length_le 1)
  | succ n ih =>
    rw [pow_succ]
    have hh:=nat_mul_code_bound (c^n) c
    simp only [Nat.succ_mul]
    omega

theorem multiply_iterate (c n : ℕ) : (fun x:ℕ=>x*c)^[n] 1=c^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,pow_succ]

theorem fp_fixedNatPower (c : ℕ) : FP BitEncoding.unaryNat BitEncoding.nat (fun n=>c^n) := by
  have hbody : FP BitEncoding.nat BitEncoding.nat (fun x=>x*c) :=
    ((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat c)).comp BinaryArithmetic.fp_multiplication
  let p:Polynomial ℕ := Polynomial.C (BitEncoding.nat.encode c).length*Polynomial.X+1
  have hb : ∀n i,i≤n→(BitEncoding.nat.encode ((fun x:ℕ=>x*c)^[i] 1)).length≤p.eval n := by
    intro n i hi
    rw [multiply_iterate]
    have hh:=nat_pow_code_bound c i
    have hm:=Nat.mul_le_mul_right (BitEncoding.nat.encode c).length hi
    simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith only [hh,hm]
  have hf : FP BitEncoding.unaryNat BitEncoding.nat (fun n=>(fun x:ℕ=>x*c)^[n] 1) :=
    ⟨BoundedIterationMachine.fromSeedComputer BitEncoding.nat (fun x=>x*c) 1 (Classical.choice hbody) p hb⟩
  exact hf.congr (fun n=>multiply_iterate c n)

def componentCount (f : NumericFormula) : ℕ := (GraphComponentCode.components (compile f)).length

def queries (f : NumericFormula) : List MixedCode := [compile f]

def recover (p : NumericFormula × List ℕ) : ℕ :=
  2^unusedOriginal p.1 * (p.2.headD 0 / 6^componentCount p.1)

theorem fp_componentCount : FP formulaEncoding BitEncoding.unaryNat componentCount :=
  (fp_compile.comp GraphComponentMachines.fp_components).comp
    (ListUnaryLengthMachine.fp_length MixedCode.encoding)

theorem fp_queries : FP formulaEncoding MixedCode.encoding.list queries :=
  PositiveBlockProgram.fp_singleton formulaEncoding MixedCode.encoding compile fp_compile

theorem fp_recover : FP (formulaEncoding.prod BitEncoding.nat.list) BitEncoding.nat recover := by
  have hf:=fp_fst formulaEncoding BitEncoding.nat.list
  have hans:=(fp_snd formulaEncoding BitEncoding.nat.list).comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  have htwo:=(hf.comp fp_unusedOriginal).comp (fp_fixedNatPower 2)
  have hsix:=(hf.comp fp_componentCount).comp (fp_fixedNatPower 6)
  have hdiv:=((hans.pair hsix).comp BinaryArithmetic.fp_division).comp (fp_fst BitEncoding.nat BitEncoding.nat)
  exact (htwo.pair hdiv).comp BinaryArithmetic.fp_multiplication

end PlanarHom.ColoringEmitter
