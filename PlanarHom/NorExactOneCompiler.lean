import PlanarHom.ParsimoniousNorNumericNetwork
import PlanarHom.ConditionalMachines
import PlanarHom.BinarySubtractionMachine
import PlanarHom.ListFoldMachines

/-! A literal serialized positive exactly-one formula compiler. All references,
including future or out-of-range NOR reads, are normalized to the fixed false
register before the actual three-clause gadget is materialized. -/
namespace PlanarHom.NorExactOne
open Complexity CountingCookLevin ParsimoniousNorOneInThree
open PairProjectionMachines ArithmeticCircuitPrimitives

/-- Three clauses fix `t` true and the fresh variables `m,m+1,m+2` false. -/
def pin (m t : ℕ) : Formula ℕ := [(t,m+1,m),(t,m+2,m),(m+1,t,m+2)]
def ground (n : ℕ) : NumericFormula := (n+4,pin (n+1) n)
abbrev State := ℕ × NumericFormula
def stateEncoding : BitEncoding State := BitEncoding.nat.prod formulaEncoding

def step (s : State) (g : ℕ × ℕ) : State :=
  (s.1,compileGate (s.2,(checkedRef s.2.1 s.1 g.1,checkedRef s.2.1 s.1 g.2)))

def finish (s : State) (output : ℕ) : NumericFormula :=
  (s.2.1+3,s.2.2++pin s.2.1 (checkedRef s.2.1 s.1 output))

def compile (p : CountingNorProgram.Program) : NumericFormula :=
  finish (p.2.1.foldl step (p.1+1,ground p.1)) p.2.2

@[simp] theorem pin_length (m t : ℕ) : (pin m t).length=3 := rfl
@[simp] theorem network_length (n z : ℕ) (gs : NorGates) :
    (network n z gs).length=3*gs.length := by
  induction gs generalizing n with
  | nil => simp [network]
  | cons g gs ih => rcases g with ⟨x,y⟩; simp [network,numericGate,ih]; omega

/-- This identifies the exact list produced by the operational accumulator. -/
theorem fold_step (gs : NorGates) (z m : ℕ) (f : Formula ℕ) :
    gs.foldl step (z,(m,f))=(z,(m+4*gs.length,f++network m z gs)) := by
  induction gs generalizing m f with
  | nil => simp [network]
  | cons g gs ih =>
    rcases g with ⟨x,y⟩
    simp only [List.foldl_cons,step,compileGate]
    rw [ih]
    simp only [network,List.length_cons,List.append_assoc]
    congr 2 <;> omega

@[simp] theorem compile_variables (p : CountingNorProgram.Program) :
    (compile p).1=p.1+4+4*p.2.1.length+3 := by simp [compile,ground,fold_step,finish]
@[simp] theorem compile_clauses (p : CountingNorProgram.Program) :
    (compile p).2=pin (p.1+1) p.1++network (p.1+4) (p.1+1) p.2.1++
      pin (p.1+4+4*p.2.1.length) (checkedRef (p.1+4+4*p.2.1.length) (p.1+1) p.2.2) := by
  simp [compile,ground,fold_step,finish]

private theorem fp_three {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (f g h : A → B) (hf : FP ea eb f) (hg : FP ea eb g) (hh : FP ea eb h) :
    FP ea eb.list (fun a => [f a,g a,h a]) := by
  exact (hf.pair ((hg.pair ((hh.pair (fp_const ea eb.list [])).comp
    (ListMutationMachines.fp_cons eb))).comp (ListMutationMachines.fp_cons eb))).comp
      (ListMutationMachines.fp_cons eb)

/-- Bounds checks are genuine binary comparison and conditional machines. -/
theorem fp_checkedRef : FP (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
    BitEncoding.nat (fun p => checkedRef p.1 p.2.1 p.2.2) := by
  have hn := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hzi := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hz := hzi.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi := hzi.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact ((hi.pair hn).comp BinaryArithmetic.fp_comparison).ite hi hz

theorem fp_pin : FP (BitEncoding.nat.prod BitEncoding.nat) clauseEncoding.list
    (fun p => pin p.1 p.2) := by
  have hm := fp_fst BitEncoding.nat BitEncoding.nat
  have ht := fp_snd BitEncoding.nat BitEncoding.nat
  have hoff (k : ℕ) := (hm.pair (fp_const _ BitEncoding.nat k)).comp BinaryArithmetic.fp_addition
  exact fp_three _ clauseEncoding _ _ _ (ht.pair ((hoff 1).pair hm))
    (ht.pair ((hoff 2).pair hm)) ((hoff 1).pair (ht.pair (hoff 2)))

theorem fp_ground : FP BitEncoding.unaryNat formulaEncoding ground := by
  have hn := UnaryNatConversionMachine.fp_conversion
  have hv := ((fp_id BitEncoding.unaryNat).pair (fp_const _ BitEncoding.unaryNat 4)).comp
    UnaryPolynomialMachines.fp_add
  have hm := (hn.pair (fp_const _ BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  exact hv.pair ((hm.pair hn).comp fp_pin)

theorem fp_step : FP (stateEncoding.prod gateEncoding) stateEncoding (fun p => step p.1 p.2) := by
  have hs := fp_fst stateEncoding gateEncoding
  have hg := fp_snd stateEncoding gateEncoding
  have hz := hs.comp (fp_fst BitEncoding.nat formulaEncoding)
  have hf := hs.comp (fp_snd BitEncoding.nat formulaEncoding)
  have hm := (hf.comp (fp_fst BitEncoding.unaryNat clauseEncoding.list)).comp UnaryNatConversionMachine.fp_conversion
  have hx := hg.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hy := hg.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hcx := (hm.pair (hz.pair hx)).comp fp_checkedRef
  have hcy := (hm.pair (hz.pair hy)).comp fp_checkedRef
  exact hz.pair ((hf.pair (hcx.pair hcy)).comp fp_compileGate)

theorem fp_finish : FP (stateEncoding.prod BitEncoding.nat) formulaEncoding (fun p => finish p.1 p.2) := by
  have hs := fp_fst stateEncoding BitEncoding.nat
  have ho := fp_snd stateEncoding BitEncoding.nat
  have hz := hs.comp (fp_fst BitEncoding.nat formulaEncoding)
  have hf := hs.comp (fp_snd BitEncoding.nat formulaEncoding)
  have hm := hf.comp (fp_fst BitEncoding.unaryNat clauseEncoding.list)
  have hmb := hm.comp UnaryNatConversionMachine.fp_conversion
  have hc := hf.comp (fp_snd BitEncoding.unaryNat clauseEncoding.list)
  have href := (hmb.pair (hz.pair ho)).comp fp_checkedRef
  have hpin := (hmb.pair href).comp fp_pin
  have hv := (hm.pair (fp_const _ BitEncoding.unaryNat 3)).comp UnaryPolynomialMachines.fp_add
  exact hv.pair ((hc.pair hpin).comp (ListMutationMachines.fp_append clauseEncoding))

end PlanarHom.NorExactOne
