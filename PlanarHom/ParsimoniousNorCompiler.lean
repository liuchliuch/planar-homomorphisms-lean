import PlanarHom.ParsimoniousNorOneInThree
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.UnaryNatConversionMachine

/-! The local unique-extension NOR gadget is emitted by an actual polynomial
binary machine, with an honestly unary variable-count header. -/
namespace PlanarHom.ParsimoniousNorOneInThree
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

abbrev NumericFormula := ℕ × Formula ℕ
abbrev GateInput := NumericFormula × (ℕ × ℕ)

def clauseEncoding : BitEncoding (Clause ℕ) := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
def formulaEncoding : BitEncoding NumericFormula := BitEncoding.unaryNat.prod clauseEncoding.list
def gateInputEncoding : BitEncoding GateInput := formulaEncoding.prod (BitEncoding.nat.prod BitEncoding.nat)

def numericGate (m x y : ℕ) : Formula ℕ := [(x,m+2,m),(y,m+3,m),(m+1,m+2,m+3)]

/-- Physically append the three gadget clauses using four fresh variable indices. -/
def compileGate (p : GateInput) : NumericFormula :=
  (p.1.1+4,p.1.2++numericGate p.1.1 p.2.1 p.2.2)

/-- Every referenced variable lies within the explicit variable-count header. -/
def NumericValid (f : NumericFormula) : Prop :=
  ∀ c∈f.2, c.1<f.1 ∧ c.2.1<f.1 ∧ c.2.2<f.1

theorem compileGate_valid (p : GateInput) (hf : NumericValid p.1)
    (hx : p.2.1<p.1.1) (hy : p.2.2<p.1.1) : NumericValid (compileGate p) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · have hh := hf c hc
    dsimp [compileGate]
    omega
  · simp only [numericGate, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> dsimp [compileGate] <;> omega

@[simp] theorem compileGate_variables (p : GateInput) : (compileGate p).1=p.1.1+4 := rfl
@[simp] theorem compileGate_clauses (p : GateInput) : (compileGate p).2.length=p.1.2.length+3 := by
  simp [compileGate,numericGate]

/-- The actual emitted natural indices coincide with the typed parsimonious
clause constructor, rather than merely having the same lengths. -/
theorem compileGate_typed {n : ℕ} (f : Formula (Fin n)) (x y : Fin n) :
    compileGate ((n,rename Fin.val f),(x.val,y.val)) =
      (n+4,rename (Sum.elim Fin.val (fun k : Fin 4 => n+k.val)) (appendGate f x y)) := by
  simp [compileGate,numericGate,appendGate,gateClauses,rename,List.map_map,Function.comp_def]

private theorem fp_three {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (f g h : A → B) (hf : FP ea eb f) (hg : FP ea eb g) (hh : FP ea eb h) :
    FP ea eb.list (fun a => [f a,g a,h a]) := by
  exact (hf.pair ((hg.pair ((hh.pair (fp_const ea eb.list [])).comp
    (ListMutationMachines.fp_cons eb))).comp (ListMutationMachines.fp_cons eb))).comp
      (ListMutationMachines.fp_cons eb)

/-- Concrete local formula compiler: all copies, offsets, list headers and
payloads are handled by existing proved finite-control machines. -/
theorem fp_compileGate : FP gateInputEncoding formulaEncoding compileGate := by
  let input := gateInputEncoding
  have hf := fp_fst formulaEncoding (BitEncoding.nat.prod BitEncoding.nat)
  have hab := fp_snd formulaEncoding (BitEncoding.nat.prod BitEncoding.nat)
  have hm := hf.comp (fp_fst BitEncoding.unaryNat clauseEncoding.list)
  have hc := hf.comp (fp_snd BitEncoding.unaryNat clauseEncoding.list)
  have hx := hab.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hy := hab.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hmb := hm.comp UnaryNatConversionMachine.fp_conversion
  have hoff (k : ℕ) : FP input BitEncoding.nat (fun p : GateInput => p.1.1+k) :=
    (hmb.pair (fp_const input BitEncoding.nat k)).comp BinaryArithmetic.fp_addition
  have hrow1 : FP input clauseEncoding (fun p : GateInput => (p.2.1,p.1.1+2,p.1.1)) :=
    hx.pair ((hoff 2).pair hmb)
  have hrow2 : FP input clauseEncoding (fun p : GateInput => (p.2.2,p.1.1+3,p.1.1)) :=
    hy.pair ((hoff 3).pair hmb)
  have hrow3 : FP input clauseEncoding (fun p : GateInput => (p.1.1+1,p.1.1+2,p.1.1+3)) :=
    (hoff 1).pair ((hoff 2).pair (hoff 3))
  have hrows := fp_three input clauseEncoding _ _ _ hrow1 hrow2 hrow3
  have hclauses := (hc.pair hrows).comp (ListMutationMachines.fp_append clauseEncoding)
  have hvars := (hm.pair (fp_const input BitEncoding.unaryNat 4)).comp UnaryPolynomialMachines.fp_add
  exact hvars.pair hclauses

end PlanarHom.ParsimoniousNorOneInThree
