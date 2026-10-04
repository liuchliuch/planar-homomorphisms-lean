import PlanarHom.ParsimoniousBlockTemplate
import PlanarHom.FixedVectorMachines

/-! Honest materialization machines for every fixed local clause template. -/
namespace PlanarHom.ParsimoniousBlockTemplate
open Complexity ParsimoniousNorOneInThree PairProjectionMachines ArithmeticCircuitPrimitives

namespace Template

def inputEncoding (T : Template) : BitEncoding (ℕ × (Fin T.inputs → ℕ)) :=
  BitEncoding.unaryNat.prod (BitEncoding.nat.vector T.inputs)

theorem fp_translate (T : Template) (v : Fin (T.inputs+T.fresh)) :
    FP T.inputEncoding BitEncoding.nat (fun p => T.translate p.1 p.2 v) := by
  by_cases hv : v.val<T.inputs
  · have h := (fp_snd BitEncoding.unaryNat (BitEncoding.nat.vector T.inputs)).comp
      (FixedVectorMachines.fp_coordinate BitEncoding.nat T.inputs ⟨v.val,hv⟩)
    exact h.congr (fun p => by simp [translate,hv])
  · have hm := (fp_fst BitEncoding.unaryNat (BitEncoding.nat.vector T.inputs)).comp
      UnaryNatConversionMachine.fp_conversion
    have h := (hm.pair (fp_const T.inputEncoding BitEncoding.nat (v.val-T.inputs))).comp
      BinaryArithmetic.fp_addition
    exact h.congr (fun p => by simp [translate,hv])

private theorem fp_rows (T : Template) (rows : Formula (Fin (T.inputs+T.fresh))) :
    FP T.inputEncoding clauseEncoding.list (fun p => rename (T.translate p.1 p.2) rows) := by
  induction rows with
  | nil => exact fp_const _ _ []
  | cons c cs ih =>
    have hc := (T.fp_translate c.1).pair ((T.fp_translate c.2.1).pair (T.fp_translate c.2.2))
    exact (hc.pair ih).comp (ListMutationMachines.fp_cons clauseEncoding)

/-- All local clauses and every binary address are emitted by an actual machine. -/
theorem fp_emit (T : Template) :
    FP T.inputEncoding clauseEncoding.list (fun p => T.emit p.1 p.2) := fp_rows T T.clauses

def appendInputEncoding (T : Template) : BitEncoding (NumericFormula × (Fin T.inputs → ℕ)) :=
  formulaEncoding.prod (BitEncoding.nat.vector T.inputs)

def append (T : Template) (p : NumericFormula × (Fin T.inputs → ℕ)) : NumericFormula :=
  (p.1.1+T.fresh,p.1.2++T.emit p.1.1 p.2)

/-- Unary allocation, reference emission, and list-header/copy costs are charged. -/
theorem fp_append (T : Template) : FP T.appendInputEncoding formulaEncoding T.append := by
  have hf := fp_fst formulaEncoding (BitEncoding.nat.vector T.inputs)
  have hr := fp_snd formulaEncoding (BitEncoding.nat.vector T.inputs)
  have hm := hf.comp (fp_fst BitEncoding.unaryNat clauseEncoding.list)
  have hc := hf.comp (fp_snd BitEncoding.unaryNat clauseEncoding.list)
  have hn := (hm.pair (fp_const _ BitEncoding.unaryNat T.fresh)).comp UnaryPolynomialMachines.fp_add
  have he := (hm.pair hr).comp T.fp_emit
  exact hn.pair ((hc.pair he).comp (ListMutationMachines.fp_append clauseEncoding))

end Template
end PlanarHom.ParsimoniousBlockTemplate
