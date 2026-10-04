import PlanarHom.LagrangeCoefficientMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.ListContextFilterMachines
import PlanarHom.FieldDotProductMachines

/-! # Actual list-based shifted Lagrange recovery on the source-product promise -/
namespace PlanarHom.LagrangeRecoveryMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines
open LagrangeCoefficientMachines
variable {K I : Type} [Field K] [DecidableEq K]

abbrev Data (K : Type) := ℕ×(List (K×K)×List K)

def Valid (A : I→K) (d : Data K) : Prop := NodesValid A d.1 (d.2.1.map Prod.fst)
def Input (A : I→K) := {d : Data K // Valid A d}

/-- Discard every row with the distinguished source key; keep all other source
nodes in their actual table order. No target value is recomputed. -/
def otherNodes (μ : K) (table : List (K×K)) : List K :=
  (table.map Prod.fst).filter (fun ν => decide (ν≠μ))

def rowTerm (A : I→K) (input : Input A) (row : K×K) : K :=
  let others := otherNodes row.1 input.val.2.1
  let cs := productCoefficients others
  let den := MaterializedFieldListMachines.shiftedDenominator (row.1,others)
  (row.2/den)*(List.zipWith (fun c y => c*y) cs input.val.2.2).sum

def recover (A : I→K) (input : Input A) : K :=
  (input.val.2.1.map (fun row => rowTerm A input row)).sum

/-- A row's filtered node list inherits the source-word promise solely by list
membership; no hidden predicate-deciding algorithm is required. -/
def coefficientInput (A : I→K) (p : Input A×(K×K)) : LagrangeCoefficientMachines.Input A :=
  ⟨(p.1.val.1,otherNodes p.2.1 p.1.val.2.1),fun μ hμ =>
    p.1.property μ (List.mem_of_mem_filter hμ)⟩

variable [Algebra ℚ K] [Fintype I] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K) (A : I→K)

noncomputable def dataEncoding : BitEncoding (Data K) :=
  BitEncoding.unaryNat.prod (((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list.prod
    (numberFieldEncoding basis).list)

/-- Unary m, the complete original source/target pair table, and actual answer
words remain in the input. Only the proved source-node promise is restricted. -/
noncomputable def inputEncoding : BitEncoding (Input A) := (dataEncoding basis).restrict (Valid A)

omit [Fintype I] [DecidableEq K] in
theorem fp_input_view : FP (inputEncoding basis A) (dataEncoding basis) (fun x => x.val) :=
  fp_code_view _ _ _ (fun _ => rfl)

omit [Fintype I] [DecidableEq K] in
theorem fp_table : FP (inputEncoding basis A) ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
    (fun x => x.val.2.1) :=
  ((fp_input_view basis A).comp (fp_snd BitEncoding.unaryNat _)).comp (fp_fst _ _)

omit [Fintype I] [DecidableEq K] in
theorem fp_answers : FP (inputEncoding basis A) (numberFieldEncoding basis).list (fun x => x.val.2.2) :=
  ((fp_input_view basis A).comp (fp_snd BitEncoding.unaryNat _)).comp (fp_snd _ _)

omit [Fintype I] [DecidableEq K] in
theorem fp_unary_m : FP (inputEncoding basis A) BitEncoding.unaryNat (fun x => x.val.1) :=
  (fp_input_view basis A).comp (fp_fst BitEncoding.unaryNat _)

omit [Fintype I] in
theorem fp_otherNodes : FP ((numberFieldEncoding basis).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list) (numberFieldEncoding basis).list
      (fun p => otherNodes p.1 p.2) := by
  have hm := fp_fst (numberFieldEncoding basis) ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
  have ht := fp_snd (numberFieldEncoding basis) ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
  have hn := ht.comp (ListMapMachines.fp_map _ _ Prod.fst (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)))
  have hneq : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) BitEncoding.bool
      (fun p : K×K => decide (p.2≠p.1)) :=
    ((FixedFieldArithmetic.fp_equality basis).comp (fp_bool_unary BitEncoding.bool not)).congr
      (fun p => by simp [eq_comm])
  exact (hm.pair hn).comp (ListContextFilterMachines.fp_filterWithContext _ _ _ hneq)

/-- Every row calculation is a compiled ordinary FP circuit: filtered source
nodes, exact product coefficients, shifted denominator, shortest-list dot,
division by the denominator, and multiplication by the retained target value. -/
theorem fp_rowTerm : FP ((inputEncoding basis A).prod ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
    (numberFieldEncoding basis) (fun p => rowTerm A p.1 p.2) := by
  have hc := fp_fst (inputEncoding basis A) ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have hr := fp_snd (inputEncoding basis A) ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have hm := hc.comp (fp_unary_m basis A)
  have ht := hc.comp (fp_table basis A)
  have hy := hc.comp (fp_answers basis A)
  have hμ := hr.comp (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis))
  have hη := hr.comp (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis))
  have ho := (hμ.pair ht).comp (fp_otherNodes basis)
  have hp : FP ((inputEncoding basis A).prod ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
      (LagrangeCoefficientMachines.inputEncoding basis A) (coefficientInput A) :=
    (hm.pair ho).transportOutput (fun _ => rfl)
  have hcs := hp.comp (LagrangeCoefficientMachines.fp_productCoefficients basis A)
  have hd := (hμ.pair ho).comp (MaterializedFieldListMachines.fp_shiftedDenominator basis)
  have hscale := (hη.pair hd).comp (FixedFieldArithmetic.fp_division basis)
  have hdot := (hcs.pair hy).comp (FieldDotProductMachines.fp_dot basis)
  exact (hscale.pair hdot).comp (FixedFieldArithmetic.fp_multiplication basis)

/-- Complete ordinary machine for this materialized shifted recovery formula.
Distinctness, nonzero nodes and answer lengths are semantic hypotheses for the
later interpolation identity, not assumptions hidden in this machine theorem. -/
theorem fp_recover : FP (inputEncoding basis A) (numberFieldEncoding basis) (recover A) := by
  have hrows := ListContextMachines.fp_mapWithContext (inputEncoding basis A)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) (numberFieldEncoding basis)
    (fun p => rowTerm A p.1 p.2) (fp_rowTerm basis A)
  exact ((((fp_id (inputEncoding basis A)).pair (fp_table basis A)).comp hrows).comp
    (MaterializedFieldListMachines.fp_sum basis))

end PlanarHom.LagrangeRecoveryMachines
