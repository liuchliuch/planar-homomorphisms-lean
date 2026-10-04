import PlanarHom.BooleanGroupedTableRecoveryMachines

/-! Concrete polynomial bounds for the materialized intermediate words of the
complete grouped compiler. Each polynomial is extracted from its constructed
ordinary TM2 program, so these are conclusions rather than growth premises. -/
noncomputable section
namespace PlanarHom.BooleanGroupedRecoveryBounds
open Complexity PairProjectionMachines MachineComposition
open BooleanFieldTower BooleanFieldTowerMachines
open BooleanGroupedGridRecoveryMachines BooleanGroupedTableRecoveryMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def gridValues (n : ℕ) (p : Input K n) : List (Tower K n) :=
  let q := prepare n p
  BooleanGroupedGridRecoveryMachines.gridValues n (q.1,(q.2.1,q.2.2.1))

def weights (n : ℕ) (p : Input K n) : List K :=
  let q := prepare n p
  MaterializedGridWeightsMachines.weights (MaterializedGridWeightsMachines.grid q.2.1,q.2.2.2)

theorem fp_gridValues (n : ℕ) : FP (inputEncoding basis n) (encoding basis n).list (gridValues n) := by
  let ek := numberFieldEncoding basis
  let er := (rowEncoding basis n).list
  have hp := fp_prepare basis n
  have hd := hp.comp (fp_fst ek.list (BitEncoding.unaryNat.prod (er.prod ek.list)))
  have ht := hp.comp (fp_snd ek.list (BitEncoding.unaryNat.prod (er.prod ek.list)))
  have hn := ht.comp (fp_fst BitEncoding.unaryNat (er.prod ek.list))
  have hr := (ht.comp (fp_snd BitEncoding.unaryNat (er.prod ek.list))).comp (fp_fst er ek.list)
  exact (hd.pair (hn.pair hr)).comp (BooleanGroupedGridRecoveryMachines.fp_gridValues basis n)

theorem fp_weights (n : ℕ) : FP (inputEncoding basis n) (numberFieldEncoding basis).list (weights n) := by
  let ek := numberFieldEncoding basis
  let er := (rowEncoding basis n).list
  have hp := fp_prepare basis n
  have ht := hp.comp (fp_snd ek.list (BitEncoding.unaryNat.prod (er.prod ek.list)))
  have hn := ht.comp (fp_fst BitEncoding.unaryNat (er.prod ek.list))
  have hy := (ht.comp (fp_snd BitEncoding.unaryNat (er.prod ek.list))).comp (fp_snd er ek.list)
  exact ((hn.comp (MaterializedGridWeightsMachines.fp_grid basis)).pair hy).comp
    (MaterializedGridWeightsMachines.fp_weights basis)

/-- A single explicit polynomial expression dominates preparation, both large
intermediate lists, the represented answer, and the descended base answer. -/
def intermediatePolynomial (n : ℕ) : Polynomial ℕ :=
  outputLengthPolynomial (Classical.choice (fp_prepare basis n)) +
  outputLengthPolynomial (Classical.choice (fp_gridValues basis n)) +
  outputLengthPolynomial (Classical.choice (fp_weights basis n)) +
  outputLengthPolynomial (Classical.choice (BooleanGroupedTableRecoveryMachines.fp_recoverTower basis n)) +
  outputLengthPolynomial (Classical.choice (BooleanGroupedTableRecoveryMachines.fp_recover basis n))

theorem intermediate_encoding_bounds (n : ℕ) (p : Input K n) :
    let B := (intermediatePolynomial basis n).eval ((inputEncoding basis n).encode p).length
    ((coreEncoding basis n).encode (prepare n p)).length ≤ B ∧
    ((encoding basis n).list.encode (gridValues n p)).length ≤ B ∧
    ((numberFieldEncoding basis).list.encode (weights n p)).length ≤ B ∧
    ((encoding basis n).encode (BooleanGroupedTableRecoveryMachines.recoverTower n p)).length ≤ B ∧
    ((numberFieldEncoding basis).encode (BooleanGroupedTableRecoveryMachines.recover n p)).length ≤ B := by
  have h₁ := encoded_output_length_le (Classical.choice (fp_prepare basis n)) p
  have h₂ := encoded_output_length_le (Classical.choice (fp_gridValues basis n)) p
  have h₃ := encoded_output_length_le (Classical.choice (fp_weights basis n)) p
  have h₄ := encoded_output_length_le
    (Classical.choice (BooleanGroupedTableRecoveryMachines.fp_recoverTower basis n)) p
  have h₅ := encoded_output_length_le
    (Classical.choice (BooleanGroupedTableRecoveryMachines.fp_recover basis n)) p
  simp only [BitEncoding.toFinEncoding] at h₁ h₂ h₃ h₄ h₅
  simp only [intermediatePolynomial, Polynomial.eval_add]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

end PlanarHom.BooleanGroupedRecoveryBounds
