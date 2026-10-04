import PlanarHom.PottsTutteIdentity
import PlanarHom.PottsComponentCode
import PlanarHom.OneQueryGraphScaling
import PlanarHom.FixedPowerMachines
import PlanarHom.FullLogarithmicPottsReduction

/-!
# Actual one-query Tutte/Potts scaling reductions

Both problems use the same ordinary planar multigraph raw-code promise and the
same fixed rational-basis field answer encoding. Each reduction normalizes the
raw input, computes its component count, makes one query on that graph, and
multiplies by the computed fixed-base power. This file proves the scaling
reductions; Potts hardness is supplied separately by `PositivePottsFoundationClosed`.
-/
noncomputable section
open Classical
namespace PlanarHom.PottsTutteReduction
open Complexity Complexity.MixedCode FullLogarithmicProductIdentities
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension : ℕ}

/-- Total decoded rank-subset Tutte value; invalid ranges have explicit fallback zero. -/
def tutteValue (q : ℕ) (g : MixedCode) : K :=
  if hg : g.Valid 1 0 then (g.toMultiGraph hg).rankSubsetTutte ((q : K) + 1) 2 else 0

/-- The exact raw planar Tutte-point promise in the source field presentation. -/
def tutteProblem (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) : PromiseProblem :=
  ⟨PlanarInput 1 0, encodedFunction encoding (numberFieldEncoding basis) (tutteValue q) []⟩

def pottsValue (q : ℕ) (g : MixedCode) : K :=
  totalEvaluation (fun _ : Fin 1 => (pottsMatrix : Matrix (Fin q) (Fin q) K))
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) g

theorem pottsValue_eq (q : ℕ) (g : MixedCode) (hg : g.Valid 1 0) :
    pottsValue (K := K) q g =
      (q : K) ^ (GraphComponentCode.parts g).length * tutteValue q g := by
  rw [pottsValue, totalEvaluation_valid _ _ _ _ hg,
    FullLogarithmicPottsReduction.evaluate_potts,
    MultiGraph.potts_tutte_fin,
    GraphComponentCode.componentCount_eq_parts_length]
  simp [tutteValue, hg]

omit [FiniteDimensional ℚ K] in
theorem fp_componentPower (basis : Module.Basis (Fin dimension) ℚ K) (a : K) :
    FP encoding (numberFieldEncoding basis)
      (fun g : MixedCode => a ^ (GraphComponentCode.parts g).length) :=
  (GraphComponentMachines.fp_parts.comp
    (ListUnaryLengthMachine.fp_length GraphComponentMachines.natCode.list)).comp
      (FixedPowerMachines.fp_power basis a)

omit [FiniteDimensional ℚ K] in
theorem tutteValue_decode (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ)
    (raw : Bits) (g : MixedCode) (hd : encoding.decode raw = some g) :
    (tutteProblem basis q).value raw = (numberFieldEncoding basis).encode (tutteValue q g) := by
  simp [tutteProblem, encodedFunction, hd]

omit [FiniteDimensional ℚ K] in
theorem pottsValue_decode (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ)
    (raw : Bits) (g : MixedCode) (hd : encoding.decode raw = some g) (hg : g.Valid 1 0) :
    (FullLogarithmicPottsReduction.pottsProblem basis q).value raw =
      (numberFieldEncoding basis).encode (pottsValue q g) := by
  rw [pottsValue, totalEvaluation_valid _ _ _ _ hg]
  exact evaluationValue_decode basis _ _ _ raw g hd hg

/-- Divide the Potts answer by q^c(G). This is an actual one-query fixed-field
reduction for every positive q; q=0 is deliberately excluded from division. -/
def tutteToPotts (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) (hq : q ≠ 0) :
    PromisePolyTimeTuringReduction (tutteProblem basis q)
      (FullLogarithmicPottsReduction.pottsProblem basis q) := by
  let bounds := evaluationProblem_output_bound basis
    (fun _ : Fin 1 => (pottsMatrix : Matrix (Fin q) (Fin q) K))
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)
  let p := Classical.choose bounds
  have hp := Classical.choose_spec bounds
  apply OneQueryGraphScaling.reduction basis (PlanarValid 1 0)
    (tutteProblem basis q) (FullLogarithmicPottsReduction.pottsProblem basis q)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) (tutteValue q) (pottsValue q)
    (fun g => ((q : K)⁻¹) ^ (GraphComponentCode.parts g).length)
    (fun raw g hd _ => tutteValue_decode basis q raw g hd)
    (fun raw g hd hg => pottsValue_decode basis q raw g hd hg.1)
    (fp_componentPower basis _) ?_ p hp
  intro g hg
  rw [pottsValue_eq q g hg.1, ← mul_assoc, ← mul_pow]
  have hqK : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq
  simp [hqK]

/-- Multiply the Tutte answer by q^c(G). The Tutte answer-size bound is obtained
from the already compiled reverse scaling reduction, so no unit-cost or
unproved output-size assumption is introduced. -/
def pottsToTutte (basis : Module.Basis (Fin dimension) ℚ K) (q : ℕ) (hq : q ≠ 0) :
    PromisePolyTimeTuringReduction (FullLogarithmicPottsReduction.pottsProblem basis q)
      (tutteProblem basis q) := by
  let reverse := tutteToPotts basis q hq
  apply OneQueryGraphScaling.reduction basis (PlanarValid 1 0)
    (FullLogarithmicPottsReduction.pottsProblem basis q) (tutteProblem basis q)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) (pottsValue q) (tutteValue q)
    (fun g => (q : K) ^ (GraphComponentCode.parts g).length)
    (fun raw g hd hg => pottsValue_decode basis q raw g hd hg.1)
    (fun raw g hd _ => tutteValue_decode basis q raw g hd)
    (fp_componentPower basis _) (fun g hg => (pottsValue_eq q g hg.1).symm)
    reverse.outputPolynomial reverse.output_length_bound

/-- Exact composition point for an external theorem about this raw-code Tutte
problem. No hardness or classification premise is hidden or postulated. -/
def transfer_external_tutte_reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (q : ℕ) (hq : q ≠ 0) (target : PromiseProblem)
    (external : PromisePolyTimeTuringReduction target (tutteProblem basis q)) :
    PromisePolyTimeTuringReduction target (FullLogarithmicPottsReduction.pottsProblem basis q) :=
  external.trans (tutteToPotts basis q hq)

/-- The source's full-logarithmic-support theorem now starts directly from the
literal rank-subset Tutte point, in the unchanged field answer presentation. -/
def fullLogarithmicReduction {q bt ut : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K) (old : Fin bt)
    (hq : 3 ≤ q) (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hnonneg : ∀ i j, 0 ≤ SpectralFieldPresentation.realMatrix (M old) i j)
    (hconn : (LogarithmicSupport.offDiagonalSupport
      (SpectralFieldPresentation.realMatrix (M old)) hA.1).Connected)
    (hfull : ∀ i j, i ≠ j →
      EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j ≠ 0) :
    PromisePolyTimeTuringReduction (tutteProblem basis q)
      (evaluationProblem basis M U (fun _ => 1)) :=
  (tutteToPotts basis q (by omega)).trans
    (FullLogarithmicPottsReduction.reduction basis M U old hq hA hnonneg hconn hfull)

end PlanarHom.PottsTutteReduction
