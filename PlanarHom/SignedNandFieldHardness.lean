import PlanarHom.SignedNandPlanarHardness
import PlanarHom.MixedColorReindex

/-! Transfer the already unconditional signed-NAND hardness to any fixed
number-field presentation and then to the explicit two-element Fin alphabet. -/
noncomputable section
open Classical
namespace PlanarHom.BiasedPositiveHardness
open Complexity Complexity.MixedCode ProperColoringPottsReduction SignedNandExactOneClause
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

def nandMatrix : Matrix Bool Bool K := nandWeight

def negativeUnary : Bool → K := centerActivity

def nandFin : Matrix (Fin 2) (Fin 2) K := fun i j => nandMatrix (finTwoEquiv i) (finTwoEquiv j)
def negativeFin : Fin 2 → K := fun i => negativeUnary (finTwoEquiv i)

theorem signed_field_hard (basis : Module.Basis (Fin dimension) ℚ K) :
    PromisedSharpPHard (evaluationProblem basis (fun _ : Fin 1 => nandMatrix)
      (fun _ : Fin 1 => negativeUnary) (fun _ => 1)) := by
  have r := fieldDescentReduction rationalBasis basis (Algebra.ofId ℚ K)
    SignedNandNumeric.matrices SignedNandNumeric.unaries (fun _ => 1)
  have hm : (fun (l : Fin 1) i j => (Algebra.ofId ℚ K) (SignedNandNumeric.matrices l i j))=
      (fun _ : Fin 1 => nandMatrix (K:=K)) := by
    funext l i j
    cases i <;> cases j <;> simp [SignedNandNumeric.matrices,nandMatrix,nandWeight]
  have hu : (fun (l : Fin 1) i => (Algebra.ofId ℚ K) (SignedNandNumeric.unaries l i))=
      (fun _ : Fin 1 => negativeUnary (K:=K)) := by
    funext l i
    cases i <;> simp [SignedNandNumeric.unaries,negativeUnary,centerActivity]
  have r' : PromisePolyTimeTuringReduction SignedNandPlanarHardness.problem
      (evaluationProblem basis (fun _ : Fin 1 => nandMatrix) (fun _ : Fin 1 => negativeUnary) (fun _ => 1)) := by
    simpa only [hm,hu,map_one] using r
  exact SignedNandPlanarHardness.promisedSharpPHard.trans r'

theorem signed_fin_hard (basis : Module.Basis (Fin dimension) ℚ K) :
    PromisedSharpPHard (evaluationProblem basis (fun _ : Fin 1 => nandFin)
      (fun _ : Fin 1 => negativeFin) (fun _ => 1)) := by
  have he := evaluationProblem_colorReindex basis finTwoEquiv (fun _ : Fin 1 => nandMatrix (K:=K))
    (fun _ : Fin 1 => negativeUnary (K:=K)) (fun _ => 1)
  exact he.symm ▸ signed_field_hard basis

end PlanarHom.BiasedPositiveHardness
