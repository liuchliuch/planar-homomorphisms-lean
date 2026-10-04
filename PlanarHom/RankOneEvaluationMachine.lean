import PlanarHom.GraphDegreeSemantics
import PlanarHom.FixedPowerMachines
import PlanarHom.FixedVectorMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.PromisePolynomialTime

/-! Genuine polynomial-bit rank-one evaluation. Degrees, powers, color sums
and vertex products are all computed by actual finite-stack TM2 programs. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.RankOneEvaluationMachine
open Complexity Complexity.MixedCode PairProjectionMachines
variable {K : Type} [Field K] [Algebra ℚ K] {q dimension : ℕ}

def factor (a w : Fin q→K) (n : ℕ) : K := ∑i,w i*a i^n

def evaluate (a w : Fin q→K) (g : MixedCode) : K :=
  ((GraphDegreeMachines.degrees g).map (factor a w)).prod

theorem fp_factor (basis : Module.Basis (Fin dimension) ℚ K) (a w : Fin q→K) :
    FP BitEncoding.unaryNat (numberFieldEncoding basis) (factor a w) := by
  let e := numberFieldEncoding basis
  have hf : ∀i : Fin q,FP BitEncoding.unaryNat e (fun n=>w i*a i^n) := by
    intro i
    exact ((fp_const BitEncoding.unaryNat e (w i)).pair (FixedPowerMachines.fp_power basis (a i))).comp
      (FixedFieldArithmetic.fp_multiplication basis)
  have hv := FixedVectorMachines.fp_assemble BitEncoding.unaryNat e q (fun n i=>w i*a i^n) hf
  have hl : FP BitEncoding.unaryNat e.list (fun n=>List.ofFn (fun i=>w i*a i^n)) :=
    hv.transportOutput (fun _=>rfl)
  exact (hl.comp (MaterializedFieldListMachines.fp_sum basis)).congr (fun n=>by simpa only [factor,Function.comp_apply] using List.sum_ofFn (f:=fun i : Fin q=>w i*a i^n))

theorem fp_evaluate (basis : Module.Basis (Fin dimension) ℚ K) (a w : Fin q→K) :
    FP encoding (numberFieldEncoding basis) (evaluate a w) :=
  (GraphDegreeMachines.fp_degrees.comp
    (ListMapMachines.fp_map BitEncoding.unaryNat (numberFieldEncoding basis) (factor a w)
      (fp_factor basis a w))).comp (MaterializedFieldListMachines.fp_product basis)

/-- The stronger all-valid-input promise needs no planarity algorithm. -/
theorem validEvaluation_inFP (basis : Module.Basis (Fin dimension) ℚ K) (a w : Fin q→K) :
    (restrictedEvaluationProblem basis (fun _ : Fin 1=>fun i j=>a i*a j)
      (fun i : Fin 0=>Fin.elim0 i) w (Valid 1 0)).InFP := by
  apply (restrictedEvaluation_inFP_iff basis _ _ _ (Valid 1 0) (fun _ h=>h)).mpr
  have hv : FP (encoding.restrict (Valid 1 0)) encoding Subtype.val :=
    fp_code_view _ _ _ (fun _=>rfl)
  apply (hv.comp (fp_evaluate basis a w)).congr
  intro g
  exact (GraphDegreeMachines.rankOne_evaluate g.val g.property a w).symm

/-- Every fixed weighted rank-one source has an actual promised polynomial
machine on all raw planar inputs, including alternate successful encodings. -/
theorem evaluation_inFP (basis : Module.Basis (Fin dimension) ℚ K) (a w : Fin q→K) :
    (evaluationProblem basis (fun _ : Fin 1=>fun i j=>a i*a j) (fun i : Fin 0=>Fin.elim0 i) w).InFP := by
  apply (validEvaluation_inFP basis a w).mono
  · rintro raw ⟨g,hd,hg⟩
    exact ⟨g,hd,hg.1⟩
  · intro _ _
    rfl

end PlanarHom.RankOneEvaluationMachine
