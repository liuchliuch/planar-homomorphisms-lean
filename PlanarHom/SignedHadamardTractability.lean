import PlanarHom.HadamardGraphPhase
import PlanarHom.BooleanQuadraticMachines
import PlanarHom.PromisePolynomialTime

/-! NEW unconditional signed Hadamard evaluator on ordinary raw mixed graph
codes, in the caller's prescribed number-field basis. Semantics hold for all
valid finite multigraphs; the public planar promise is a restriction only. -/
namespace PlanarHom.SignedHadamard
open Complexity Complexity.MixedCode

abbrev interaction {K : Type} [CommRing K] : Matrix Bool Bool K := BooleanQuadratic.hadamard

 theorem evaluate_eq {K : Type} [Field K] [Algebra ℚ K]
    (g : MixedCode) (hg : g.Valid 1 0) :
    BooleanQuadratic.evaluate (K:=K) g=
      g.evaluate hg (fun _:Fin 1=>interaction (K:=K)) BooleanTensorFPClosure.emptyUnaries (fun _=>1) := by
  letI : CharZero K:=Algebra.charZero_of_charZero ℚ K
  rw [BooleanQuadratic.evaluate,BooleanQuadratic.result_eq_gauss,
    BooleanQuadratic.dimension_ofGraph,BooleanQuadratic.gauss_ofGraph g hg]

 theorem valid_fp {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) :
    FP (encoding.restrict (Valid 1 0)) (numberFieldEncoding basis)
      (fun g=>g.val.evaluate g.property (fun _:Fin 1=>interaction (K:=K))
        BooleanTensorFPClosure.emptyUnaries (fun _=>1)) := by
  have hv : FP (encoding.restrict (Valid 1 0)) encoding Subtype.val :=
    fp_code_view _ _ _ (fun _=>rfl)
  exact (hv.comp (BooleanQuadratic.fp_evaluate basis)).congr (fun g=>evaluate_eq g.val g.property)

 theorem inFP {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) :
    (evaluationProblem basis (fun _:Fin 1=>interaction (K:=K))
      BooleanTensorFPClosure.emptyUnaries (fun _=>1)).InFP := by
  apply (evaluation_inFP_iff basis _ _ _).mpr
  have hv : FP (encoding.restrict (PlanarValid 1 0)) encoding Subtype.val :=
    fp_code_view _ _ _ (fun _=>rfl)
  exact (hv.comp (BooleanQuadratic.fp_evaluate basis)).congr (fun g=>evaluate_eq g.val g.property.1)

end PlanarHom.SignedHadamard
