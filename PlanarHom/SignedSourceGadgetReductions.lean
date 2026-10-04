import PlanarHom.Corollary32Field
import PlanarHom.SelectedStretchMachines
import PlanarHom.SelectedStretchSemantics
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.SignedThreeStateAlgebra

/-! Genuine raw planar Turing reductions for the signed classification.
Sign interpolation, literal two-edge path substitution and Schur squaring
retain the prescribed fixed field and unit background. -/
noncomputable section
open Classical
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode PairProjectionMachines ProductCompatibility
variable {K C : Type} [Field K] [Algebra ℚ K] [Fintype C] [DecidableEq C]
variable {dimension u : ℕ}

/-- One matrix square is a literal two-edge path at each source occurrence.
Loops and parallel edges are retained by the existing path compiler. -/
def pathSquareReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _:Fin 1=>M*M) U (fun _=>1))
      (evaluationProblem basis (fun _:Fin 1=>M) U (fun _=>1)) := by
  have ht : FP encoding encoding (fun g=>g.stretchLabel 0 0 1) :=
    ((fp_const encoding BitEncoding.unaryNat 1).pair (fp_id encoding)).comp (fp_stretchLabel 0 0)
  apply planarReductionOfPipeline basis BitEncoding.bits (fun _:Fin 1=>M*M) U (fun _=>1)
    (fun _:Fin 1=>M) U (fun _=>1)
    (fun g=>([],[g.stretchLabel 0 0 1])) (fun p : Bits×List K=>p.2.sum)
  · exact (fp_const _ BitEncoding.bits []).pair
      ((ht.pair (fp_const _ encoding.list [])).comp (ListMutationMachines.fp_cons encoding))
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    obtain rfl := List.mem_singleton.mp hq
    exact stretchLabel_planar g hg 0 0 1 (by decide) (fun e he _=>(hg.1.1 e he).2.2)
  · intro g hg
    have hkeep : ∀e∈g.edges,e.2.2≠0→e.2.2<1 := fun e he _=>(hg.1.1 e he).2.2
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (g.stretchLabel_valid hg.1 0 0 1 (by decide) hkeep)]
    have h := evaluate_stretchLabel g hg.1 0 1 (0:Fin 1) hkeep (fun _=>M) U
    have hm : pathPowerLabels (a:=1) (fun _:Fin 1=>M) 0 (0:Fin 1) 1=
        (fun _:Fin 1=>M*M) := by
      funext i
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      simp [pathPowerLabels,pow_two]
    rw [hm] at h
    exact h

/-- Composition uses the actual planar programs, not a matrix-operation
oracle or a product of independent oracle values. -/
def squaredGramReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _:Fin 1=>schurSquare (M*M)) U (fun _=>1))
      (evaluationProblem basis (fun _:Fin 1=>M) U (fun _=>1)) :=
  (squareReduction basis (M*M) U (fun _=>1)).trans (pathSquareReduction basis M U)

/-- The standalone sign transform is a specialization of the proved product
interpolation machine, over the original field without any oracle extension. -/
def signReduction {q : ℕ} {F : IntermediateField ℚ ℝ}
    (basis : Module.Basis (Fin dimension) ℚ F)
    (M : Matrix (Fin q) (Fin q) F) (U : Fin u→Fin q→F) (w : Fin q→F) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _:Fin 1=>MagnitudeSign.signMatrix M) U w)
      (evaluationProblem basis (fun _:Fin 1=>M) U w) := by
  apply homogeneousProductReduction basis M (MagnitudeSign.signMatrix M) U w
  · intro i j h
    simp [MagnitudeSign.signMatrix,MagnitudeSign.sign,h]
  · apply hasProductMaps_of_compatible
    apply compatible_of_field_embedding F.val.toRingHom
    change Compatible (fun p : Fin q×Fin q=>(M p.1 p.2:ℝ))
      (fun p=>(MagnitudeSign.sign (M p.1 p.2):ℝ))
    simpa only [MagnitudeSign.sign_coe] using
      compatible_sign (fun p : Fin q×Fin q=>(M p.1 p.2:ℝ))

/-- Concrete signed-source target used for the remaining irreducible
three-state branch. -/
def signSquaredGramReduction {q : ℕ} {F : IntermediateField ℚ ℝ}
    (basis : Module.Basis (Fin dimension) ℚ F)
    (M : Matrix (Fin q) (Fin q) F) (U : Fin u→Fin q→F) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis
        (fun _:Fin 1=>schurSquare (MagnitudeSign.signMatrix M*MagnitudeSign.signMatrix M)) U (fun _=>1))
      (evaluationProblem basis (fun _:Fin 1=>M) U (fun _=>1)) :=
  (squaredGramReduction basis (MagnitudeSign.signMatrix M) U).trans
    (signReduction basis M U (fun _=>1))

end PlanarHom.SignedThreeState
