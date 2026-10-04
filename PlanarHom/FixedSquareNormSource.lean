import PlanarHom.WeightedGramAvailability
import PlanarHom.UnaryLoopRealization

/-!
# Fixed weighted square-norm source programs — NEW reconstruction

These programs construct the conditional parallel-edge unary and its fixed
integer moment backgrounds from the original source. They do not supply or
assume the missing normalized-matrix reduction. All programs retain the exact
original field, basis, raw mixed-code promise, and companion labels.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.RectangularBackgroundSourceNormSimulation

variable {C R : Type} [Fintype C] [CommSemiring R]

/-- The root background is excluded; the one internal vertex keeps its weight. -/
def squareNorm (B : Matrix C C R) (w : C → R) (i : C) : R :=
  ∑ j, w j * (B i j)^2

end PlanarHom.RectangularBackgroundSourceNormSimulation

namespace PlanarHom.FixedSquareNormSource
open Complexity Complexity.MixedCode FiniteLanguageAliases
open PositiveWeightRemoval PairProjectionMachines
open RectangularBackgroundSourceNormSimulation

variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension bt ut : ℕ}

omit [Algebra ℚ K] in
/-- Symmetry turns the weighted two-edge return path into the squared row norm. -/
theorem gram_diagonal (B : Matrix C C K) (w : C → K)
    (hs : ∀ i j, B i j = B j i) (m : ℕ) (i : C) :
    gramCoreField B w m i i = (squareNorm B w i)^m := by
  unfold gramCoreField squareNorm
  congr 1
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hs i j]
  ring

/-- The already compiled loop insertion program multiplies every background,
including an isolated vertex, by one selected diagonal factor. -/
def loopFactorReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (w : C → K) (selected : Fin bt) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis M U (fun i => w i * M selected i i))
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits
    M U (fun i => w i * M selected i i) M U w
    (fun g => ([], [g.addLoops selected.val])) (fun p : Bits × List K => p.2.sum)
  · have hl := ((fp_addLoops selected.val).pair
        (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query = g.addLoops selected.val := List.mem_singleton.mp hq
    subst query
    exact addLoops_planar selected.val selected.isLt g hg
  · intro g hg
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [totalEvaluation_valid _ _ _ _ (addLoops_valid selected g hg.1)]
    exact evaluate_addLoops selected g hg.1 M U w

/-- The temporary Gram matrix label is removed by the actual finite-label
reindexing machine, rather than by treating labels as free. -/
def omitAuxiliaryMatrix (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (N : Matrix C C K)
    (U : Fin ut → C → K) (w : C → K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis M U w)
      (evaluationProblem basis (appendOne M N) U w) := by
  have h := binaryRelabelReduction basis (Fin.castAdd 1) (appendOne M N) U w
  have hm : (appendOne M N) ∘ (Fin.castAdd 1) = M := by
    funext l
    exact appendOne_old M N l
  simpa only [hm] using h

/-- Every fixed natural moment of the genuine conditional square norm can be
added as a unary, jointly with every old binary and unary label. No supplied
source-availability witness occurs in this theorem. -/
def squareNormPowerUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (w : C → K) (old : Fin bt) (hs : ∀ i j, M old i j = M old j i) (m : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis M (appendOne U (fun i => (squareNorm (M old) w i)^m)) w)
      (evaluationProblem basis M U w) := by
  let G := gramCoreField (M old) w m
  have hr := (diagonalUnaryAppendReduction basis (appendOne M G) U w (Fin.last bt)).trans
    (gramAppendReduction basis M U w old m)
  simp only [appendOne_aux] at hr
  have hd : (fun i => G i i) = fun i => (squareNorm (M old) w i)^m :=
    funext (gram_diagonal (M old) w hs m)
  rw [hd] at hr
  exact (omitAuxiliaryMatrix basis M G _ w).trans hr

/-- The fixed moment background is realized with original-source queries in
the same field and basis. In particular m=0 retains w, not unit weights.
This is a source-program prerequisite for normalization, not normalization. -/
def squareNormMomentReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix C C K) (U : Fin ut → C → K)
    (w : C → K) (old : Fin bt) (hs : ∀ i j, M old i j = M old j i) (m : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis M U (fun i => w i * (squareNorm (M old) w i)^m))
      (evaluationProblem basis M U w) := by
  let G := gramCoreField (M old) w m
  have hr := (loopFactorReduction basis (appendOne M G) U w (Fin.last bt)).trans
    (gramAppendReduction basis M U w old m)
  simp only [appendOne_aux] at hr
  have hd : (fun i => w i * G i i) = fun i => w i * (squareNorm (M old) w i)^m := by
    funext i
    exact congrArg (w i * ·) (gram_diagonal (M old) w hs m i)
  rw [hd] at hr
  exact (omitAuxiliaryMatrix basis M G U _).trans hr

end PlanarHom.FixedSquareNormSource
