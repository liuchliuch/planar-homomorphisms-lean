import PlanarHom.Quotient
import PlanarHom.RootedHomogeneousSemantics
import PlanarHom.SupportComponentReduction
import PlanarHom.PositiveWeightRemovalReduction
import PlanarHom.OracleReductionLaws
import PlanarHom.PromiseReductionTransport
import Mathlib.Data.Fintype.Quotient

/-! Actual identical-row quotienting is a one-query reduction on the very same
raw graph. The quotient retains every row class, including the zero row, and
adds vertex weights within classes. All answers use the original field basis. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.ActualTwins
open Complexity Complexity.MixedCode
variable {C D K : Type} [Fintype C] [Fintype D] [Field K] [Algebra ℚ K]
variable {dimension : ℕ}

/-- Semantic changes of a fixed color set leave the input word unchanged. The
machine makes one actual oracle call on that word, with a proved output bound.
Every successful alternate raw encoding and every promised oracle extension
is covered by the reduction. -/
def homogeneousIdentityReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C → K) (N : Matrix D D K) (v : D → K)
    (he : ∀ (g : MixedCode) (hg : g.Valid 1 0),
      (g.toMultiGraph hg).partition M w = (g.toMultiGraph hg).partition N v) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w)
      (evaluationProblem basis (fun _ : Fin 1 => N) (fun u : Fin 0 => Fin.elim0 u) v) := by
  let bound := evaluationProblem_output_bound basis
    (fun _ : Fin 1 => N) (fun u : Fin 0 => Fin.elim0 u) v
  let r := PromisePolyTimeTuringReduction.refl_of_output_bound _
    (Classical.choose bound) (Classical.choose_spec bound)
  apply r.transport
    (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w)
    (evaluationProblem basis (fun _ : Fin 1 => N) (fun u : Fin 0 => Fin.elim0 u) v)
    (fun _ h => h) (fun _ h => h) ?_ (fun _ _ => rfl)
  intro bits hb
  obtain ⟨g,hd,hg⟩ := hb
  change evaluationValue basis _ _ _ bits = evaluationValue basis _ _ _ bits
  rw [evaluationValue_decode basis _ _ _ bits g hd hg.1,
    evaluationValue_decode basis _ _ _ bits g hd hg.1]
  congr 1
  simpa only [evaluate_homogeneous] using he g hg.1

/-- The full weighted actual quotient is available from the original oracle;
no zero-row class is removed at this exact-identity stage. -/
def quotientReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (w : C → K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => Twins.quotientMatrix A hs)
        (fun u : Fin 0 => Fin.elim0 u) (Twins.quotientWeight A w))
      (evaluationProblem basis (fun _ : Fin 1 => A) (fun u : Fin 0 => Fin.elim0 u) w) :=
  homogeneousIdentityReduction basis _ _ A w
    (fun g hg => (Twins.partition_canonicalQuotient (g.toMultiGraph hg) A w hs).symm)

/-- Quotienting asks the source oracle about the identical raw input word. -/
theorem quotientReduction_machine (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (w : C → K) :
    (quotientReduction basis A hs w).machine = directQueryMachine := rfl

/-- The same exact identity gives the converse reduction, still without
dropping the zero row or its positive accumulated weight. -/
def originalReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A : Matrix C C K) (hs : ∀ i j,A i j=A j i) (w : C → K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => A) (fun u : Fin 0 => Fin.elim0 u) w)
      (evaluationProblem basis (fun _ : Fin 1 => Twins.quotientMatrix A hs)
        (fun u : Fin 0 => Fin.elim0 u) (Twins.quotientWeight A w)) :=
  homogeneousIdentityReduction basis A w _ _
    (fun g hg => Twins.partition_canonicalQuotient (g.toMultiGraph hg) A w hs)

/-- Renumbering a fixed finite color set is likewise an unchanged-graph
semantic query; no color data are placed into the input graph. -/
def reindexReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix D D K) (w : D → K) (e : C ≃ D) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => fun i j => M (e i) (e j))
        (fun u : Fin 0 => Fin.elim0 u) (fun i => w (e i)))
      (evaluationProblem basis (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w) :=
  homogeneousIdentityReduction basis _ _ M w
    (fun g hg => (g.toMultiGraph hg).partition_reindexColors M w e)

end PlanarHom.ActualTwins
