import PlanarHom.ComputedBipartiteSideSemantics

/-! NEW actual ordinary-to-prescribed source reduction. Each computed connected
component queries both prescribed orientations and adds them. This supplies
the missing hard-direction bridge; it never assumes the two answers are equal. -/
noncomputable section
set_option autoImplicit false
namespace PlanarHom.OrdinaryToPrescribedBipartite
open Complexity Complexity.MixedCode PrescribedDomains HomogeneousSourceOrientation
open FixedRealRootRestrictions PairProjectionMachines GraphComponentCode
open ComputedBipartiteSideQueries BipartiteRankTwoTractability
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension : ℕ}

def prescribedProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) (side : C→Bool) : PromiseProblem :=
  domainEvaluationProblem basis (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w
    (Bipartite.domains side) sidePolicies emptyPolicies

def connectedForward (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) :
    PromisePolyTimeTuringReduction
      (connectedEvaluationProblem basis (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w)
      (prescribedProblem basis M w side) := by
  rw [prescribedProblem,domainProblem_eq_restricted]
  apply reductionOfPipeline basis BitEncoding.bits
    (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w
    (fun _ : Fin 1=>M) (extendedUnaries (fun u : Fin 0=>u.elim0) (Bipartite.domains side)) w
    (fun g=>g.PlanarValid 1 0 ∧ (support g).Connected ∧ 0<g.vertices)
    (EncodedGraph sidePolicies emptyPolicies) (fun _ h=>h.1.1) (fun _ h=>h.planarValid.1)
    (fun g=>([],ComputedBipartiteSideQueries.queries g)) (fun p : Bits×List K=>p.2.sum)
  · exact (fp_const MixedCode.encoding BitEncoding.bits []).pair ComputedBipartiteSideQueries.fp_queries
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    cases hr : (coloring g).1
    · simp [ComputedBipartiteSideQueries.queries,hr] at hq
    · simp only [ComputedBipartiteSideQueries.queries,hr,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl <;> exact query_planar g hg.1 hr _
  · intro g hg
    exact queries_value_sum g hg.1.1 hg.2.1 hg.2.2 M w side hcross

def forward (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w)
      (prescribedProblem basis M w side) :=
  (GraphComponentCode.componentReduction basis _ _ w).trans (connectedForward basis M w side hcross)

variable [LinearOrder K] [IsStrictOrderedRing K]

def reverse (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) (hw : ∀i,0<w i) (side : C→Bool)
    (hcross : ∀i j,M i j≠0 → side i≠side j) :
    PromisePolyTimeTuringReduction (prescribedProblem basis M w side)
      (evaluationProblem basis (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w) :=
  HomogeneousSourceOrientation.reduction basis M w hw side hcross

end PlanarHom.OrdinaryToPrescribedBipartite
