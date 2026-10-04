import PlanarHom.ComputedDomainDoublingComponents
import PlanarHom.HeterogeneousGraphReduction

/-! NEW actual polynomial-time equivalence for Corollary 12.2. Bipartiteness
is computed from the occurrence list, components are extracted by a compiled
program, and the factor two is removed once per component, including isolates. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ComputedDomainDoubling
open Complexity Complexity.MixedCode GraphComponentCode PairProjectionMachines
open BipartiteRankTwoTractability
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension : ℕ}

def bipartiteProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) : PromiseProblem :=
  restrictedEvaluationProblem basis (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w BipartitePlanarCode

def doubleQueries (g : MixedCode) : List MixedCode := if (coloring g).1 then [g,g] else []

theorem fp_doubleQueries : FP encoding encoding.list doubleQueries := by
  have hs:=((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
    (ListMutationMachines.fp_cons encoding)
  have ht:=((fp_id encoding).pair hs).comp (ListMutationMachines.fp_cons encoding)
  have hflag:=fp_coloring.comp (fp_fst BitEncoding.bool PlanarityParitySolver.assignmentCode)
  exact (hflag.congr (fun _=>by simp)).ite ht (fp_const encoding encoding.list [])

def connectedDoubleToBipartite (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) :
    PromisePolyTimeTuringReduction
      (connectedEvaluationProblem basis (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w))
      (bipartiteProblem basis M w) := by
  apply reductionOfHeterogeneousPipeline basis BitEncoding.bits
    (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w)
    (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w
    (fun g=>g.PlanarValid 1 0 ∧ (support g).Connected ∧ 0<g.vertices)
    BipartitePlanarCode (fun _ h=>h.1.1) (fun _ h=>h.1.1)
    (fun g=>([],doubleQueries g)) (fun p : Bits×List K=>p.2.sum)
  · exact (fp_const encoding BitEncoding.bits []).pair fp_doubleQueries
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    cases hr : (coloring g).1
    · simp [doubleQueries,hr] at hq
    · simp only [doubleQueries,hr,ite_true,List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
      subst query
      exact ⟨hg.1,hr⟩
  · intro g hg
    cases hr : (coloring g).1
    · simp only [doubleQueries,hr,Bool.false_eq_true,ite_false,List.map_nil,List.sum_nil]
      rw [evaluate_homogeneous]
      exact (ComputedBipartiteSideQueries.rejected_zero g hg.1.1 (matrix M) (weights w) Prod.fst
        (crosses M) (by rw [hr]; decide)).symm
    · simp only [doubleQueries,hr,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [totalEvaluation_valid _ _ _ _ hg.1.1,connected_value g hg.1.1 hg.2.1 hg.2.2 hr]
      ring

def doubleToBipartite (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w))
      (bipartiteProblem basis M w) :=
  (componentReduction basis _ _ (weights w)).trans (connectedDoubleToBipartite basis M w)

def bipartiteToDouble (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (w : C→K) :
    PromisePolyTimeTuringReduction (bipartiteProblem basis M w)
      (evaluationProblem basis (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w)) := by
  apply reductionOfHeterogeneousPipeline basis BitEncoding.bits
    (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w
    (fun _ : Fin 1=>matrix M) (fun u : Fin 0=>u.elim0) (weights w)
    BipartitePlanarCode (PlanarValid 1 0) (fun _ h=>h.1.1) (fun _ h=>h.1)
    (fun g=>([],components g)) (fun p : Bits×List K=>(p.2.map (fun a=>a/2)).prod)
  · exact (fp_const encoding BitEncoding.bits []).pair GraphComponentMachines.fp_components
  · have hd:=((fp_id (numberFieldEncoding basis)).pair
        (fp_const (numberFieldEncoding basis) (numberFieldEncoding basis) (2:K))).comp
        (FixedFieldArithmetic.fp_division basis)
    exact (fp_snd _ _).comp ((ListMapMachines.fp_map _ _ _ hd).comp
      (MaterializedFieldListMachines.fp_product basis))
  · intro g hg query hq
    exact (components_promises g hg.1 query hq).1
  · intro g hg
    have he : (((components g).map (totalEvaluation (fun _ : Fin 1=>matrix M)
        (fun u : Fin 0=>u.elim0) (weights w))).map (fun a=>a/2))=
        (components g).map (totalEvaluation (fun _ : Fin 1=>M) (fun u : Fin 0=>u.elim0) w) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro query hq
      obtain ⟨hv,hc,hn⟩:=components_promises g hg.1 query hq
      rw [Function.comp_apply,totalEvaluation_valid _ _ _ _ hv.1,totalEvaluation_valid _ _ _ _ hv.1,
        connected_value query hv.1 hc hn (component_coloring g hg.1.1 hg.2 query hq)]
      letI : CharZero K:=((algebraMap ℚ K).charZero_iff (algebraMap ℚ K).injective).mp inferInstance
      have ht : (2:K)≠0:=by norm_num
      field_simp
    rw [he]
    exact (evaluate_components g hg.1.1 _ _ w).symm

end PlanarHom.ComputedDomainDoubling
