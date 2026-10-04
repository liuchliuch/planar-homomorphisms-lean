import PlanarHom.RectangularNormalizedMomentPrograms

noncomputable section
open Classical
namespace PlanarHom.NormalizedMomentProgramRegressions
open Complexity Complexity.MixedCode EndpointUnarySource EndpointLoopMachines
open FiniteLabelLookupMachines FiniteLanguageAliases
open RectangularSourceNormSimulation RectangularBackgroundSourceNormSimulation

def markedLoop : MixedCode := ⟨1,[(0,0,1)],[(0,0)]⟩
def markedParallel : MixedCode := ⟨2,[(0,1,1),(0,1,1)],[]⟩
def mixedOccurrences : MixedCode := ⟨2,[(0,1,0),(0,1,1)],[(1,0)]⟩
def isolatedVertex : MixedCode := ⟨1,[],[(0,1)]⟩
def emptyGraph : MixedCode := ⟨0,[],[]⟩

theorem marked_loop_two_unaries :
    (endpointTransform (0 : Fin 1) (1 : Fin 2) markedLoop).unaries =
      [(0,0),(0,1),(0,1)] := by
  simp [endpointTransform,addUnaryAt,loopVertices,GraphDegreeMachines.endpoints,
    markedLoop,relabelBinary]

theorem marked_loop_keeps_one_binary_occurrence :
    (endpointTransform (0 : Fin 1) (1 : Fin 2) markedLoop).edges = [(0,0,0)] := by
  simp [endpointTransform,addUnaryAt,markedLoop,relabelBinary,finTable,lookup,dropAux,List.ofFn_succ]

theorem parallel_edges_get_four_unaries :
    (endpointTransform (0 : Fin 1) (1 : Fin 2) markedParallel).unaries =
      [(0,1),(1,1),(0,1),(1,1)] := by
  simp [endpointTransform,addUnaryAt,loopVertices,GraphDegreeMachines.endpoints,
    markedParallel,relabelBinary]

theorem only_selected_occurrences_are_decorated :
    (endpointTransform (0 : Fin 1) (1 : Fin 2) mixedOccurrences).unaries =
      [(1,0),(0,1),(1,1)] := by
  simp [endpointTransform,addUnaryAt,loopVertices,GraphDegreeMachines.endpoints,
    mixedOccurrences,relabelBinary]

theorem isolate_has_no_endpoint_decoration :
    (endpointTransform (0 : Fin 1) (1 : Fin 2) isolatedVertex).unaries = [(0,1)] := rfl

theorem isolate_still_gets_moment :
    (momentTransform (0 : Fin 2) 3 isolatedVertex).unaries =
      [(0,1),(0,0),(0,0),(0,0)] := rfl

theorem zeroth_moment_keeps_unaries (g : MixedCode) :
    momentTransform (0 : Fin 2) 0 g = g := by
  cases g
  simp [momentTransform,momentVertices,addUnaryAt]

theorem empty_endpoint_graph : endpointTransform (0 : Fin 1) (1 : Fin 2) emptyGraph = emptyGraph := rfl

theorem empty_moment_graph (m : ℕ) : momentTransform (0 : Fin 2) m emptyGraph = emptyGraph := rfl

theorem all_original_vertices_retained (g : MixedCode) (m : ℕ) :
    (momentTransform (0 : Fin 2) m (endpointTransform (0 : Fin 1) (1 : Fin 2) g)).vertices = g.vertices := rfl

theorem markedLoop_valid : markedLoop.Valid 2 2 := by simp [markedLoop,MixedCode.Valid]

def sourceMatrix : Fin 1 → Matrix (Fin 1) (Fin 1) ℚ := fun _ _ _ => 2
def sourceUnaries : Fin 2 → Fin 1 → ℚ := fun l _ => if l = 0 then 7 else 5

theorem endpoint_loop_numerics :
    markedLoop.evaluate markedLoop_valid
      (appendOne sourceMatrix (unaryGauge (sourceMatrix 0) (sourceUnaries 1))) sourceUnaries (fun _ => 3) = 1050 := by
  norm_num [MixedCode.evaluate,markedLoop,binaryValue,unaryValue,sourceMatrix,sourceUnaries,
    appendOne,unaryGauge,Fin.addCases]

theorem rectangular_literal_normalization {p s : ℕ} {K F : IntermediateField ℚ ℝ}
    (h₀ : K ≤ F) (V : Matrix (Fin p) (Fin s) K) (μ : Fin p → K) (ν : Fin s → K)
    (v : Fin (p+s) → F)
    (hv : ∀ i, (v i : ℝ) = (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)⁻¹) :
    (fun i j => (unaryGauge (fun i j => IntermediateField.inclusion h₀ (block V i j)) v i j : ℝ)) =
      block (RectangularWeightedNormNormalization.normalized (realRectangular V)
        (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) :=
  inverse_norm_gauge_real h₀ V μ ν v hv

/-- The exact original consumer destructuring, pointwise conversion and hr 0
call compile against the constructed source theorem. -/
theorem original_consumer_singleton_call {p s d : ℕ} [Nonempty (Fin p)] [Nonempty (Fin s)]
    {K : IntermediateField ℚ ℝ} (basis : Module.Basis (Fin d) ℚ K)
    (V : Matrix (Fin p) (Fin s) K) (hV : ∀ i j, 0 < (V i j : ℝ))
    (μ : Fin p → K) (ν : Fin s → K) (hμ : ∀ i, 0 < (μ i : ℝ)) (hν : ∀ j, 0 < (ν j : ℝ)) (m : ℕ) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K ≤ F) (e : ℕ) (bF : Module.Basis (Fin e) ℚ F)
      (C : Matrix (Fin (p+s)) (Fin (p+s)) F) (hs : ∀ i j, C i j = C j i),
      (∀ i j, (C i j : ℝ) = block (RectangularWeightedNormNormalization.normalized
        (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) i j) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun _ : Fin 1 => Twins.quotientMatrix C hs) (fun l : Fin 0 => l.elim0)
          (Twins.quotientWeight C (fun i => IntermediateField.inclusion h₀ (weights μ ν i) *
            (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^m)))
        (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν))) := by
  obtain ⟨F,h₀,e,bF,C,hs,hc,hr⟩ := exists_rectangular_quotient_moment_sources
    basis V hV μ ν hμ hν (fun _ : Fin 1 => m)
  have hc' := fun i j => congrFun (congrFun hc i) j
  obtain ⟨r⟩ := hr 0
  exact ⟨F,h₀,e,bF,C,hs,hc',⟨r⟩⟩

end PlanarHom.NormalizedMomentProgramRegressions
