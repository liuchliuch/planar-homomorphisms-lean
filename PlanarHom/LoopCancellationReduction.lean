import PlanarHom.LoopAdditionMachines
import PlanarHom.SelectedStretchSemantics
import PlanarHom.GraphNonadaptiveReduction
import PlanarHom.MaterializedFieldListMachines

/-! Literal loop factors cancel the original backgrounds, including on isolated
vertices, by an actual raw-bit one-query planar reduction. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.Complexity.MixedCode
open PlanarHom PairProjectionMachines
variable {C R : Type} [Fintype C] [CommSemiring R] {b u : ℕ}

theorem addLoops_valid (selected : Fin b) (g : MixedCode) (hg : g.Valid b u) :
    (g.addLoops selected.val).Valid b u := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact hg.1 e he
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
      have hv := List.mem_range.mp (List.mem_reverse.mp hr)
      exact ⟨hv,hv,selected.isLt⟩
  · exact hg.2

theorem added_loop_product (selected : Fin b) (g : MixedCode)
    (M : Fin b → Matrix C C R) (σ : Fin g.vertices → C) :
    ((((List.range g.vertices).reverse.map (fun r => (r,r,selected.val))).map
      (binaryValue g.vertices b M σ)).prod) =
      ∏ v : Fin g.vertices,M selected (σ v) (σ v) := by
  rw [List.map_map,List.map_reverse,List.prod_reverse,prod_map_get]
  apply Fintype.prod_equiv (finCongr (List.length_range (n:=g.vertices)))
  intro v
  have hv : v.val < g.vertices := by simpa using v.isLt
  simp [binaryValue,List.get_eq_getElem,List.getElem_range,hv,selected.isLt]
  rfl

/-- The background changes by exactly the selected diagonal factor. -/
theorem evaluate_addLoops (selected : Fin b) (g : MixedCode) (hg : g.Valid b u)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R) :
    (g.addLoops selected.val).evaluate (addLoops_valid selected g hg) M U w =
      g.evaluate hg M U (fun i => w i * M selected i i) := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro σ _
  change Fin g.vertices → C at σ
  change (∏ v : Fin g.vertices,w (σ v)) *
      (((g.edges ++ (List.range g.vertices).reverse.map (fun r => (r,r,selected.val))).map
        (binaryValue g.vertices b M σ)).prod) *
      (g.unaries.map (unaryValue g.vertices u U σ)).prod = _
  rw [List.map_append,List.prod_append,added_loop_product]
  simp only [Finset.prod_mul_distrib]
  ac_rfl

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- A diagonal inverse already in the jointly available language removes the
background through one loop at every old vertex. -/
def loopCancellationReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) (selected : Fin b)
    (hcancel : ∀ i,w i * M selected i i=1) :
    PromisePolyTimeTuringReduction (evaluationProblem basis M U (fun _=>1))
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits M U (fun _=>1) M U w
    (fun g => ([],[g.addLoops selected.val])) (fun p : Bits × List K => p.2.sum)
  · have hl := ((fp_addLoops selected.val).pair
        (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query=g.addLoops selected.val := List.mem_singleton.mp hq
    subst query
    exact addLoops_planar selected.val selected.isLt g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (addLoops_valid selected g hg.1),evaluate_addLoops selected g hg.1]
    simp only [hcancel]

end PlanarHom.Complexity.MixedCode
