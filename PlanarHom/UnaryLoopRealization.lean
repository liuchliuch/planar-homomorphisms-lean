import PlanarHom.LoopCancellationReduction
import PlanarHom.ListFilterMachines
import PlanarHom.NatListSumMachines
import PlanarHom.FiniteLanguageJointReductions

/-! Each occurrence of an appended diagonal unary is replaced by exactly one
loop. Background weights remain unchanged, including repeated occurrences. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity.MixedCode
open PlanarHom PairProjectionMachines FiniteLanguageAliases
variable {b u : ℕ}

def realizeUnaryLoops (u selected : ℕ) (g : MixedCode) : MixedCode :=
  ⟨g.vertices,g.edges++(g.unaries.filter (fun e=>decide (e.2=u))).map (fun e=>(e.1,e.1,selected)),
    g.unaries.filter (fun e=>decide (e.2≠u))⟩

theorem realizeUnaryLoops_valid (selected : Fin b) (g : MixedCode) (hg : g.Valid b (u+1)) :
    (realizeUnaryLoops u selected.val g).Valid b u := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact hg.1 e he
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
      exact ⟨(hg.2 v (List.mem_filter.mp hv).1).1,(hg.2 v (List.mem_filter.mp hv).1).1,selected.isLt⟩
  · intro e he
    have h := hg.2 e (List.mem_filter.mp he).1
    have hn : e.2≠u := of_decide_eq_true (List.mem_filter.mp he).2
    exact ⟨h.1,by omega⟩

theorem realizeUnaryLoops_planar (selected : Fin b) (g : MixedCode) (hg : g.PlanarValid b (u+1)) :
    (realizeUnaryLoops u selected.val g).PlanarValid b u := by
  refine ⟨realizeUnaryLoops_valid selected g hg.1,?_⟩
  have hp := addLoopsAt_planar selected.val selected.isLt
    ((g.unaries.filter (fun e=>decide (e.2=u))).map Prod.fst) g hg (by
      intro r hr
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
      exact (hg.1.2 v (List.mem_filter.mp hv).1).1)
  have he : (realizeUnaryLoops u selected.val g).underlying =
      (addLoopsAt selected.val ((g.unaries.filter (fun e=>decide (e.2=u))).map Prod.fst) g).underlying := by
    simp only [realizeUnaryLoops,addLoopsAt,List.map_map]
    rfl
  rw [he]
  exact hp.2

variable {C R : Type} [Fintype C] [CommSemiring R]
theorem evaluate_realizeUnaryLoops (selected : Fin b) (g : MixedCode) (hg : g.Valid b (u+1))
    (M : Fin b→Matrix C C R) (U : Fin u→C→R) (w : C→R) :
    (realizeUnaryLoops u selected.val g).evaluate (realizeUnaryLoops_valid selected g hg) M U w =
      g.evaluate hg M (appendOne U (fun i=>M selected i i)) w := by
  rw [evaluate_eq_unary_product_sum g hg u]
  unfold evaluate unaryRemainder selectedUnaryProduct
  apply Finset.sum_congr rfl
  intro σ _
  change Fin g.vertices→C at σ
  change (∏ v : Fin g.vertices,w (σ v))*
      (((g.edges++(g.unaries.filter (fun e=>decide (e.2=u))).map (fun e=>(e.1,e.1,selected.val))).map
        (binaryValue g.vertices b M σ)).prod)*
      ((g.unaries.filter (fun e=>decide (e.2≠u))).map (unaryValue g.vertices u U σ)).prod = _
  rw [List.map_append,List.prod_append,List.map_map]
  have ho : ((g.unaries.filter (fun e=>decide (e.2≠u))).map (unaryValue g.vertices u U σ)) =
      ((g.unaries.filter (fun e=>decide (e.2≠u))).map
        (unaryValue g.vertices (u+1) (appendOne U (fun i=>M selected i i)) σ)) := by
    apply List.map_congr_left
    intro e he
    have hv := hg.2 e (List.mem_filter.mp he).1
    have hn : e.2≠u := of_decide_eq_true (List.mem_filter.mp he).2
    have hu : e.2<u := by omega
    simp only [unaryValue,hv.1,hv.2,hu,and_self,↓reduceDIte]
    change U ⟨e.2,hu⟩ _=appendOne U _ (Fin.castAdd 1 ⟨e.2,hu⟩) _
    rw [appendOne_old]
  have hs : ((g.unaries.filter (fun e=>decide (e.2=u))).map
      (fun e=>binaryValue g.vertices b M σ (e.1,e.1,selected.val))) =
      ((g.unaries.filter (fun e=>decide (e.2=u))).map
        (unaryValue g.vertices (u+1) (appendOne U (fun i=>M selected i i)) σ)) := by
    apply List.map_congr_left
    intro e he
    have hv := hg.2 e (List.mem_filter.mp he).1
    have hl : e.2=u := of_decide_eq_true (List.mem_filter.mp he).2
    simp only [binaryValue,unaryValue,hv.1,hv.2,selected.isLt,and_self,↓reduceDIte]
    have heq : (⟨e.2,hv.2⟩ : Fin (u+1))=Fin.last u := Fin.ext hl
    rw [heq,appendOne_aux]
  simp only [Function.comp_def]
  rw [ho,hs]
  ring

theorem fp_realizeUnaryLoops (u selected : ℕ) : FP encoding encoding (realizeUnaryLoops u selected) := by
  let item := BitEncoding.nat.prod BitEncoding.nat
  let edge := BitEncoding.nat.prod item
  have heq : FP item BitEncoding.bool (fun e : ℕ×ℕ=>decide (e.2=u)) :=
    ((fp_snd BitEncoding.nat BitEncoding.nat).pair (fp_const item BitEncoding.nat u)).comp
      NatListSumMachines.fp_equal
  have hne : FP item BitEncoding.bool (fun e : ℕ×ℕ=>decide (e.2≠u)) :=
    (heq.comp (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool Bool.not)).congr (fun _=>by simp)
  have hi : FP item edge (fun e : ℕ×ℕ=>(e.1,e.1,selected)) :=
    (fp_fst BitEncoding.nat BitEncoding.nat).pair
      ((fp_fst BitEncoding.nat BitEncoding.nat).pair (fp_const item BitEncoding.nat selected))
  have loops := (fp_unaries.comp (ListFilterMachines.fp_filter item _ heq)).comp
    (ListMapMachines.fp_map item edge _ hi)
  have edges := (fp_edges.pair loops).comp (ListMutationMachines.fp_append edge)
  have unaries := fp_unaries.comp (ListFilterMachines.fp_filter item _ hne)
  exact (fp_vertices.pair (edges.pair unaries)).transportOutput (fun _=>rfl)

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
def diagonalUnaryAppendReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K) (selected : Fin b) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis M (appendOne U (fun i=>M selected i i)) w)
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits M (appendOne U (fun i=>M selected i i)) w M U w
    (fun g=>([],[realizeUnaryLoops u selected.val g])) (fun p : Bits×List K=>p.2.sum)
  · have hl := ((fp_realizeUnaryLoops u selected.val).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query=realizeUnaryLoops u selected.val g := List.mem_singleton.mp hq
    subst query
    exact realizeUnaryLoops_planar selected g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (realizeUnaryLoops_valid selected g hg.1)]
    exact evaluate_realizeUnaryLoops selected g hg.1 M U w

end PlanarHom.Complexity.MixedCode
