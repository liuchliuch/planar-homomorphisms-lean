import PlanarHom.LoopCancellationReduction
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.PromiseReductionTransport

/-! Background-cancelling loops preserve every original vertex domain. Loop
admissibility is explicit in the original source policy, not added by a query. -/
noncomputable section
open Classical
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
variable {b u d : ℕ}

theorem Typed.addLoops {B : Fin b→Fin d→Fin d→Prop} {T : Fin u→Fin d→Prop}
    {g : MixedCode} {hg : g.Valid b u} {δ : Fin g.vertices→Fin d}
    (ht : Typed B T g hg δ) (selected : Fin b) (hloop : ∀x,B selected x x) :
    Typed B T (g.addLoops selected.val) (addLoops_valid selected g hg) δ := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact ht.1 e he
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
      simpa using hloop (δ ⟨r,List.mem_range.mp (List.mem_reverse.mp hr)⟩)
  · exact ht.2

theorem addLoops_withDomains (selected : ℕ) (g : MixedCode) (δ : Fin g.vertices→Fin d) :
    (withDomains (unaryTypes:=u) g δ).addLoops selected =
      withDomains (unaryTypes:=u) (g.addLoops selected) δ := rfl

theorem EncodedGraph.addLoops {B : Fin b→Fin d→Fin d→Prop} {T : Fin u→Fin d→Prop}
    {g : MixedCode} (h : EncodedGraph B T g) (selected : Fin b) (hloop : ∀x,B selected x x) :
    EncodedGraph B T (g.addLoops selected.val) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [MixedCode.encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=u) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [addLoops_withDomains]
  exact encodedInput_encode_withDomains (ht.addLoops selected hloop)
    (addLoops_planar selected.val selected.isLt original ⟨hg,hp⟩).2

end PlanarHom.PrescribedDomains
namespace PlanarHom.Complexity.MixedCode
open PlanarHom PrescribedDomains PairProjectionMachines
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {b u d dimension : ℕ}

def domainLoopCancellationReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (D : Fin d→Set C) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (selected : Fin b) (hloop : ∀x,B selected x x) (hcancel : ∀i,w i*M selected i i=1) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U (fun _=>1) D B T)
      (domainEvaluationProblem basis M U w D B T) := by
  let H := EncodedGraph B T
  have hv : ∀g,H g→g.Valid b (u+d) := fun _ h=>(h.planarValid B T).1
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) (fun g=>([],[g.addLoops selected.val])) := by
    have hl := ((fp_addLoops selected.val).pair (fp_const encoding encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  let r := reductionOfPipeline basis BitEncoding.bits M (extendedUnaries U D) (fun _=>1)
    M (extendedUnaries U D) w H H hv hv (fun g=>([],[g.addLoops selected.val]))
    (fun p : Bits×List K=>p.2.sum) hp
    ((fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis))
    (by intro g hg query hq; obtain rfl := List.mem_singleton.mp hq; exact hg.addLoops selected hloop)
    (by
      intro g hg
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [totalEvaluation_valid _ _ _ _ (addLoops_valid selected g (hv g hg))]
      have he := evaluate_addLoops selected g (hv g hg) M (extendedUnaries U D) w
      simpa only [hcancel] using he)
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph B T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.Complexity.MixedCode
