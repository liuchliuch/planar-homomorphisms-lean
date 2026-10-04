import PlanarHom.EndpointLoopAvailability
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.PrescribedDomainAliasReductions

/-! Endpoint loop decoration with unchanged original prescribed domains and
companion policies. Only the source label's own loop permissions are needed. -/
noncomputable section
open Classical
namespace PlanarHom.EndpointLoopMachines
open Complexity Complexity.MixedCode FiniteLanguageAliases FiniteLabelLookupMachines PrescribedDomains
variable {b u d : ℕ}

theorem addLoopsAt_valid (old : Fin b) (xs : List ℕ) (g : MixedCode) (hg : g.Valid b u)
    (hx : ∀r∈xs,r<g.vertices) : (addLoopsAt old.val xs g).Valid b u := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact hg.1 e he
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
      exact ⟨hx r hr,hx r hr,old.isLt⟩
  · exact hg.2

theorem typed_addLoopsAt (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (old : Fin b) (xs : List ℕ) (g : MixedCode) (hg : g.Valid b u) (δ : Fin g.vertices→Fin d)
    (ht : Typed B T g hg δ) (hx : ∀r∈xs,r<g.vertices) (hloop : ∀x,B old x x) :
    Typed B T (addLoopsAt old.val xs g) (addLoopsAt_valid old xs g hg hx) δ := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact ht.1 e he
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
      exact hloop (δ ⟨r,hx r hr⟩)
  · exact ht.2

theorem transform_withDomains (old : Fin b) (k : ℕ) (g : MixedCode) (δ : Fin g.vertices→Fin d) :
    transform old k (withDomains (unaryTypes:=u) g δ)=
      withDomains (unaryTypes:=u) (transform old k g) δ := rfl

theorem policy_dropAux (B : Fin b→Fin d→Fin d→Prop) (old : Fin b) :
    B ∘ dropAux old=appendOne B (B old) := by
  funext l
  refine Fin.lastCases ?_ (fun i=>?_) l
  · simp [dropAux,appendOne_aux]
  · simp only [Function.comp_apply,dropAux,Fin.lastCases_castSucc,id_eq]
    change B i=appendOne B (B old) (Fin.castAdd 1 i)
    rw [appendOne_old]

theorem encoded_transform (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (old : Fin b) (k : ℕ) (g : MixedCode) (h : EncodedGraph (appendOne B (B old)) T g)
    (hloop : ∀x,B old x x) : EncodedGraph B T (transform old k g) := by
  obtain ⟨original,hg,δ,ht,hp,hd⟩ := h
  rw [encoding.decode_encode] at hd
  have he : g=withDomains (unaryTypes:=u) original δ := Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [transform_withDomains]
  have htype : ∀l x y,appendOne B (B old) l x y→B (dropAux old l) x y := by
    intro l x y h
    exact (congrFun (congrFun (congrFun (policy_dropAux B old) l) x) y).mpr h
  have hrel := Typed.relabelBinaryAlias (dropAux old) htype ht
  have hvalid := relabelBinary_valid _ hg (lookup_finTable_lt (dropAux old))
  have hbound := loopVertices_lt original hg b k
  have htyped := typed_addLoopsAt B T old (loopVertices b k original)
    (original.relabelBinary (finTable (dropAux old))) hvalid δ hrel hbound hloop
  exact encodedInput_encode_withDomains htyped (transform_planar old k original ⟨hg,hp⟩).2

variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K] {dimension : ℕ}
def domainReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix C C K) (U : Fin u→C→K) (w : C→K)
    (D : Fin d→Set C) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (old : Fin b) (k : ℕ) (hloop : ∀x,B old x x) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis (appendOne M (decorated (M old) k)) U w D (appendOne B (B old)) T)
      (domainEvaluationProblem basis M U w D B T) := by
  let HT := EncodedGraph (appendOne B (B old)) T
  let HS := EncodedGraph B T
  have vt : ∀g,HT g→g.Valid (b+1) (u+d) := fun _ h=>(h.planarValid _ _).1
  have vs : ∀g,HS g→g.Valid b (u+d) := fun _ h=>(h.planarValid _ _).1
  have hq : ∀g,HT g→HS (transform old k g) := fun g h=>encoded_transform B T old k g h hloop
  have hpre : FP encoding (BitEncoding.bits.prod encoding.list) (fun g=>([],[transform old k g])) := by
    have hl := ((fp_transform old k).pair (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  let r := reductionOfPipeline basis BitEncoding.bits (appendOne M (decorated (M old) k)) (extendedUnaries U D) w
    M (extendedUnaries U D) w HT HS vt vs (fun g=>([],[transform old k g]))
    (fun p : Bits×List K=>p.2.sum) hpre
    ((PairProjectionMachines.fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis))
    (by intro g hg query h; obtain rfl := List.mem_singleton.mp h; exact hq g hg)
    (by
      intro g hg
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [totalEvaluation_valid _ _ _ _ (vs _ (hq g hg))]
      exact evaluate_transform old k g (vt g hg) M (extendedUnaries U D) w (vs _ (hq g hg)))
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph (appendOne B (B old)) T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

end PlanarHom.EndpointLoopMachines
