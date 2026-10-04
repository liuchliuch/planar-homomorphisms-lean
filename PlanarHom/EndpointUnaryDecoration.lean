import PlanarHom.UnaryLoopRealization
import PlanarHom.ListFlattenMachines

/-! Actual endpoint-unary decoration, with unchanged vertices and geometric
incidence. A source loop receives two unary occurrences, as required. -/
noncomputable section
open Classical
namespace PlanarHom.EndpointUnaryDecoration
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines

abbrev Edge := ℕ × (ℕ × ℕ)
abbrev edgeEncoding := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)
abbrev unaryEncoding := BitEncoding.nat.prod BitEncoding.nat

def rewriteEdge (new old : ℕ) (e : Edge) : Edge := (e.1,e.2.1,if e.2.2=new then old else e.2.2)
def extraUnaries (new unary : ℕ) (e : Edge) : List (ℕ × ℕ) :=
  if e.2.2=new then [(e.1,unary),(e.2.1,unary)] else []

def transform (new old unary : ℕ) (g : MixedCode) : MixedCode :=
  ⟨g.vertices,g.edges.map (rewriteEdge new old),g.unaries++g.edges.flatMap (extraUnaries new unary)⟩

theorem rewriteEdge_bound {b u : ℕ} (old : Fin b) (g : MixedCode) (hg : g.Valid (b+1) u)
    (e : Edge) (he : e∈g.edges) :
    (rewriteEdge b old.val e).1<g.vertices ∧ (rewriteEdge b old.val e).2.1<g.vertices ∧
      (rewriteEdge b old.val e).2.2<b := by
  have h := hg.1 e he
  refine ⟨h.1,h.2.1,?_⟩
  by_cases hl : e.2.2=b
  · simpa [rewriteEdge,hl] using old.isLt
  · simp only [rewriteEdge,if_neg hl]
    omega

theorem extraUnaries_bound {b u : ℕ} (unary : Fin u) (g : MixedCode) (hg : g.Valid (b+1) u)
    (e : Edge) (he : e∈g.edges) : ∀v∈extraUnaries b unary.val e,v.1<g.vertices ∧ v.2<u := by
  have h := hg.1 e he
  by_cases hl : e.2.2=b
  · simp only [extraUnaries,if_pos hl,List.mem_cons,List.not_mem_nil,or_false]
    rintro v (rfl | rfl)
    · exact ⟨h.1,unary.isLt⟩
    · exact ⟨h.2.1,unary.isLt⟩
  · simp [extraUnaries,hl]

theorem transform_valid {b u : ℕ} (old : Fin b) (unary : Fin u) (g : MixedCode)
    (hg : g.Valid (b+1) u) : (transform b old.val unary.val g).Valid b u := by
  constructor
  · intro e he
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    exact rewriteEdge_bound old g hg d hd
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hg.2 v hv
    · obtain ⟨e,he,hv⟩ := List.mem_flatMap.mp hv
      exact extraUnaries_bound unary g hg e he v hv

@[simp] theorem underlying_transform (new old unary : ℕ) (g : MixedCode) :
    (transform new old unary g).underlying=g.underlying := by
  simp [transform,MixedCode.underlying,List.map_map,rewriteEdge]

theorem transform_planar {b u : ℕ} (old : Fin b) (unary : Fin u) (g : MixedCode)
    (hg : g.PlanarValid (b+1) u) : (transform b old.val unary.val g).PlanarValid b u :=
  ⟨transform_valid old unary g hg.1,by simpa only [underlying_transform] using hg.2⟩

theorem fp_rewriteEdge (new old : ℕ) : FP edgeEncoding edgeEncoding (rewriteEdge new old) := by
  have hv := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hp := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hw := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hl := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have ht := (hl.pair (fp_const edgeEncoding BitEncoding.nat new)).comp NatListSumMachines.fp_equal
  exact hv.pair (hw.pair (ht.ite (fp_const edgeEncoding BitEncoding.nat old) hl))

theorem fp_extraUnaries (new unary : ℕ) : FP edgeEncoding unaryEncoding.list (extraUnaries new unary) := by
  have hv := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hp := fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hw := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hl := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have ht := (hl.pair (fp_const edgeEncoding BitEncoding.nat new)).comp NatListSumMachines.fp_equal
  have hu := fp_const edgeEncoding BitEncoding.nat unary
  have htail := ((hw.pair hu).pair (fp_const edgeEncoding unaryEncoding.list [])).comp
    (ListMutationMachines.fp_cons unaryEncoding)
  have hboth := ((hv.pair hu).pair htail).comp (ListMutationMachines.fp_cons unaryEncoding)
  exact ht.ite hboth (fp_const edgeEncoding unaryEncoding.list [])

theorem fp_transform (new old unary : ℕ) : FP MixedCode.encoding MixedCode.encoding (transform new old unary) := by
  have he := MixedCode.fp_edges.comp (ListMapMachines.fp_map edgeEncoding edgeEncoding _ (fp_rewriteEdge new old))
  have hx := (MixedCode.fp_edges.comp (ListMapMachines.fp_map edgeEncoding unaryEncoding.list _
    (fp_extraUnaries new unary))).comp (ListFlattenMachines.fp_flatten unaryEncoding)
  have hu := (MixedCode.fp_unaries.pair hx).comp (ListMutationMachines.fp_append unaryEncoding)
  exact (MixedCode.fp_vertices.pair (he.pair hu)).transportOutput (fun _ => rfl)

variable {C R : Type} [Fintype C] [CommSemiring R]

def decorated (M : Matrix C C R) (U : C → R) : Matrix C C R := fun i j => U i*M i j*U j

theorem edge_value {b u : ℕ} (old : Fin b) (unary : Fin u) (g : MixedCode)
    (hg : g.Valid (b+1) u) (M : Fin b → Matrix C C R) (U : Fin u → C → R)
    (σ : Fin g.vertices → C) (e : Edge) (he : e∈g.edges) :
    binaryValue g.vertices (b+1) (appendOne M (decorated (M old) (U unary))) σ e=
      binaryValue g.vertices b M σ (rewriteEdge b old.val e) *
        ((extraUnaries b unary.val e).map (unaryValue g.vertices u U σ)).prod := by
  have hv := hg.1 e he
  have hr := rewriteEdge_bound old g hg e he
  rw [binaryValue,dif_pos hv,binaryValue,dif_pos hr]
  by_cases hl : e.2.2=b
  · have hlast : (⟨e.2.2,hv.2.2⟩ : Fin (b+1))=Fin.last b := Fin.ext hl
    rw [hlast,appendOne_aux]
    have hvu : e.1<g.vertices ∧ unary.val<u := ⟨hv.1,unary.isLt⟩
    have hwu : e.2.1<g.vertices ∧ unary.val<u := ⟨hv.2.1,unary.isLt⟩
    simp only [extraUnaries,if_pos hl,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      unaryValue,dif_pos hvu,dif_pos hwu,mul_one,rewriteEdge,if_pos hl,decorated]
    ring
  · have heold : e.2.2<b := by omega
    have heq : (⟨e.2.2,hv.2.2⟩ : Fin (b+1))=Fin.castAdd 1 ⟨e.2.2,heold⟩ := rfl
    rw [heq,appendOne_old]
    simp [extraUnaries,rewriteEdge,hl]

theorem product_flatMap {A B : Type} (xs : List A) (f : A → List B) (w : B → R) :
    ((xs.flatMap f).map w).prod=(xs.map (fun a => ((f a).map w).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem evaluate_transform {b u : ℕ} (old : Fin b) (unary : Fin u) (g : MixedCode)
    (hg : g.Valid (b+1) u) (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R) :
    (transform b old.val unary.val g).evaluate (transform_valid old unary g hg) M U w=
      g.evaluate hg (appendOne M (decorated (M old) (U unary))) U w := by
  unfold MixedCode.evaluate
  apply Finset.sum_congr rfl
  intro σ _
  change Fin g.vertices → C at σ
  change (∏v,w (σ v)) *
    (((g.edges.map (rewriteEdge b old.val)).map (binaryValue g.vertices b M σ)).prod) *
    ((g.unaries++g.edges.flatMap (extraUnaries b unary.val)).map (unaryValue g.vertices u U σ)).prod=_
  rw [List.map_map,List.map_append,List.prod_append,product_flatMap]
  have ht : (g.edges.map (binaryValue g.vertices (b+1) (appendOne M (decorated (M old) (U unary))) σ)).prod=
      (g.edges.map (fun e => binaryValue g.vertices b M σ (rewriteEdge b old.val e))).prod *
      (g.edges.map (fun e => ((extraUnaries b unary.val e).map (unaryValue g.vertices u U σ)).prod)).prod := by
    rw [←List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    exact edge_value old unary g hg M U σ e he
  rw [ht]
  simp only [Function.comp_def]
  ring

variable {K : Type} [Field K] [Algebra ℚ K] {dimension b u : ℕ}

def reduction (basis : Module.Basis (Fin dimension) ℚ K) (M : Fin b → Matrix C C K)
    (U : Fin u → C → K) (w : C → K) (old : Fin b) (unary : Fin u) :
    PromisePolyTimeTuringReduction (evaluationProblem basis (appendOne M (decorated (M old) (U unary))) U w)
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits (appendOne M (decorated (M old) (U unary))) U w M U w
    (fun g => ([],[transform b old.val unary.val g])) (fun p : Bits × List K => p.2.sum)
  · have hl := ((fp_transform b old.val unary.val).pair (fp_const MixedCode.encoding MixedCode.encoding.list [])).comp
      (ListMutationMachines.fp_cons MixedCode.encoding)
    exact (fp_const MixedCode.encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query=transform b old.val unary.val g := List.mem_singleton.mp hq
    subst query
    exact transform_planar old unary g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (transform_valid old unary g hg.1)]
    exact evaluate_transform old unary g hg.1 M U w

end PlanarHom.EndpointUnaryDecoration
