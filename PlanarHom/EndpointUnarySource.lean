import PlanarHom.EndpointLoopSemantics
import PlanarHom.FixedSquareNormSource

/-!
# Endpoint unary and all-vertex moment compilers — NEW reconstruction

Actual raw mixed-code programs. Endpoint decorations preserve loops twice;
all-vertex decorations retain isolated vertices. The unary labels are existing
source constraints, not freely supplied pins or source-availability oracles.
-/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.EndpointUnarySource
open Complexity Complexity.MixedCode PairProjectionMachines FiniteLanguageAliases
open FiniteLabelLookupMachines EndpointLoopMachines

/-- Append actual unary occurrences at the listed vertices, preserving all
original occurrences, binary edges, and the vertex count. -/
def addUnaryAt (selected : ℕ) (xs : List ℕ) (g : MixedCode) : MixedCode :=
  ⟨g.vertices, g.edges, g.unaries ++ xs.map (fun r => (r,selected))⟩

@[simp] theorem addUnaryAt_vertices (selected : ℕ) (xs : List ℕ) (g : MixedCode) :
    (addUnaryAt selected xs g).vertices = g.vertices := rfl

@[simp] theorem addUnaryAt_edges (selected : ℕ) (xs : List ℕ) (g : MixedCode) :
    (addUnaryAt selected xs g).edges = g.edges := rfl

/-- Actual binary-header/payload list-map and append machines. -/
theorem fp_addUnaryAt (selected : ℕ) :
    FP (BitEncoding.nat.list.prod encoding) encoding
      (fun p : List ℕ × MixedCode => addUnaryAt selected p.1 p.2) := by
  let input := BitEncoding.nat.list.prod encoding
  let unary := BitEncoding.nat.prod BitEncoding.nat
  have hi : FP BitEncoding.nat unary (fun r => (r,selected)) :=
    (fp_id BitEncoding.nat).pair (fp_const _ _ selected)
  have xs := fp_fst BitEncoding.nat.list encoding
  have g := fp_snd BitEncoding.nat.list encoding
  have us := xs.comp (ListMapMachines.fp_map BitEncoding.nat unary _ hi)
  have out := ((g.comp MixedCode.fp_unaries).pair us).comp (ListMutationMachines.fp_append unary)
  exact ((g.comp MixedCode.fp_vertices).pair ((g.comp MixedCode.fp_edges).pair out)).transportOutput (fun _ => rfl)

theorem addUnaryAt_valid {b u : ℕ} (selected : Fin u) (xs : List ℕ)
    (g : MixedCode) (hg : g.Valid b u) (hx : ∀ r ∈ xs, r < g.vertices) :
    (addUnaryAt selected.val xs g).Valid b u := by
  refine ⟨hg.1, ?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hg.2 e he
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    exact ⟨hx r hr, selected.isLt⟩

theorem addUnaryAt_planar {b u : ℕ} (selected : Fin u) (xs : List ℕ)
    (g : MixedCode) (hg : g.PlanarValid b u) (hx : ∀ r ∈ xs, r < g.vertices) :
    (addUnaryAt selected.val xs g).PlanarValid b u :=
  ⟨addUnaryAt_valid selected xs g hg.1 hx, hg.2⟩

/-- Replace just the appended binary label and attach one existing unary to
both endpoints of each replaced occurrence. -/
def endpointTransform {b u : ℕ} (old : Fin b) (gauge : Fin u) (g : MixedCode) : MixedCode :=
  addUnaryAt gauge.val (loopVertices b 1 g) (g.relabelBinary (finTable (dropAux old)))

theorem fp_endpointTransform {b u : ℕ} (old : Fin b) (gauge : Fin u) :
    FP encoding encoding (endpointTransform old gauge) :=
  ((fp_loopVertices b 1).pair (fp_relabelBinary (finTable (dropAux old)))).comp
    (fp_addUnaryAt gauge.val)

theorem endpointTransform_planar {b u : ℕ} (old : Fin b) (gauge : Fin u)
    (g : MixedCode) (hg : g.PlanarValid (b+1) u) :
    (endpointTransform old gauge g).PlanarValid b u := by
  apply addUnaryAt_planar gauge _ _ (relabelBinary_planar _ hg (lookup_finTable_lt (dropAux old)))
  exact loopVertices_lt g hg.1 b 1

variable {C R : Type} [Fintype C] [CommSemiring R]

def unaryGauge (A : Matrix C C R) (v : C → R) : Matrix C C R :=
  fun i j => v i * A i j * v j

def unaryScalar (n : ℕ) (v : C → R) (σ : Fin n → C) (r : ℕ) : R :=
  if h : r < n then v (σ ⟨r,h⟩) else 0

omit [Fintype C] in
theorem edge_value_gauge {b n : ℕ} (M : Fin b → Matrix C C R)
    (old : Fin b) (v : C → R) (σ : Fin n → C) (e : ℕ × ℕ × ℕ)
    (hv : e.1 < n ∧ e.2.1 < n ∧ e.2.2 < b+1) :
    binaryValue n (b+1) (appendOne M (M old)) σ e *
      (if e.2.2 = b then unaryScalar n v σ e.1 * unaryScalar n v σ e.2.1 else 1) =
      binaryValue n (b+1) (appendOne M (unaryGauge (M old) v)) σ e := by
  rw [binaryValue, dif_pos hv, binaryValue, dif_pos hv]
  by_cases he : e.2.2 = b
  · have hl : (⟨e.2.2,hv.2.2⟩ : Fin (b+1)) = Fin.last b := Fin.ext he
    simp only [if_pos he, hl, appendOne_aux, unaryScalar, dif_pos hv.1, dif_pos hv.2.1, unaryGauge]
    ring
  · have hlt : e.2.2 < b := by omega
    have hl : (⟨e.2.2,hv.2.2⟩ : Fin (b+1)) = Fin.castAdd 1 ⟨e.2.2,hlt⟩ := rfl
    simp only [if_neg he, hl, appendOne_old, mul_one]

/-- Assignment-level equality: the root background is not duplicated; a loop
has two endpoint unaries at its one existing vertex. -/
theorem evaluate_endpointTransform {b u : ℕ} (old : Fin b) (gauge : Fin u)
    (g : MixedCode) (hg : g.Valid (b+1) u)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R)
    (hout : (endpointTransform old gauge g).Valid b u) :
    (endpointTransform old gauge g).evaluate hout M U w =
      g.evaluate hg (appendOne M (unaryGauge (M old) (U gauge))) U w := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro σ _
  change Fin g.vertices → C at σ
  change (∏ v : Fin g.vertices, w (σ v)) *
      (((g.relabelBinary (finTable (dropAux old))).edges).map
        (binaryValue g.vertices b M σ)).prod *
      ((g.unaries ++ (loopVertices b 1 g).map (fun r => (r,gauge.val))).map
        (unaryValue g.vertices u U σ)).prod = _
  rw [List.map_append, List.prod_append, List.map_map]
  have hbase : (((g.relabelBinary (finTable (dropAux old))).edges).map
      (binaryValue g.vertices b M σ)) =
      g.edges.map (binaryValue g.vertices (b+1) (appendOne M (M old)) σ) := by
    change (g.edges.map (fun e => (e.1,e.2.1,lookup (finTable (dropAux old)) e.2.2))).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    have hv := hg.1 e he
    have hl := lookup_finTable (dropAux old) ⟨e.2.2,hv.2.2⟩
    have ht : e.1 < g.vertices ∧ e.2.1 < g.vertices ∧ lookup (finTable (dropAux old)) e.2.2 < b :=
      ⟨hv.1,hv.2.1,lookup_finTable_lt _ _ hv.2.2⟩
    simp only [Function.comp_apply]
    rw [binaryValue, dif_pos ht, binaryValue, dif_pos hv]
    have hf : (⟨lookup (finTable (dropAux old)) e.2.2,ht.2.2⟩ : Fin b) =
        dropAux old ⟨e.2.2,hv.2.2⟩ := Fin.ext hl
    change M (⟨lookup (finTable (dropAux old)) e.2.2,ht.2.2⟩ : Fin b)
      (σ ⟨e.1,hv.1⟩) (σ ⟨e.2.1,hv.2.1⟩) = _
    rw [hf]
    exact congrFun (congrFun (congrFun (sourceLabels M old) ⟨e.2.2,hv.2.2⟩)
      (σ ⟨e.1,hv.1⟩)) (σ ⟨e.2.1,hv.2.1⟩)
  have hu : (loopVertices b 1 g).map (unaryValue g.vertices u U σ ∘ fun r => (r,gauge.val)) =
      (loopVertices b 1 g).map (unaryScalar g.vertices (U gauge) σ) := by
    apply List.map_congr_left
    intro r hr
    have hv := loopVertices_lt g hg b 1 r hr
    simp [unaryValue, unaryScalar, hv, gauge.isLt]
  rw [hbase, hu, loopVertices_product]
  simp only [pow_one]
  have hp : (g.edges.map (binaryValue g.vertices (b+1) (appendOne M (M old)) σ)).prod *
      (g.edges.map (fun e => if e.2.2 = b then
        unaryScalar g.vertices (U gauge) σ e.1 * unaryScalar g.vertices (U gauge) σ e.2.1 else 1)).prod =
      (g.edges.map (binaryValue g.vertices (b+1) (appendOne M (unaryGauge (M old) (U gauge))) σ)).prod := by
    rw [← List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    exact edge_value_gauge M old (U gauge) σ e (hg.1 e he)
  calc
    _ = (∏ v : Fin g.vertices, w (σ v)) *
        ((g.edges.map (binaryValue g.vertices (b+1) (appendOne M (M old)) σ)).prod *
          (g.edges.map (fun e => if e.2.2 = b then
            unaryScalar g.vertices (U gauge) σ e.1 * unaryScalar g.vertices (U gauge) σ e.2.1 else 1)).prod) *
        (g.unaries.map (unaryValue g.vertices u U σ)).prod := by ring
    _ = _ := by rw [hp]

variable {K : Type} [Field K] [Algebra ℚ K] {dimension b u : ℕ}

/-- Genuine charged original-codec reduction for an endpoint unary gauge. -/
def endpointUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (old : Fin b) (gauge : Fin u) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (unaryGauge (M old) (U gauge))) U w)
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits
    (appendOne M (unaryGauge (M old) (U gauge))) U w M U w
    (fun g => ([],[endpointTransform old gauge g])) (fun p : Bits × List K => p.2.sum)
  · have hl := ((fp_endpointTransform old gauge).pair
      (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query = endpointTransform old gauge g := List.mem_singleton.mp hq
    subst query
    exact endpointTransform_planar old gauge g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (endpointTransform_planar old gauge g hg).1]
    exact evaluate_endpointTransform old gauge g hg.1 M U w _

end PlanarHom.EndpointUnarySource

namespace PlanarHom.EndpointUnarySource
open Complexity Complexity.MixedCode EndpointLoopMachines

/-- Exact endpoint occurrence count, not a simple-graph degree bound. -/
theorem loopVertices_one_length (selected : ℕ) (g : MixedCode) :
    (loopVertices selected 1 g).length =
      2 * (g.edges.filter (fun e => decide (e.2.2 = selected))).length := by
  have hone (xs : List ℕ) : (xs.map (List.replicate 1)).flatten = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa using congrArg (List.cons x) ih
  have hlen (es : List (ℕ × ℕ × ℕ)) : (GraphDegreeMachines.endpoints es).length = 2 * es.length := by
    induction es with
    | nil => rfl
    | cons e es ih => simp [GraphDegreeMachines.endpoints,List.flatMap_cons] at ih ⊢; omega
  rw [loopVertices,hone,hlen]

/-- Original explicit unaries plus exactly two per selected edge occurrence. -/
theorem endpointTransform_unaries_length {b u : ℕ} (old : Fin b) (gauge : Fin u) (g : MixedCode) :
    (endpointTransform old gauge g).unaries.length =
      g.unaries.length + 2 * (g.edges.filter (fun e => decide (e.2.2 = b))).length := by
  simp only [endpointTransform,addUnaryAt,relabelBinary,List.length_append,List.length_map,
    loopVertices_one_length]

end PlanarHom.EndpointUnarySource
