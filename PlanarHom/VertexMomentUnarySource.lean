import PlanarHom.EndpointUnarySource

/-! NEW reconstruction: a fixed existing unary power is attached to every
original vertex, including isolates, by actual raw-codec machines. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.EndpointUnarySource
open Complexity Complexity.MixedCode PairProjectionMachines EndpointLoopMachines

/-- A fixed number of copies of every original vertex; no edge-incidence
assumption excludes isolated vertices. -/
def momentVertices (power : ℕ) (g : MixedCode) : List ℕ :=
  (((List.range g.vertices).reverse).map (List.replicate power)).flatten

def momentTransform {u : ℕ} (selected : Fin u) (power : ℕ) (g : MixedCode) : MixedCode :=
  addUnaryAt selected.val (momentVertices power g) g

theorem fp_momentVertices (power : ℕ) : FP encoding BitEncoding.nat.list (momentVertices power) := by
  have hr := MixedCode.fp_vertices.comp UnaryRangeMachines.fp_range
  exact (hr.comp (ListMapMachines.fp_map BitEncoding.nat BitEncoding.nat.list _ (fp_repeat power))).comp
    (ListFlattenMachines.fp_flatten BitEncoding.nat)

theorem fp_momentTransform {u : ℕ} (selected : Fin u) (power : ℕ) :
    FP encoding encoding (momentTransform selected power) :=
  ((fp_momentVertices power).pair (fp_id encoding)).comp (fp_addUnaryAt selected.val)

theorem momentVertices_lt (power : ℕ) (g : MixedCode) :
    ∀ r ∈ momentVertices power g, r < g.vertices := by
  intro r hr
  obtain ⟨xs,hxs,hr⟩ := List.mem_flatten.mp hr
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hxs
  have hrv : r = v := (List.mem_replicate.mp hr).2
  subst r
  exact List.mem_range.mp (List.mem_reverse.mp hv)

theorem momentTransform_planar {b u : ℕ} (selected : Fin u) (power : ℕ)
    (g : MixedCode) (hg : g.PlanarValid b u) :
    (momentTransform selected power g).PlanarValid b u :=
  addUnaryAt_planar selected _ g hg (momentVertices_lt power g)

/-- The exact occurrence count is power times the original vertex count. -/
theorem momentVertices_length (power : ℕ) (g : MixedCode) :
    (momentVertices power g).length = power * g.vertices := by
  have hl (xs : List ℕ) : ((xs.map (List.replicate power)).flatten).length = power * xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.mul_add, Nat.add_comm]
  simpa only [momentVertices, List.length_reverse, List.length_range] using hl (List.range g.vertices).reverse

theorem momentTransform_unaries_length {u : ℕ} (selected : Fin u) (power : ℕ) (g : MixedCode) :
    (momentTransform selected power g).unaries.length = g.unaries.length + power * g.vertices := by
  simp only [momentTransform, addUnaryAt, List.length_append, List.length_map, momentVertices_length]

variable {C R : Type} [Fintype C] [CommSemiring R]

omit [Fintype C] in
theorem momentVertices_product (power : ℕ) (g : MixedCode) (v : C → R) (σ : Fin g.vertices → C) :
    ((momentVertices power g).map (unaryScalar g.vertices v σ)).prod =
      ∏ i : Fin g.vertices, (v (σ i))^power := by
  unfold momentVertices
  simp only [List.map_flatten, List.prod_flatten, List.map_map, Function.comp_def,
    List.map_replicate, List.prod_replicate]
  rw [List.map_reverse,List.prod_reverse,prod_map_get]
  apply Fintype.prod_equiv (finCongr (List.length_range (n := g.vertices)))
  intro i
  have hi : i.val < g.vertices := by simpa using i.isLt
  simp [unaryScalar,List.get_eq_getElem,List.getElem_range,hi]
  rfl

/-- A repeated existing unary multiplies each background exactly once by its
power, independently of degree and including zero-edge/zero-vertex inputs. -/
theorem evaluate_momentTransform {b u : ℕ} (selected : Fin u) (power : ℕ)
    (g : MixedCode) (hg : g.Valid b u)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R)
    (hout : (momentTransform selected power g).Valid b u) :
    (momentTransform selected power g).evaluate hout M U w =
      g.evaluate hg M U (fun i => w i * (U selected i)^power) := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro σ _
  change Fin g.vertices → C at σ
  change (∏ i : Fin g.vertices, w (σ i)) *
      (g.edges.map (binaryValue g.vertices b M σ)).prod *
      ((g.unaries ++ (momentVertices power g).map (fun r => (r,selected.val))).map
        (unaryValue g.vertices u U σ)).prod = _
  rw [List.map_append,List.prod_append,List.map_map]
  have hu : (momentVertices power g).map (unaryValue g.vertices u U σ ∘ fun r => (r,selected.val)) =
      (momentVertices power g).map (unaryScalar g.vertices (U selected) σ) := by
    apply List.map_congr_left
    intro r hr
    have hv := momentVertices_lt power g r hr
    simp [unaryValue,unaryScalar,hv,selected.isLt]
  rw [hu,momentVertices_product]
  simp only [Finset.prod_mul_distrib]
  ring

variable {K : Type} [Field K] [Algebra ℚ K] {dimension b u : ℕ}

/-- Actual preprocessing, one query, and field-coordinate recovery; no
availability hypothesis or unit-cost arithmetic convention is assumed. -/
def momentUnaryReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (selected : Fin u) (power : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis M U (fun i => w i * (U selected i)^power))
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits
    M U (fun i => w i * (U selected i)^power) M U w
    (fun g => ([],[momentTransform selected power g])) (fun p : Bits × List K => p.2.sum)
  · have hl := ((fp_momentTransform selected power).pair
      (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query = momentTransform selected power g := List.mem_singleton.mp hq
    subst query
    exact momentTransform_planar selected power g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (momentTransform_planar selected power g hg).1]
    exact evaluate_momentTransform selected power g hg.1 M U w _

end PlanarHom.EndpointUnarySource

namespace PlanarHom.EndpointUnarySource
open Complexity Complexity.MixedCode PairProjectionMachines FiniteLanguageAliases

/-- One actual source graph query carries both types of unary attachment. -/
def gaugeMomentTransform {b u : ℕ} (old : Fin b) (gauge moment : Fin u)
    (power : ℕ) (g : MixedCode) : MixedCode :=
  endpointTransform old gauge (momentTransform moment power g)

theorem fp_gaugeMomentTransform {b u : ℕ} (old : Fin b) (gauge moment : Fin u) (power : ℕ) :
    FP encoding encoding (gaugeMomentTransform old gauge moment power) :=
  (fp_momentTransform moment power).comp (fp_endpointTransform old gauge)

/-- The polynomial is extracted from the compiled machine's actual finite
syntax and running-time polynomial, in the real input/output bit encodings. -/
theorem gaugeMoment_bit_bound {b u : ℕ} (old : Fin b) (gauge moment : Fin u) (power : ℕ) :
    ∃ P : Polynomial ℕ, ∀ g : MixedCode,
      (encoding.encode (gaugeMomentTransform old gauge moment power g)).length ≤
        P.eval (encoding.encode g).length := by
  obtain ⟨machine⟩ := fp_gaugeMomentTransform old gauge moment power
  exact ⟨MachineComposition.outputLengthPolynomial machine,
    MachineComposition.encoded_output_length_le machine⟩

theorem gaugeMomentTransform_planar {b u : ℕ} (old : Fin b) (gauge moment : Fin u) (power : ℕ)
    (g : MixedCode) (hg : g.PlanarValid (b+1) u) :
    (gaugeMomentTransform old gauge moment power g).PlanarValid b u :=
  endpointTransform_planar old gauge _ (momentTransform_planar moment power g hg)

theorem gaugeMomentTransform_unaries_length {b u : ℕ}
    (old : Fin b) (gauge moment : Fin u) (power : ℕ) (g : MixedCode) :
    (gaugeMomentTransform old gauge moment power g).unaries.length =
      g.unaries.length + power * g.vertices +
        2 * (g.edges.filter (fun e => decide (e.2.2 = b))).length := by
  rw [gaugeMomentTransform,endpointTransform_unaries_length,momentTransform_unaries_length]
  rfl

variable {C R : Type} [Fintype C] [CommSemiring R]

theorem evaluate_gaugeMomentTransform {b u : ℕ}
    (old : Fin b) (gauge moment : Fin u) (power : ℕ) (g : MixedCode) (hg : g.Valid (b+1) u)
    (M : Fin b → Matrix C C R) (U : Fin u → C → R) (w : C → R)
    (hout : (gaugeMomentTransform old gauge moment power g).Valid b u) :
    (gaugeMomentTransform old gauge moment power g).evaluate hout M U w =
      g.evaluate hg (appendOne M (unaryGauge (M old) (U gauge))) U
        (fun i => w i * (U moment i)^power) := by
  have hm : (momentTransform moment power g).Valid (b+1) u :=
    addUnaryAt_valid moment _ g hg (momentVertices_lt power g)
  change (endpointTransform old gauge (momentTransform moment power g)).evaluate hout M U w = _
  rw [evaluate_endpointTransform old gauge _ hm M U w hout]
  exact evaluate_momentTransform moment power g hg _ U w hm

variable {K : Type} [Field K] [Algebra ℚ K] {dimension b u : ℕ}

/-- One-query original-field compiler for endpoint gauge plus fixed moments. -/
def gaugeMomentOneQueryReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (old : Fin b) (gauge moment : Fin u) (power : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (unaryGauge (M old) (U gauge))) U
        (fun i => w i * (U moment i)^power))
      (evaluationProblem basis M U w) := by
  apply planarReductionOfPipeline basis BitEncoding.bits
    (appendOne M (unaryGauge (M old) (U gauge))) U (fun i => w i * (U moment i)^power) M U w
    (fun g => ([],[gaugeMomentTransform old gauge moment power g])) (fun p : Bits × List K => p.2.sum)
  · have hl := ((fp_gaugeMomentTransform old gauge moment power).pair
      (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hl
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    have he : query = gaugeMomentTransform old gauge moment power g := List.mem_singleton.mp hq
    subst query
    exact gaugeMomentTransform_planar old gauge moment power g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (gaugeMomentTransform_planar old gauge moment power g hg).1]
    exact evaluate_gaugeMomentTransform old gauge moment power g hg.1 M U w _

end PlanarHom.EndpointUnarySource
