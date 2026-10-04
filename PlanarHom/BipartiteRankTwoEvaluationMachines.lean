import PlanarHom.BipartiteRankTwoEvaluationSemantics
import PlanarHom.GraphComponentTractability

/-! NEW actual polynomial-time weighted bipartite rank-two evaluator. It
computes a parity assignment, degrees, two orientation products, and their sum.
The existing connected-component compiler handles disconnected and empty input. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.BipartiteRankTwoTractability
open Complexity Complexity.MixedCode PairProjectionMachines ArithmeticCircuitPrimitives
open PlanarityParitySolver GraphComponentCode
variable {k l dimension : ℕ} {K : Type} [Field K] [Algebra ℚ K]

abbrev rowCode := BitEncoding.bool.prod BitEncoding.unaryNat
abbrev contextCode := MixedCode.encoding.prod assignmentCode

def vertexData (p : (MixedCode × Assignment) × ℕ) : Bool × ℕ :=
  (lookup p.1.2 p.2,GraphDegreeMachines.degree p.1.1 p.2)

def table (g : MixedCode) : List (Bool × ℕ) :=
  ((List.range g.vertices).reverse).map (fun v=>vertexData ((g,(coloring g).2),v))

def tableValue (a μ : Fin k → K) (b ν : Fin l → K) (flip : Bool) (xs : List (Bool × ℕ)) : K :=
  (xs.map (fun p=>sideFactor a μ b ν (Bool.xor p.1 flip) p.2)).prod

def evaluateConnected (a μ : Fin k → K) (b ν : Fin l → K) (g : MixedCode) : K :=
  if (coloring g).1 then tableValue a μ b ν false (table g)+tableValue a μ b ν true (table g) else 0

theorem fp_vertexData : FP (contextCode.prod BitEncoding.nat) rowCode vertexData := by
  have hp := fp_fst contextCode BitEncoding.nat
  have hg := hp.comp (fp_fst MixedCode.encoding assignmentCode)
  have hx := hp.comp (fp_snd MixedCode.encoding assignmentCode)
  have hv := fp_snd contextCode BitEncoding.nat
  have hc := (hv.pair hx).comp PlanarityParitySolver.fp_lookup
  have he := hg.comp (MixedCode.fp_edges.comp GraphDegreeMachines.fp_endpoints)
  have hd := (he.pair hv).comp GraphDegreeMachines.fp_count
  exact hc.pair hd

theorem fp_table : FP encoding rowCode.list table := by
  have hc := (fp_id encoding).pair (fp_coloring.comp (fp_snd BitEncoding.bool assignmentCode))
  have hv := MixedCode.fp_vertices.comp UnaryRangeMachines.fp_range
  exact (hc.pair hv).comp
    (ListContextMachines.fp_mapWithContext contextCode BitEncoding.nat rowCode vertexData fp_vertexData)

theorem fp_sideFactor (basis : Module.Basis (Fin dimension) ℚ K)
    (a μ : Fin k → K) (b ν : Fin l → K) :
    FP rowCode (numberFieldEncoding basis) (fun p=>sideFactor a μ b ν p.1 p.2) := by
  have hd := fp_snd BitEncoding.bool BitEncoding.unaryNat
  have hb := (fp_fst BitEncoding.bool BitEncoding.unaryNat).comp
    (fp_bool_unary BitEncoding.bool (fun b=>decide (b=true)))
  exact hb.ite (hd.comp (RankOneEvaluationMachine.fp_factor basis b ν))
    (hd.comp (RankOneEvaluationMachine.fp_factor basis a μ))

theorem fp_tableValue (basis : Module.Basis (Fin dimension) ℚ K)
    (a μ : Fin k → K) (b ν : Fin l → K) (flip : Bool) :
    FP rowCode.list (numberFieldEncoding basis) (tableValue a μ b ν flip) := by
  have hb := (fp_fst BitEncoding.bool BitEncoding.unaryNat).comp
    (fp_bool_unary BitEncoding.bool (fun b=>Bool.xor b flip))
  have hf := (hb.pair (fp_snd BitEncoding.bool BitEncoding.unaryNat)).comp (fp_sideFactor basis a μ b ν)
  exact (ListMapMachines.fp_map rowCode (numberFieldEncoding basis) _ hf).comp
    (MaterializedFieldListMachines.fp_product basis)

theorem fp_evaluateConnected (basis : Module.Basis (Fin dimension) ℚ K)
    (a μ : Fin k → K) (b ν : Fin l → K) :
    FP encoding (numberFieldEncoding basis) (evaluateConnected a μ b ν) := by
  have hb := (fp_coloring.comp (fp_fst BitEncoding.bool assignmentCode)).comp
    (fp_bool_unary BitEncoding.bool (fun b=>decide (b=true)))
  have hl := fp_table.comp (fp_tableValue basis a μ b ν false)
  have hr := fp_table.comp (fp_tableValue basis a μ b ν true)
  exact hb.ite ((hl.pair hr).comp (FixedFieldArithmetic.fp_addition basis)) (fp_const _ _ 0)

theorem prod_map_vertices (g : MixedCode) (f : ℕ → K) :
    (((List.range g.vertices).reverse).map f).prod=∏v : Fin g.vertices,f v.val := by
  rw [List.map_reverse,List.prod_reverse,←Fin.prod_univ_fun_getElem]
  apply Fintype.prod_equiv (finCongr (List.length_range (n:=g.vertices)))
  intro v
  simp [List.get_eq_getElem,List.getElem_range]

theorem tableValue_eq (g : MixedCode) (hg : g.Valid 1 0)
    (a μ : Fin k → K) (b ν : Fin l → K) (flip : Bool) :
    tableValue a μ b ν flip (table g) =
      sideProduct g hg a μ b ν (fun v=>Bool.xor (lookup (coloring g).2 v) flip) := by
  simp only [tableValue,table,List.map_map]
  rw [prod_map_vertices]
  apply Finset.prod_congr rfl
  intro v _
  change sideFactor a μ b ν _ (GraphDegreeMachines.degree g v.val)=_
  rw [GraphDegreeMachines.degree_toMultiGraph g hg]
  rfl

theorem evaluateConnected_correct (g : MixedCode) (hg : g.Valid 1 0)
    (hc : (support g).Connected) (hn : 0<g.vertices)
    (a μ : Fin k → K) (b ν : Fin l → K) :
    evaluateConnected a μ b ν g = g.evaluate hg (fun _:Fin 1=>matrix a b)
      (fun u:Fin 0=>u.elim0) (Sum.elim μ ν) := by
  rw [evaluate_homogeneous]
  unfold evaluateConnected
  by_cases h : (coloring g).1=true
  · rw [if_pos h,tableValue_eq g hg,tableValue_eq g hg]
    have he := partition_two_orientations g hg hc ⟨0,hn⟩ a μ b ν
      (lookup (coloring g).2) (coloring_sound g h)
    simpa only [Bool.xor_false,Bool.xor_true] using he.symm
  · rw [if_neg h]
    exact (partition_zero_of_rejected g hg a b (Sum.elim μ ν) h).symm

theorem evaluation_inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (a μ : Fin k → K) (b ν : Fin l → K) :
    (evaluationProblem basis (fun _:Fin 1=>matrix a b) (fun u:Fin 0=>u.elim0) (Sum.elim μ ν)).InFP := by
  apply GraphComponentCode.evaluation_inFP_of_connected basis _ _ _
  apply (restrictedEvaluation_inFP_iff basis _ _ _ (GraphComponentCode.connectedCodeValid 1 0)
    (fun _ hg=>hg.1.1)).mpr
  have hv : FP (encoding.restrict (GraphComponentCode.connectedCodeValid 1 0)) encoding Subtype.val :=
    fp_code_view _ _ _ (fun _=>rfl)
  exact (hv.comp (fp_evaluateConnected basis a μ b ν)).congr
    (fun g=>evaluateConnected_correct g.val g.property.1.1 g.property.2.1 g.property.2.2 a μ b ν)

end PlanarHom.BipartiteRankTwoTractability
