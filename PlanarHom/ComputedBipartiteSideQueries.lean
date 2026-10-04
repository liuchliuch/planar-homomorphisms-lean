import PlanarHom.BipartiteRankTwoColoring
import PlanarHom.HomogeneousSourceOrientationReduction

/-! NEW ordinary-to-prescribed query compiler. A real parity solver supplies
one bipartition, both global orientations are queried on connected inputs,
and a contradictory parity system emits no query. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ComputedBipartiteSideQueries
open Complexity Complexity.MixedCode PairProjectionMachines ArithmeticCircuitPrimitives
open PrescribedDomains HomogeneousSourceOrientation PlanarityParitySolver
open BipartiteRankTwoTractability

abbrev inputCode := MixedCode.encoding.prod BitEncoding.bool

def bit (g : MixedCode) (flip : Bool) (v : ℕ) : Bool := lookup (coloring g).2 v ^^ flip

def tag (g : MixedCode) (flip : Bool) (v : Fin g.vertices) : Fin 2 := if bit g flip v.val then 1 else 0

def query (flip : Bool) (g : MixedCode) : MixedCode :=
  ⟨g.vertices,g.edges,(List.range g.vertices).map (fun v=>(v,if bit g flip v then 1 else 0))⟩

def queries (g : MixedCode) : List MixedCode :=
  if (coloring g).1 then [query false g,query true g] else []

theorem tag_bit (g : MixedCode) (flip : Bool) (v : Fin g.vertices) :
    decide (tag g flip v=1)=bit g flip v.val := by
  cases h : bit g flip v.val <;> simp [tag,h]

theorem tag_flip (g : MixedCode) (v : Fin g.vertices) :
    decide (tag g true v=1)=!decide (tag g false v=1) := by
  rw [tag_bit,tag_bit]
  simp [bit]

theorem query_eq_withDomains (g : MixedCode) (hg : g.Valid 1 0) (flip : Bool) :
    query flip g=withDomains (unaryTypes:=0) g (tag g flip) := by
  have hu:=unaries_nil_of_valid_zero g hg
  have hd : domainOccurrences (unaryTypes:=0) g (tag g flip)=
      (List.range g.vertices).map (fun v=>(v,if bit g flip v then 1 else 0)) := by
    rw [←List.map_coe_finRange,List.map_map,←List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext v
    cases h : bit g flip v.val <;> simp [domainOccurrences,tag,h]
  cases g
  simp_all only [query,withDomains,List.nil_append]

theorem tag_proper (g : MixedCode) (hg : g.Valid 1 0) (hok : (coloring g).1=true) (flip : Bool) :
    ∀u v,(GraphComponentCode.support g).Adj u v →
      decide (tag g flip u=1)≠decide (tag g flip v=1) := by
  intro u v huv
  rw [tag_bit,tag_bit]
  have h:=proper_support g hg _ (coloring_sound g hok) u v huv
  cases flip
  · simpa only [bit,Bool.xor_false] using h
  · intro he
    apply h
    have hh:=congrArg Bool.not he
    simpa only [bit,Bool.xor_true,Bool.not_not] using hh

theorem query_typed (g : MixedCode) (hg : g.Valid 1 0) (hok : (coloring g).1=true) (flip : Bool) :
    Typed sidePolicies emptyPolicies g hg (tag g flip) := by
  constructor
  · intro e he
    have h:=coloring_sound g hok e he
    change tag g flip ⟨e.1,(hg.1 e he).1⟩≠tag g flip ⟨e.2.1,(hg.1 e he).2.1⟩
    intro ht
    have hb:=congrArg (fun d : Fin 2=>decide (d=1)) ht
    dsimp only at hb
    rw [tag_bit,tag_bit] at hb
    cases h1 : lookup (coloring g).2 e.1 <;> cases h2 : lookup (coloring g).2 e.2.1 <;>
      cases flip <;> simp_all [bit]
  · intro u hu
    have hbad := (hg.2 u hu).2
    omega

theorem query_planar (g : MixedCode) (hg : g.PlanarValid 1 0)
    (hok : (coloring g).1=true) (flip : Bool) : EncodedGraph sidePolicies emptyPolicies (query flip g) := by
  rw [query_eq_withDomains g hg.1 flip]
  exact encodedInput_encode_withDomains (query_typed g hg.1 hok flip) hg.2

theorem fp_bit : FP (inputCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>bit p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode BitEncoding.nat
  have hv:=fp_snd inputCode BitEncoding.nat
  have hg:=hc.comp (fp_fst MixedCode.encoding BitEncoding.bool)
  have hf:=hc.comp (fp_snd MixedCode.encoding BitEncoding.bool)
  have ha:=(hg.comp fp_coloring).comp (fp_snd BitEncoding.bool assignmentCode)
  have hb:=(hv.pair ha).comp PlanarityParitySolver.fp_lookup
  exact (hb.pair hf).comp (fp_bool_gate (fun p=>p.1 ^^ p.2))

theorem fp_query : FP inputCode MixedCode.encoding (fun p=>query p.2 p.1) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.bool
  have hn:=hg.comp MixedCode.fp_vertices
  have he:=hg.comp MixedCode.fp_edges
  have hl:=fp_bit.comp (fp_bool_unary BitEncoding.nat (fun b=>if b then 1 else 0))
  have hv:=fp_snd inputCode BitEncoding.nat
  have hentry:=hv.pair hl
  have hr:=hn.comp UnaryArithmeticMachines.fp_range
  have htags:=((fp_id inputCode).pair hr).comp
    (ListContextMachines.fp_mapWithContext inputCode BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat) _ hentry)
  exact (hn.pair (he.pair htags)).transportOutput (fun _=>rfl)

theorem fp_queries : FP MixedCode.encoding MixedCode.encoding.list queries := by
  have hfalse:=((fp_id MixedCode.encoding).pair (fp_const MixedCode.encoding BitEncoding.bool false)).comp fp_query
  have htrue:=((fp_id MixedCode.encoding).pair (fp_const MixedCode.encoding BitEncoding.bool true)).comp fp_query
  have hn:=fp_const MixedCode.encoding MixedCode.encoding.list []
  have ht:=(htrue.pair hn).comp (ListMutationMachines.fp_cons MixedCode.encoding)
  have hboth:=(hfalse.pair ht).comp (ListMutationMachines.fp_cons MixedCode.encoding)
  have hf:=fp_coloring.comp (fp_fst BitEncoding.bool assignmentCode)
  have hf' : FP MixedCode.encoding BitEncoding.bool (fun g=>decide ((coloring g).1=true)) :=
    hf.congr (fun _=>by simp)
  exact (hf'.ite hboth hn).congr (fun _=>rfl)

end PlanarHom.ComputedBipartiteSideQueries
