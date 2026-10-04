import PlanarHom.PottsSourceCoefficientQueries
import PlanarHom.RadialPottsClockwiseQuery
import PlanarHom.PottsCoefficientReduction

/-! NEW exact join of the executable inverse serializer with the drawn-source
radial theorem. Every geometric premise is displayed and concerns the same
inherited numeric rows; no alternative computed embedding is substituted. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PottsSourceCoefficientQueries
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open RadialPottsAssemblyGeometry PottsSourceInverseRows FinitePermutationCycles

structure CompatibleRows (g : MixedCode) (hg : g.Valid 1 0) (rows : Rows) where
  typed : RotationRows (g.toMultiGraph hg)
  realizes : PlanarityRowFaceCode.Realizes g hg rows typed
  incident : ∀v,∃a : Dart (Fin g.edges.length),((g.toMultiGraph hg).dartPair a).1=v
  euler : g.vertices+count (typed.rotation*reversePerm (Fin g.edges.length))=
    g.edges.length+2*(g.toMultiGraph hg).componentCount Finset.univ
  drawing : PolygonalDrawing (g.toMultiGraph hg)
  rays : Dart (Fin g.edges.length)→Plane
  germ : ∀a,StraightGerm (drawing.drawing.dartPath a)
    (drawing.drawing.point ((g.toMultiGraph hg).dartPair a).1) (rays a)
  nonvertical : ∀a,(rays a).1≠0
  clockwise : ∀v,(typed.row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b))

theorem serialized_query_planar (g : MixedCode) (hg : g.Valid 1 0) (rows : Rows)
    (h : CompatibleRows g hg rows) (k : ℕ) :
    (RadialPotts.Numeric.coefficientQuery (radialInput g rows k)).2.PlanarValid 1 0 := by
  rw [radialInput_eq g hg rows h.typed h.realizes]
  exact RadialPotts.Numeric.query_planar_clockwise h.drawing h.rays h.germ h.typed h.nonvertical h.clockwise

theorem serialized_coefficient_value (g : MixedCode) (hg : g.Valid 1 0) (rows : Rows)
    (h : CompatibleRows g hg rows) (q k : ℕ) (hq : 1<q) (hk : 0<k) :
    PottsCoefficientPrograms.coefficientValue q
      (RadialPotts.Numeric.coefficientQuery (radialInput g rows k))=
      PottsTwoStageInterpolation.radialValue (g.toMultiGraph hg) ((q:ℚ)-1) k := by
  rw [radialInput_eq g hg rows h.typed h.realizes]
  simp only [RadialPotts.Numeric.coefficientQuery]
  rw [PottsCoefficientPrograms.coefficientValue,dif_pos (RadialPotts.Numeric.query_valid h.typed.rotation)]
  exact RadialPotts.Numeric.query_coefficient_clockwise h.typed h.incident
    (by simpa only [Fintype.card_fin] using h.euler) q hq hk

/-- The coefficient oracle accepts the ordinary canonical graph query. Its
underlying promise also admits noncanonical successfully decoded raw words. -/
theorem coefficient_problem_valid (q : ℕ) (p : ℕ×MixedCode) (hp : p.2.PlanarValid 1 0) :
    (PottsCoefficientReduction.problem q).valid (queryCode.encode p) := by
  let rawGraph : BitEncoding.ValidWord MixedCode.encoding :=
    ⟨MixedCode.encoding.encode p.2,⟨p.2,MixedCode.encoding.decode_encode p.2⟩⟩
  refine ⟨(p.1,rawGraph),?_,?_⟩
  · rfl
  · have he : rawGraph.value=p.2 :=
      BitEncoding.ValidWord.value_eq (w:=rawGraph) (MixedCode.encoding.decode_encode p.2)
    simpa only [he] using hp

theorem coefficient_problem_value (q : ℕ) (p : ℕ×MixedCode) :
    (PottsCoefficientReduction.problem q).value (queryCode.encode p)=
      PottsCoefficientPrograms.fieldCode.encode (PottsCoefficientPrograms.coefficientValue q p) :=
  encodedFunction_encode PottsCoefficientPrograms.inputEncoding PottsCoefficientPrograms.fieldCode
    (PottsCoefficientPrograms.coefficientValue q) [] p

end PlanarHom.PottsSourceCoefficientQueries
