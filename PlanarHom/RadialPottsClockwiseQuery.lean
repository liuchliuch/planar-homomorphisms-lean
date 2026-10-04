import PlanarHom.RadialPottsNumericQuery
import PlanarHom.PottsOccurrenceReversal
import PlanarHom.PlanarityLRDualReachability
import PlanarHom.RadialPottsAssemblyGeometricRows

/-! One exact source convention for geometry and arithmetic. The ordinary
numeric query is planar from the actual clockwise source canvas, and its value
uses the same rotation. Reversing source occurrence directions is explicit and
preserves the symmetric Potts/Tutte value. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPotts.Numeric
open Complexity Assembly MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open PottsCentered PottsTwoStageInterpolation FinitePermutationCycles RadialPottsAssemblyGeometry
variable {V : Type} [Fintype V] {m k : ℕ} [DecidableEq (Dart (Fin m))]
variable {G : MultiGraph V (Fin m)}

 theorem clockwise_row_cycles (rows : RotationRows G) (a b : Dart (Fin m)) :
    rows.rotation.SameCycle a b ↔ (G.dartPair a).1=(G.dartPair b).1 := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hh := rows.rotation_iterate_host a n
    rw [Equiv.Perm.iterate_eq_pow,hn] at hh
    exact hh.symm
  · intro h
    obtain ⟨n,hn⟩ := rows.exists_rotation_iterate_of_sameHost a b h
    exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn⟩

 theorem query_coefficient_clockwise (rows : RotationRows G)
    (hinc : ∀v,∃a : Dart (Fin m),(G.dartPair a).1=v)
    (heuler : Fintype.card V+count (rows.rotation*reversePerm (Fin m))=m+2*G.componentCount Finset.univ)
    (q : ℕ) (hq : 1<q) (hk : 0<k) :
    (polynomial ((query (input rows.rotation k)).toMultiGraph (query_valid rows.rotation)) q).coeff
      (coefficientDegree (input rows.rotation k))=radialValue G ((q:ℚ)-1) k := by
  have hc : ∀a b,rows.rotation.SameCycle a b ↔ (reversedGraph G).dartVertex a=(reversedGraph G).dartVertex b := by
    intro a b
    simpa only [reversed_dartVertex] using clockwise_row_cycles rows a b
  have hs : Function.Surjective (reversedGraph G).dartVertex := by
    intro v
    obtain ⟨a,ha⟩ := hinc v
    exact ⟨a,by simpa only [reversed_dartVertex] using ha⟩
  have hf : Fintype.card V+count (subsetBoundary rows.rotation Finset.univ)=
      m+2*(reversedGraph G).componentCount Finset.univ := by
    rw [full_boundary_count_face,reversed_componentCount]
    exact heuler
  simpa only [reversed_radialValue] using query_coefficient V (reversedGraph G) rows.rotation hc hs hf q hq hk

/-- A literal ordinary planar query from actual drawn source rows. No geometric
realization is inferred from the Euler identity. -/
theorem query_planar_clockwise (d : PolygonalDrawing G) (rays : Dart (Fin m)→Plane)
    (hgerm : ∀a,StraightGerm (d.drawing.dartPath a) (d.drawing.point (G.dartPair a).1) (rays a))
    (rows : RotationRows G) (hne : ∀a,(rays a).1≠0)
    (hrows : ∀v,(rows.row v).Pairwise (fun a b=>ClockwiseRayOrder (rays a) (rays b))) :
    (query (input rows.rotation k)).PlanarValid 1 0 :=
  query_planar rows.rotation (planar_of_clockwiseRows d rays hgerm rows hne hrows k)
end PlanarHom.RadialPotts.Numeric
