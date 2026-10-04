import PlanarHom.PottsParallelRowCorrespondence
import PlanarHom.PolygonalIncidenceTransport
import PlanarHom.ParallelSourceClockwiseGeometry
import PlanarHom.ParallelSourceEuler
import PlanarHom.ColoringIncidenceComponents

/-! NEW complete transport of the actual inherited parallel certificate into
the literal emitted graph/row code. Incidence, geometry, row realization and
full Euler are all transported by the same explicit occurrence equivalence. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.PottsSourceCoefficientQueries
open Complexity MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
open PottsSourceInverseRows FinitePermutationCycles

theorem parallel_compatible (g : MixedCode) (hg : g.Valid 1 0) (rows : Rows)
    (h : CompatibleRows g hg rows) (t : ℕ) (ht : 0<t) :
    Nonempty (CompatibleRows (g.parallelLabel 0 t) (UniformParallelCode.validParallel g hg t)
      (parallelRows t rows)) := by
  let i:=UniformParallelCode.incidence g hg t
  let R:=RotationRows.redecidable (ParallelSource.rows h.typed t)
  have hi := ParallelSource.parallel_incident t ht h.incident
  have he := ParallelSource.parallel_euler h.typed t ht
    (by simpa only [Fintype.card_fin] using h.euler)
  have hR : Fintype.card (Fin g.vertices)+count (R.rotation*reversePerm (Fin g.edges.length×Fin t))=
      Fintype.card (Fin g.edges.length×Fin t)+2*((g.toMultiGraph hg).thicken t).componentCount Finset.univ := by
    simpa only [R,RotationRows.redecidable_rotation] using he
  obtain ⟨p,rays,hgerm,hne,horder⟩ := ParallelSource.exists_clockwise_parallel
    h.drawing h.rays h.germ h.typed h.nonvertical h.clockwise t
  obtain ⟨p',rays',hgerm',hne',horder'⟩ := PolygonalIncidenceTransport.clockwise
    p i R rays hgerm hne horder
  refine ⟨{
    typed:=i.dartRelabel.rows R
    realizes:=PottsParallelRowCorrespondence.realizes g hg rows h.typed h.realizes t
    incident:=?_
    euler:=?_
    drawing:=p'
    rays:=rays'
    germ:=hgerm'
    nonvertical:=hne'
    clockwise:=horder' }⟩
  · intro v
    obtain ⟨a,ha⟩ := hi (i.vertex.symm v)
    refine ⟨i.dartRelabel.dart a,?_⟩
    rw [i.dartRelabel.host,ha]
    exact i.vertex.apply_symm_apply v
  · have htransport : Fintype.card (Fin g.vertices)+count (i.dartRelabel.rows R).facePerm=
        Fintype.card (Fin (g.parallelLabel 0 t).edges.length)+
          2*((g.parallelLabel 0 t).toMultiGraph (UniformParallelCode.validParallel g hg t)).componentCount Finset.univ := by
      rw [i.dartRelabel.face_count,←Fintype.card_congr i.edge,i.componentCount_eq]
      exact hR
    simpa only [Fintype.card_fin,RotationRows.facePerm,MixedCode.parallelLabel_vertices] using htransport

end PlanarHom.PottsSourceCoefficientQueries
